// Copyright (c) 2025 Felix Kahle.
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to
// the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
// LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
// THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

use crate::{
    berth::quay::QuayRead,
    framework::planning::{Plan, PlanningContext},
    meta::operator::Operator,
    meta::oplib::util::{best_improving_slot, global_time_window, req_windows},
};
use dock_alloc_core::{SolverVariable, time::TimePoint};
use dock_alloc_model::model::Problem;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

pub struct GreedyRelocateBestOfKOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub k: usize,
    pub horizon_end: TimePoint<T>,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for GreedyRelocateBestOfKOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            k: 96,
            horizon_end: TimePoint::new(T::zero()),
            _phantom: core::marker::PhantomData,
        }
    }
}

/// Choose `k` based on congestion ρ and instance size; set `horizon_end` to latest completion.
impl<T, C, Q> From<&Problem<T, C>> for GreedyRelocateBestOfKOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(p: &Problem<T, C>) -> Self {
        let s = p.stats();
        let rho = s.rho();
        let mov = p.movable_count();

        // Base k by congestion; add a small size-aware bump; clamp to a sane range.
        let base = if rho < 0.6 {
            48
        } else if rho < 0.9 {
            64
        } else if rho < 1.2 {
            96
        } else {
            128
        };
        let size = 16 + mov / 6;
        let k = (base + size).clamp(16, 512);

        Self {
            k,
            horizon_end: s.latest_completion_time(),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for GreedyRelocateBestOfKOperator<T, C, Q>
where
    T: SolverVariable + Send + Sync,
    C: SolverVariable + TryFrom<T> + TryFrom<usize> + Send + Sync,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "GreedyRelocateBestOfK"
    }

    #[instrument(level = "info", skip_all)]
    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        _: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let mut tx = b.begin();

            let Some(cur) = tx.with_explorer(|ex| ex.iter_movable_assignments().next()) else {
                return b.build();
            };

            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();

            // Typed global time window and request-constrained windows.
            let gw = global_time_window(&tx, self.horizon_end);
            let (t_w, s_w) = req_windows(&req, gw, req.feasible_space_window());

            // Best improving among first k candidates (domain-level cost comparisons).
            let best = best_improving_slot(&tx, &req, t_w, s_w, old_cost, self.k);
            let Some((_d, slot)) = best else {
                return b.build();
            };

            if tx.propose_unassign(&cur).is_err() {
                return b.build();
            }
            if tx.propose_assign(&req, slot).is_err() {
                return b.build();
            }

            if tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}
