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

/// Adaptive K: size- and congestion-aware; horizon from stats.
impl<T, C, Q> From<&Problem<T, C>> for GreedyRelocateBestOfKOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(p: &Problem<T, C>) -> Self {
        let s = p.stats();
        let rho = s.rho();
        let mov = s.movable_count().max(1);

        // Base ~ O(log n) with a small size bump; congestion multiplies effort.
        let base = (mov.ilog2() as usize) + 8;
        let size_bump = (mov / 32).min(32);
        let cong_mult = 1.0 + 0.5 * rho; // ρ ∈ [0,2] → [1.0, 2.0]
        let k = (((base + size_bump) as f64) * cong_mult).round() as usize;

        // Size-aware ceiling.
        let ceiling = (48 + (mov.ilog2() as usize) * 32).clamp(64, 512);

        Self {
            k: k.clamp(24, ceiling),
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

            // Pick the movable with highest current assignment cost (greater potential gain).
            let Some(cur) = tx.with_explorer(|ex| {
                ex.iter_movable_assignments()
                    .max_by_key(|m| m.assignment().cost())
            }) else {
                return b.build();
            };

            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();

            // Shared dynamic horizon + request windows (typed).
            let gw = global_time_window(&tx, self.horizon_end);
            let (t_w, s_w) = req_windows(&req, gw, req.feasible_space_window());

            // Best improving among first k candidates (domain-typed cost).
            let Some((_delta, slot)) = best_improving_slot(&tx, &req, t_w, s_w, old_cost, self.k)
            else {
                return b.build();
            };

            // Apply move (no borrow conflicts: mutations after explorer borrows end).
            if tx.propose_unassign(&cur).is_err() {
                return b.build();
            }
            if tx.propose_assign(&req, slot).is_err() {
                return b.build();
            }

            // Commit only if everything remains fully assigned.
            if tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}
