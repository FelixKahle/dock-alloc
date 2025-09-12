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
// WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

use crate::{
    berth::{overlay::BrandedFreeSlot, quay::QuayRead},
    framework::planning::{Plan, PlanningContext},
    meta::{
        operator::Operator,
        oplib::util::{global_time_window, req_windows},
    },
};
use dock_alloc_core::{SolverVariable, time::TimePoint};
use dock_alloc_model::model::Problem;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

pub struct MoveToLatestFeasibleOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub scan_limit: usize,
    pub horizon_end: TimePoint<T>,
    _phantom: core::marker::PhantomData<(C, Q)>,
}

impl<T, C, Q> Default for MoveToLatestFeasibleOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            scan_limit: 64,
            horizon_end: TimePoint::new(T::from(10_000).unwrap_or(T::zero())),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> From<&Problem<T, C>> for MoveToLatestFeasibleOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(problem: &Problem<T, C>) -> Self {
        let s = problem.stats();
        let mov = s.movable_count().max(1);
        let rho = s.rho();

        // Base ~ O(log n) with a gentle size bump; congestion increases effort.
        let base = (mov.ilog2() as usize) + 8;
        let size_bump = (mov / 64).min(8);
        let cong_mult = 1.0 + 0.6 * rho; // ρ in [0,2] ⇒ multiplier in ~[1.0, 2.2]
        let scan = (((base + size_bump) as f64) * cong_mult).round() as usize;

        // Size-aware ceiling; let big instances explore more, still bounded.
        let ceiling = (24 + (mov.ilog2() as usize) * 16).clamp(64, 256);

        Self {
            scan_limit: scan.clamp(16, ceiling),
            horizon_end: s.latest_completion_time(), // typed TimePoint<T>
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for MoveToLatestFeasibleOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;
    fn name(&self) -> &'static str {
        "MoveToLatestFeasible"
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
            let Some(cur) = tx.with_explorer(|ex| {
                ex.iter_movable_assignments()
                    .max_by_key(|m| m.start_time().value())
            }) else {
                return b.build();
            };
            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();
            let gw = global_time_window(&tx, self.horizon_end);
            let (t_w, s_w) = req_windows(&req, gw, req.feasible_space_window());
            // collect up to scan_limit then pick the last
            let mut last: Option<BrandedFreeSlot<'_, T>> = None;
            let mut count = 0usize;
            tx.with_explorer(|ex| {
                for s in ex.iter_slots_for_request_within(&req, t_w, s_w) {
                    last = Some(s);
                    count += 1;
                    if count >= self.scan_limit {
                        break;
                    }
                }
            });
            let Some(slot) = last else {
                return b.build();
            };
            let hyp = dock_alloc_model::model::AssignmentRef::new(
                req.request(),
                slot.slot().space().start(),
                slot.slot().start_time(),
            );
            if (hyp.cost() - old_cost).value() < C::zero() {
                if tx.propose_unassign(&cur).is_err() {
                    return b.build();
                }
                if tx.propose_assign(&req, slot).is_err() {
                    return b.build();
                }
                if tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                    tx.commit();
                }
            }
            b.build()
        })
    }
}
