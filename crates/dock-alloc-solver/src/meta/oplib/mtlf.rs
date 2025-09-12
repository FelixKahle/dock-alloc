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
            horizon_end: TimePoint::new(T::zero()),
            _phantom: core::marker::PhantomData,
        }
    }
}

/// Adaptive tuning:
/// - `scan_limit`: ~O(log n) with size bump; scaled by congestion ρ; capped by a size-aware ceiling
/// - `horizon_end`: latest completion time (typed)
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

        // Base ~ log2(n) + small bump; congestion increases effort.
        let base = (mov.ilog2() as usize) + 8;
        let size_bump = (mov / 64).min(12);
        let cong_mult = 1.0 + 0.6 * rho; // ρ∈[0,2] → ~[1.0, 2.2]
        let raw_scan = (((base + size_bump) as f64) * cong_mult).round() as usize;

        // Ceiling grows mildly with instance size; clamp overall.
        let ceiling = (48 + (mov.ilog2() as usize) * 16).clamp(64, 384);

        Self {
            scan_limit: raw_scan.clamp(16, ceiling),
            horizon_end: s.latest_completion_time(),
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

            // pick the currently latest-starting movable
            let Some(cur) = tx.with_explorer(|ex| {
                ex.iter_movable_assignments()
                    .max_by(|a, b| a.start_time().cmp(&b.start_time()))
            }) else {
                return b.build();
            };

            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();

            // global window (typed) + request windows
            let gw = global_time_window(&tx, self.horizon_end);
            let (t_w, s_w) = req_windows(&req, gw, req.feasible_space_window());

            // scan up to `scan_limit`, choose the *latest* improving slot;
            // tie-break on lower resulting cost.
            let mut candidate: Option<BrandedFreeSlot<'_, T>> = None;
            let mut cand_t: Option<TimePoint<T>> = None;
            let mut cand_cost: Option<dock_alloc_core::cost::Cost<C>> = None;

            tx.with_explorer(|ex| {
                let mut seen = 0usize;
                for s in ex.iter_slots_for_request_within(&req, t_w, s_w) {
                    // evaluate cost in domain units
                    let t = s.slot().start_time();
                    let sp = s.slot().space().start();
                    let hyp = dock_alloc_model::model::AssignmentRef::new(req.request(), sp, t);
                    let c = hyp.cost();

                    if c < old_cost {
                        // prefer later start time; if equal time, prefer cheaper
                        let take = match (cand_t, cand_cost) {
                            (None, _) => true,
                            (Some(bt), Some(bc)) => (t > bt) || (t == bt && c < bc),
                            (Some(bt), None) => t > bt,
                        };
                        if take {
                            candidate = Some(s);
                            cand_t = Some(t);
                            cand_cost = Some(c);
                        }
                    }

                    seen += 1;
                    if seen >= self.scan_limit {
                        break;
                    }
                }
            });

            let Some(slot) = candidate else {
                return b.build();
            };

            // apply if it truly improves
            if tx.propose_unassign(&cur).is_err() {
                return b.build();
            }
            if tx.propose_assign(&req, slot).is_err() {
                return b.build();
            }

            // commit only if fully assigned
            if tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}
