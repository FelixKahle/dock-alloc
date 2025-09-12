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
use dock_alloc_core::{
    SolverVariable,
    time::{TimeInterval, TimePoint},
};
use dock_alloc_model::model::Problem;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

pub struct MoveToEarliestFeasibleOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    /// Max number of candidate slots to inspect when searching earlier placements.
    pub attempts: usize,
    /// Soft upper bound for time windows.
    pub horizon_end: TimePoint<T>,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for MoveToEarliestFeasibleOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            attempts: 64,
            horizon_end: TimePoint::new(T::zero()),
            _phantom: core::marker::PhantomData,
        }
    }
}

/// Adaptive configuration:
/// - `attempts` grows with congestion ρ and size (movables), clamped to [12, 160].
/// - `horizon_end` takes the instance's latest completion time (typed).
impl<T, C, Q> From<&Problem<T, C>> for MoveToEarliestFeasibleOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(problem: &Problem<T, C>) -> Self {
        let s = problem.stats();
        let rho = s.rho();
        let m = s.movable_count().max(1);

        // Base ~ O(log m) + small size bump; multiply by congestion.
        let base = (m.ilog2() as usize) + 6;
        let size_bump = (m / 40).min(24);
        let cong_mul = 1.0 + 0.6 * rho; // ρ∈[0,2] -> [1.0, 2.2]
        let attempts = (((base + size_bump) as f64) * cong_mul).round() as usize;

        Self {
            attempts: attempts.clamp(12, 160),
            horizon_end: s.latest_completion_time(),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for MoveToEarliestFeasibleOperator<T, C, Q>
where
    T: SolverVariable + Send + Sync,
    C: SolverVariable + TryFrom<T> + TryFrom<usize> + Send + Sync,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "MoveToEarliestFeasible"
    }

    #[instrument(level = "info", skip_all)]
    fn propose<'p, 'al, 'bo>(
        &self,
        _it: usize,
        _rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let mut tx = b.begin();

            // Pick the movable with the largest waiting COST (time-weighted), not just time.
            let Some(cur) = tx.with_explorer(|ex| {
                ex.iter_movable_assignments()
                    .max_by_key(|m| m.assignment().waiting_cost())
            }) else {
                return b.build();
            };

            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();
            let cur_t = cur.start_time();

            // Global horizon and request windows (typed).
            let gw = global_time_window(&tx, self.horizon_end);
            let (mut t_w, s_w) = req_windows(&req, gw, req.feasible_space_window());

            // Restrict to strictly-earlier times than current start.
            // If that empties the window, nothing to do.
            if cur_t > t_w.start() {
                t_w = TimeInterval::new(t_w.start(), core::cmp::min(t_w.end(), cur_t));
                if t_w.start() >= t_w.end() {
                    return b.build();
                }
            } else {
                // Already at/near earliest; no earlier region to search.
                return b.build();
            }

            // Scan up to `attempts` slots in time order; pick the earliest IMPROVING one.
            let candidate: Option<BrandedFreeSlot<'_, T>> = tx.with_explorer(|ex| {
                ex.iter_slots_for_request_within(&req, t_w, s_w)
                    .take(self.attempts)
                    .find(|slot| {
                        let hyp = dock_alloc_model::model::AssignmentRef::new(
                            req.request(),
                            slot.slot().space().start(),
                            slot.slot().start_time(),
                        );
                        hyp.cost() < old_cost
                    })
            });

            let Some(slot) = candidate else {
                return b.build();
            };

            // Apply move (mutations happen after explorer borrow ends).
            if tx.propose_unassign(&cur).is_err() {
                return b.build();
            }
            if tx.propose_assign(&req, slot).is_err() {
                return b.build();
            }

            // Commit only if fully assigned after the move.
            if tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}
