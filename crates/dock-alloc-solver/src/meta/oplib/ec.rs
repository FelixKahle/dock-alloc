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
    berth::quay::QuayRead,
    framework::planning::{Plan, PlanningContext},
    meta::{
        operator::Operator,
        oplib::util::{best_improving_slot, global_time_window, req_windows},
    },
};
use dock_alloc_core::{SolverVariable, time::TimePoint};
use dock_alloc_model::model::Problem;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

pub struct EjectionChain2Operator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    /// Number of candidate slots to scan when searching improvements.
    pub trials: usize,
    /// Soft upper bound for time window (typed).
    pub horizon_end: TimePoint<T>,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for EjectionChain2Operator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            trials: 32,
            horizon_end: TimePoint::new(T::zero()),
            _phantom: core::marker::PhantomData,
        }
    }
}

/// Heuristic from instance stats:
/// - trials grows with congestion ρ and size; clamped to [16, 256].
/// - horizon_end uses latest_completion_time (typed).
impl<T, C, Q> From<&Problem<T, C>> for EjectionChain2Operator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(p: &Problem<T, C>) -> Self {
        let s = p.stats();
        let rho = s.rho();
        let mov = p.movable_count().max(1);

        // Size + congestion aware budget.
        let base = (mov.ilog2() as usize) + 24;
        let size_bump = (mov / 32).min(24);
        let cong_mult = 1.0 + 0.5 * rho; // ρ∈[0,2] ⇒ [1.0, 2.0]
        let trials = (((base + size_bump) as f64) * cong_mult).round() as usize;
        let trials = trials.clamp(16, 256);

        Self {
            trials,
            horizon_end: s.latest_completion_time(),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for EjectionChain2Operator<T, C, Q>
where
    T: SolverVariable + Send + Sync,
    C: SolverVariable + TryFrom<T> + TryFrom<usize> + Send + Sync,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "EjectionChain2"
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

            // Pick A = movable with highest current assignment cost (bigger potential gain).
            let Some(a) = tx.with_explorer(|ex| {
                ex.iter_movable_assignments()
                    .max_by_key(|m| m.assignment().cost())
            }) else {
                return b.build();
            };

            let req_a = a.branded_request();
            let old_a = a.assignment().cost();

            // Shared dynamic horizon + request windows (typed).
            let gw = global_time_window(&tx, self.horizon_end);
            let (t_w_a, s_w_a) = req_windows(&req_a, gw, req_a.feasible_space_window());

            // Best improving slot for A among first `trials`.
            let Some((_da, slot_a)) =
                best_improving_slot(&tx, &req_a, t_w_a, s_w_a, old_a, self.trials)
            else {
                return b.build();
            };

            // Move A (mutable ops after explorer borrows end).
            if tx.propose_unassign(&a).is_err() {
                return b.build();
            }
            if tx.propose_assign(&req_a, slot_a).is_err() {
                return b.build();
            }

            // Pick B = highest-cost movable (≠ A) and try a greedy relocate.
            if let Some(bm) = tx.with_explorer(|ex| {
                ex.iter_movable_assignments()
                    .filter(|m| m.branded_request().id() != req_a.id())
                    .max_by_key(|m| m.assignment().cost())
            }) {
                let req_b = bm.branded_request();
                let old_b = bm.assignment().cost();

                let (t_w_b, s_w_b) = req_windows(&req_b, gw, req_b.feasible_space_window());
                if let Some((_db, slot_b)) =
                    best_improving_slot(&tx, &req_b, t_w_b, s_w_b, old_b, self.trials)
                    && tx.propose_unassign(&bm).is_ok() {
                        let _ = tx.propose_assign(&req_b, slot_b);
                    }
            }

            // Commit only if everything remains fully assigned.
            if tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}
