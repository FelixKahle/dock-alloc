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
    pub trials: usize,
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
/// - `trials`: grows with congestion ρ and movable_count; clamped to [16, 256].
/// - `horizon_end`: latest completion time (typed).
impl<T, C, Q> From<&Problem<T, C>> for EjectionChain2Operator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(p: &Problem<T, C>) -> Self {
        let s = p.stats();
        let rho = s.rho();
        let mov = p.movable_count();

        let base = if rho < 0.6 {
            24
        } else if rho < 0.9 {
            32
        } else if rho < 1.2 {
            48
        } else {
            64
        };
        let size = 8 + mov / 8;
        let trials = (base + size).clamp(16, 256);

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

            // Pick A
            let Some(a) = tx.with_explorer(|ex| ex.iter_movable_assignments().next()) else {
                return b.build();
            };
            let req_a = a.branded_request();
            let old_a = a.assignment().cost();

            // Windows for A (typed)
            let gw = global_time_window(&tx, self.horizon_end);
            let (t_w, s_w) = req_windows(&req_a, gw, req_a.feasible_space_window());

            // Try a better slot for A among first `trials`
            let best_a = best_improving_slot(&tx, &req_a, t_w, s_w, old_a, self.trials);
            let Some((_da, slot_a)) = best_a else {
                return b.build();
            };

            // Move A
            if tx.propose_unassign(&a).is_err() {
                return b.build();
            }
            let Ok(_a_new) = tx.propose_assign(&req_a, slot_a) else {
                return b.build();
            };

            // Pick B (any other movable) and relocate greedily
            if let Some(bm) = tx.with_explorer(|ex| {
                ex.iter_movable_assignments()
                    .find(|m| m.branded_request().id() != req_a.id())
            }) {
                let req_b = bm.branded_request();
                let old_b = bm.assignment().cost();
                let (t2, s2) = req_windows(&req_b, gw, req_b.feasible_space_window());
                if let Some((_db, slot_b)) =
                    best_improving_slot(&tx, &req_b, t2, s2, old_b, self.trials)
                    && tx.propose_unassign(&bm).is_ok()
                {
                    let _ = tx.propose_assign(&req_b, slot_b);
                }
            }

            // Commit only if fully assigned
            if tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}
