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

pub struct MoveToEarliestFeasibleOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub attempts: usize,
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
            horizon_end: TimePoint::new(T::from(10_000).unwrap_or(T::zero())),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> From<&Problem<T, C>> for MoveToEarliestFeasibleOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(problem: &Problem<T, C>) -> Self {
        let m = problem.movable_count().max(1);
        let rho = problem.congestion_rho();
        let base = (m.max(1).ilog2() as usize) + 4;
        let scaled = (base as f64 * (1.0 + 0.5 * rho)).round() as usize;
        Self {
            attempts: scaled.clamp(6, 32),
            ..Self::default()
        }
    }
}

impl<T, C, Q> Operator for MoveToEarliestFeasibleOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
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
            let Some(cur) = tx.with_explorer(|ex| ex.iter_movable_assignments().next()) else {
                return b.build();
            };
            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();

            let gw = global_time_window(&tx, self.horizon_end);
            let (t_w, s_w) = req_windows(&req, gw, req.feasible_space_window());

            // pick the first feasible slot directly (no dummy loop)
            let candidate: Option<BrandedFreeSlot<'_, T>> =
                tx.with_explorer(|ex| ex.iter_slots_for_request_within(&req, t_w, s_w).next());

            let Some(slot) = candidate else {
                return b.build();
            };

            // improvement guard (domain-typed)
            let hyp = dock_alloc_model::model::AssignmentRef::new(
                req.request(),
                slot.slot().space().start(),
                slot.slot().start_time(),
            );
            if hyp.cost() >= old_cost {
                return b.build();
            }

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
