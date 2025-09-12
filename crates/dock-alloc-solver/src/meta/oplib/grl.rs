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

use dock_alloc_core::{SolverVariable, time::TimePoint};
use dock_alloc_model::model::Problem;
use rand::Rng;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

use crate::{
    berth::quay::QuayRead,
    framework::planning::{Plan, PlanningContext},
    meta::{
        operator::Operator,
        oplib::util::{global_time_window, req_windows},
    },
};

pub struct GlobalRelocateRandomOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub trials: usize,
    pub horizon_end: TimePoint<T>,
    _phantom: core::marker::PhantomData<(C, Q)>,
}

impl<T, C, Q> Default for GlobalRelocateRandomOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            trials: 64,
            horizon_end: TimePoint::new(T::zero()),
            _phantom: core::marker::PhantomData,
        }
    }
}

/// Heuristic from `Problem`:
/// - `trials`: scale with congestion ρ and instance size (movable_count), clamped to [16, 256]
/// - `horizon_end`: use the instance's `latest_completion_time` (typed `TimePoint<T>`)
impl<T, C, Q> From<&Problem<T, C>> for GlobalRelocateRandomOperator<T, C, Q>
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
            32
        } else if rho < 0.9 {
            48
        } else if rho < 1.2 {
            64
        } else {
            96
        };
        // small size-aware bump
        let size = 8 + mov / 6;
        let trials = (base + size).clamp(16, 256);

        Self {
            trials,
            horizon_end: s.latest_completion_time(),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for GlobalRelocateRandomOperator<T, C, Q>
where
    T: SolverVariable + Send + Sync,
    C: SolverVariable + TryFrom<T> + TryFrom<usize> + Send + Sync,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "GlobalRelocateRandom"
    }

    #[instrument(level = "info", skip_all)]
    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let mut tx = b.begin();

            // Pick a random movable assignment
            let picked = tx.with_explorer(|ex| {
                let v: Vec<_> = ex.iter_movable_assignments().collect();
                if v.is_empty() {
                    None
                } else {
                    let i = rng.random_range(0..v.len());
                    Some(v[i].clone())
                }
            });
            let Some(cur) = picked else {
                return b.build();
            };

            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();

            // Global time window up to configured horizon_end; clamp spatially by the request's window
            let gw = global_time_window(&tx, self.horizon_end);
            let (t_w, s_w) = req_windows(&req, gw, req.feasible_space_window());

            // Scan up to `trials` candidate slots (in iterator order; upstream can randomize order)
            let mut choice = None;
            tx.with_explorer(|ex| {
                let mut cnt = 0usize;
                for slot in ex.iter_slots_for_request_within(&req, t_w, s_w) {
                    choice = Some(slot);
                    cnt += 1;
                    if cnt >= self.trials {
                        break;
                    }
                }
            });
            let Some(slot) = choice else {
                return b.build();
            };

            // Evaluate cost delta using domain types only
            // Prefer direct comparison on Cost<C> (no `.value()`).
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
