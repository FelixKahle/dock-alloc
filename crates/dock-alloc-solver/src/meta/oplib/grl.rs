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
/// - `trials`: scale with congestion ρ and size; clamp to [16, 256]
/// - `horizon_end`: latest completion time (typed)
impl<T, C, Q> From<&Problem<T, C>> for GlobalRelocateRandomOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(p: &Problem<T, C>) -> Self {
        let s = p.stats();
        let rho = s.rho();
        let mov = s.movable_count().max(1);

        let base = (mov.ilog2() as usize) + 16;
        let size_bump = (mov / 24).min(32);
        let cong_mul = 1.0 + 0.5 * rho; // ρ ∈ [0,2] → [1.0, 2.0]
        let trials = (((base + size_bump) as f64) * cong_mul).round() as usize;

        Self {
            trials: trials.clamp(16, 256),
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

            // --- pick a random movable WITHOUT allocating a Vec
            // pass 1: count
            let count_opt = tx.with_explorer(|ex| {
                let mut n = 0usize;
                for _ in ex.iter_movable_assignments() {
                    n += 1;
                }
                if n == 0 { None } else { Some(n) }
            });
            let Some(n) = count_opt else {
                return b.build();
            };

            // pass 2: select nth
            let idx = rng.random_range(0..n);
            let picked =
                tx.with_explorer(|ex| ex.iter_movable_assignments().nth(idx));
            let Some(cur) = picked else {
                return b.build();
            };

            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();

            // typed global time window (dynamic) + request window
            let gw = global_time_window(&tx, self.horizon_end);
            let (t_w, s_w) = req_windows(&req, gw, req.feasible_space_window());

            // --- reservoir sample among IMPROVING slots within first `trials`
            let mut chosen = None;
            let mut k_improving = 0usize;

            tx.with_explorer(|ex| {
                for (seen, slot) in ex
                    .iter_slots_for_request_within(&req, t_w, s_w)
                    .take(self.trials)
                    .enumerate()
                {
                    // quick exact delta (domain-typed)
                    let hyp = dock_alloc_model::model::AssignmentRef::new(
                        req.request(),
                        slot.slot().space().start(),
                        slot.slot().start_time(),
                    );
                    if hyp.cost() < old_cost {
                        k_improving += 1;
                        // replace with probability 1/k
                        if rng.random_range(0..k_improving) == 0 {
                            chosen = Some(slot);
                        }
                    }

                    // early escape if we've exhausted trials (enumerate already limits)
                    let _ = seen; // silence unused warning
                }
            });

            let Some(slot) = chosen else {
                return b.build();
            };

            // --- apply move
            if tx.propose_unassign(&cur).is_err() {
                return b.build();
            }
            if tx.propose_assign(&req, slot).is_err() {
                return b.build();
            }

            // commit only on full assignment
            if tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}
