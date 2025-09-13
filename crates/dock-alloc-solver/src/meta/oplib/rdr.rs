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

use dock_alloc_core::{
    SolverVariable,
    time::{TimeInterval, TimePoint},
};
use dock_alloc_model::model::Problem;
use rand::Rng;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

use crate::{
    berth::quay::QuayRead,
    framework::planning::{Plan, PlanningContext},
    meta::operator::Operator,
};

pub struct RandomDestroyRepairOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub remove_frac: f64,
    pub min_remove: usize,
    pub max_remove: Option<usize>,
    /// soft upper bound for search
    pub horizon_end: TimePoint<T>,
    /// local radius (time units) for peeking alternatives around current start
    pub local_time_radius: T,
    /// cap on scanned alternatives per request
    pub max_trials_per_request: usize,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for RandomDestroyRepairOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            remove_frac: 0.10,
            min_remove: 10,
            max_remove: None,
            horizon_end: TimePoint::new(num_traits::cast::<i64, T>(10_000).unwrap_or(T::zero())),
            local_time_radius: num_traits::cast::<i64, T>(3_600).unwrap_or(T::zero()),
            max_trials_per_request: 64,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> From<&Problem<T, C>> for RandomDestroyRepairOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(problem: &Problem<T, C>) -> Self {
        let stats = problem.stats();
        let m = stats.movable_count().max(1);
        let rho = problem.congestion_rho();
        let base_frac = 0.06_f64;
        let frac = (base_frac * (1.0 + rho)).clamp(0.02, 0.25);
        let min_remove = ((m as f64) * 0.04).round() as usize;
        let min_remove = min_remove.clamp(2, 24);
        let p50_proc = stats.p50_processing_time().value();
        let horizon_end = stats.latest_completion_time();
        let trials = (usize::ilog2(m).max(1) * 8).clamp(16, 96) as usize;

        Self {
            remove_frac: frac,
            min_remove,
            max_remove: None,
            horizon_end,
            local_time_radius: p50_proc,
            max_trials_per_request: trials,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for RandomDestroyRepairOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "RandomDestroyRepairPeekSafe"
    }

    #[instrument(level = "info", skip_all)]
    fn propose<'p, 'al, 'bo>(
        &self,
        _iteration: usize,
        rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, Self::Time, Self::Cost, Self::Quay>,
    ) -> Plan<'p, Self::Time, Self::Cost> {
        ctx.with_builder(|mut b| {
            let mut tx = b.begin();

            // gather current assignments through txn view
            let assignments =
                tx.with_explorer(|ex| ex.iter_movable_assignments().collect::<Vec<_>>());
            let n = assignments.len();
            if n == 0 {
                return b.build();
            }

            // dynamic horizon from txn view
            let latest_end = tx.with_explorer(|ex| {
                ex.iter_assignments()
                    .map(|a| a.start_time() + a.request().processing_duration())
                    .max()
            });
            let dyn_hi = latest_end.unwrap_or(TimePoint::new(Self::Time::zero()))
                + dock_alloc_core::time::TimeDelta::new(
                    Self::Time::from(1_000).unwrap_or(Self::Time::zero()),
                );
            let hi = if self.horizon_end > dyn_hi {
                self.horizon_end
            } else {
                dyn_hi
            };

            let time_window = TimeInterval::new(TimePoint::new(T::zero()), hi);

            // sample victims
            let frac = self.remove_frac.clamp(0.0, 1.0);
            let mut k = ((n as f64) * frac).round() as usize;
            k = k.clamp(self.min_remove.min(n), self.max_remove.unwrap_or(n).min(n));
            if k == 0 {
                return b.build();
            }
            let mut idxs: Vec<usize> = (0..n).collect();
            for i in 0..k {
                let j = rng.random_range(i..n);
                idxs.swap(i, j);
            }

            // destroy & repair inside the txn
            for &ix in idxs.iter().take(k) {
                let picked = assignments[ix].clone();
                let old_t = picked.start_time();
                let old_s = picked.start_position();
                let req = picked.branded_request();
                let space_window = req.feasible_space_window();

                // (A) peek alternative while still assigned
                let alt_slot_peek = tx.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&req, time_window, space_window)
                        .filter(|slot| {
                            let s = slot.slot().space().start();
                            let t = slot.slot().start_time();
                            s != old_s || t != old_t
                        })
                        .take(self.max_trials_per_request)
                        .next()
                });

                if let Some(slot) = alt_slot_peek {
                    if let Ok(region) = tx.propose_unassign(&picked) {
                        // return the result of propose_assign_at so types align
                        let _ = tx.propose_assign(&req, slot).or_else(|_| {
                            // best-effort restore inside the same txn
                            tx.propose_assign_at(&req, &region, old_t, old_s)
                        });
                    }
                    continue;
                }

                // (B) unassign then search
                let Ok(region) = tx.propose_unassign(&picked) else {
                    continue;
                };
                let alt_slot_after_free = tx.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&req, time_window, space_window)
                        .take(self.max_trials_per_request)
                        .find(|slot| {
                            let s = slot.slot().space().start();
                            let t = slot.slot().start_time();
                            s != old_s || t != old_t
                        })
                });

                if let Some(slot) = alt_slot_after_free {
                    let _ = tx
                        .propose_assign(&req, slot)
                        .or_else(|_| tx.propose_assign_at(&req, &region, old_t, old_s));
                } else {
                    let _ = tx.propose_assign_at(&req, &region, old_t, old_s);
                }
            }

            // full assignment gate
            let fully_assigned =
                tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none());
            if !fully_assigned {
                return b.build();
            }

            tx.commit();
            b.build()
        })
    }
}
