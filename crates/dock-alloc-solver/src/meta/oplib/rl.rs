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
    meta::operator::Operator,
};
use dock_alloc_core::{
    SolverVariable,
    space::{SpaceInterval, SpacePosition},
    time::{TimeInterval, TimePoint},
};
use dock_alloc_model::model::Problem;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

pub struct RelocateLocal<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead,
{
    pub time_radius: T,      // e.g. 1200
    pub space_radius: usize, // e.g. 400
    pub max_trials: usize,   // e.g. 16
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for RelocateLocal<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            time_radius: T::from(1200).unwrap_or(T::zero()),
            space_radius: 400,
            max_trials: 16,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> From<&Problem<T, C>> for RelocateLocal<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead,
{
    fn from(problem: &Problem<T, C>) -> Self {
        let s = problem.stats();
        let rho = problem.congestion_rho();
        let m = s.movable_count().max(1);

        // space radius ≈ ~1.5 * p50 request length, expanded a bit by congestion
        let p50_len = s.p50_request_length().value();
        let base_space = p50_len.saturating_mul(3) / 2;
        let space_radius = ((base_space as f64) * (1.0 + 0.5 * rho))
            .round()
            .clamp(8.0, 4_096.0) as usize;

        // time radius = ~1.5 * p50 proc time
        let p50_proc = s.p50_processing_time().value();
        let time_radius = { p50_proc + (p50_proc / T::from(2).unwrap_or(T::zero())) };

        // trials ~ O(log m)
        let trials = (usize::ilog2(m).max(1) as usize * 4).clamp(8, 64);

        Self {
            time_radius,
            space_radius,
            max_trials: trials,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for RelocateLocal<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize> + Send + Sync,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "RelocateLocal"
    }

    #[instrument(level = "info", skip_all)]
    fn propose<'p, 'al, 'bo>(
        &self,
        _it: usize,
        _rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let quay_len = b.problem().quay_length().value();

            let mut tx = b.begin();

            let Some(cur) = tx.with_explorer(|ex| ex.iter_movable_assignments().next()) else {
                return b.build();
            };

            let old_t = cur.start_time();
            let old_s = cur.start_position();
            let old_cost = cur.assignment().cost();
            let req = cur.branded_request();

            // local windows
            let s_min = SpacePosition::new(old_s.value().saturating_sub(self.space_radius));
            let s_max =
                SpacePosition::new((old_s.value().saturating_add(self.space_radius)).min(quay_len));
            let local_band = SpaceInterval::new(s_min, s_max);
            let fw = req.feasible_space_window();
            let space_bounds = fw.intersection(&local_band).unwrap_or(fw);

            let arr = req.arrival_time();
            let t_lo = core::cmp::max(arr, TimePoint::new(old_t.value() - self.time_radius));
            let t_hi = TimePoint::new(old_t.value() + self.time_radius);
            if t_lo >= t_hi {
                return b.build();
            }
            let time_window = TimeInterval::new(t_lo, t_hi);

            // search best improving slot via txn view
            let mut best: Option<(dock_alloc_core::cost::Cost<C>, BrandedFreeSlot<'_, T>)> = None;
            tx.with_explorer(|ex| {
                for slot in ex
                    .iter_slots_for_request_within(&req, time_window, space_bounds)
                    .filter(|s| {
                        let sp = s.slot().space().start();
                        let tp = s.slot().start_time();
                        sp != old_s || tp != old_t
                    })
                    .take(self.max_trials)
                {
                    let t_new = slot.slot().start_time();
                    let s_new = slot.slot().space().start();
                    let hyp =
                        dock_alloc_model::model::AssignmentRef::new(req.request(), s_new, t_new);
                    let delta = hyp.cost() - old_cost;
                    if delta.value() < C::zero() && best.as_ref().is_none_or(|(bd, _)| delta < *bd)
                    {
                        best = Some((delta, slot));
                    }
                }
            });

            let Some((_delta, chosen_slot)) = best else {
                return b.build();
            };

            if tx.propose_unassign(&cur).is_err() {
                return b.build();
            }
            if tx.propose_assign(&req, chosen_slot).is_err() {
                return b.build();
            }

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
