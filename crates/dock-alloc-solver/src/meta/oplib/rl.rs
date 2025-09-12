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
    meta::{operator::Operator, oplib::util::best_improving_slot},
};
use dock_alloc_core::{
    SolverVariable,
    cost::Cost,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimeInterval},
};
use dock_alloc_model::model::Problem;
use num_traits::FromPrimitive;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

pub struct RelocateLocal<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead,
{
    pub time_radius: TimeDelta<T>,
    pub space_radius: SpaceLength,
    pub max_trials: usize,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for RelocateLocal<T, C, Q>
where
    T: SolverVariable + FromPrimitive,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            time_radius: TimeDelta::new(T::from_i64(1200).unwrap_or_else(T::zero)),
            space_radius: SpaceLength::new(400),
            max_trials: 16,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> From<&Problem<T, C>> for RelocateLocal<T, C, Q>
where
    T: SolverVariable + FromPrimitive,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead,
{
    fn from(problem: &Problem<T, C>) -> Self {
        let s = problem.stats();
        let rho = s.rho();
        let m = s.movable_count().max(1);

        // Space radius: start near 1.5× p50, bump a bit with congestion, clamp to [p50, quay_len].
        let p50_len = s.p50_request_length();
        let quay = s.quay_length();
        let mut space = SpaceLength::new((p50_len.value() * 3) / 2); // 1.5×p50
        if rho >= 1.2 {
            space = SpaceLength::new((space.value() * 4) / 3);
        } // +33% in high ρ
        let space_radius = space.clamp(p50_len, quay);

        // Time radius: (2..4)× p50 proc, typed.
        let p50_proc = s.p50_processing_time();
        let mult_usz = if rho < 0.8 {
            2
        } else if rho < 1.2 {
            3
        } else {
            4
        };
        let mult_t = T::from_usize(mult_usz).unwrap_or_else(T::one);
        let time_radius = p50_proc * mult_t;

        // Trials: ~ 4·log2(m) scaled by ρ; keep modest to stay cheap.
        let base = (usize::ilog2(m).max(1) * 4) as f64;
        let max_trials = {
            let raw = (base * (1.0 + 0.5 * rho)).round() as usize;
            raw.clamp(8, 64)
        };

        Self {
            time_radius,
            space_radius,
            max_trials,
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
            let quay_len = b.problem().quay_length();
            let quay_span =
                SpaceInterval::new(SpacePosition::zero(), SpacePosition::zero() + quay_len);

            let mut tx = b.begin();

            // Single focused relocation per proposal (cheap; avoids long loops).
            let Some(cur) = tx.with_explorer(|ex| ex.iter_movable_assignments().next()) else {
                return b.build();
            };

            let req = cur.branded_request();
            let old_t = cur.start_time();
            let old_s = cur.start_position();
            let old_cost = cur.assignment().cost();

            // ---- helper to attempt within given radii
            let try_once = |time_r: TimeDelta<T>, space_r: SpaceLength| -> Option<(Cost<C>, _)> {
                // spatial band ∩ quay ∩ request window
                let left = old_s.saturating_sub(space_r);
                let right = old_s + space_r;
                let band = SpaceInterval::new(left, right);
                let s_w = req
                    .feasible_space_window()
                    .intersection(&band)
                    .unwrap_or(band)
                    .intersection(&quay_span)
                    .unwrap_or(band);

                // temporal band around old_t, respecting arrival
                let arr = req.arrival_time();
                let t_lo = core::cmp::max(arr, old_t - time_r);
                let t_hi = old_t + time_r;
                if t_lo >= t_hi {
                    return None;
                }
                let t_w = TimeInterval::new(t_lo, t_hi);

                best_improving_slot(&tx, &req, t_w, s_w, old_cost, self.max_trials)
            };

            // Try local, then a one-time widen (2× time, 4/3× space) if needed.
            let best = try_once(self.time_radius, self.space_radius).or_else(|| {
                let widened_t = self.time_radius + self.time_radius;
                let widened_s = SpaceLength::new((self.space_radius.value() * 4) / 3)
                    .clamp(self.space_radius, quay_len);
                try_once(widened_t, widened_s)
            });

            let Some((_delta, slot)) = best else {
                return b.build();
            };

            if tx.propose_unassign(&cur).is_err() {
                return b.build();
            }
            if tx.propose_assign(&req, slot).is_err() {
                return b.build();
            }

            let fully_assigned =
                tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none());
            if fully_assigned {
                tx.commit();
            }
            b.build()
        })
    }
}
