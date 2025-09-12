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
    berth::quay::QuayRead,
    framework::planning::{Plan, PlanningContext},
    meta::{operator::Operator, oplib::util::best_improving_slot},
};
use dock_alloc_core::{
    SolverVariable,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimeInterval},
};
use dock_alloc_model::model::Problem;
use num_traits::FromPrimitive;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

pub struct MultiRelocateShakerOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub relocations: usize,
    pub local_time_radius: TimeDelta<T>,
    pub local_space_radius: SpaceLength,
    _phantom: core::marker::PhantomData<(C, Q)>,
}

impl<T, C, Q> Default for MultiRelocateShakerOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            relocations: 3,
            local_time_radius: TimeDelta::new(T::zero()),
            local_space_radius: SpaceLength::new(256),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> From<&Problem<T, C>> for MultiRelocateShakerOperator<T, C, Q>
where
    T: SolverVariable + FromPrimitive,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(p: &Problem<T, C>) -> Self {
        let s = p.stats();
        let quay_len = s.quay_length();
        let p50_len = s.p50_request_length();
        let p90_len = s.p90_request_length();
        let p50_proc = s.p50_processing_time();
        let rho = s.rho();
        let mov = p.movable_count();

        // spatial radius: ~2×p90, clamped into [p50, quay_len]
        let space_base = p90_len * 2;
        let local_space_radius = space_base.clamp(p50_len, quay_len);

        // time radius: (~2×p50) * congestion factor, all in typed units
        let time_scale_usize = if rho < 0.9 {
            2
        } else if rho < 1.2 {
            3
        } else {
            4
        };
        let time_scale_t: T = T::from_usize(time_scale_usize).unwrap_or_else(T::one);
        let local_time_radius = p50_proc * time_scale_t;

        // relocations: small; bump with ρ and instance size
        let base = if rho < 0.6 {
            2
        } else if rho < 0.9 {
            3
        } else if rho < 1.2 {
            4
        } else {
            5
        };
        let relocations = core::cmp::min(8, base + (mov / 50));

        Self {
            relocations,
            local_time_radius,
            local_space_radius,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for MultiRelocateShakerOperator<T, C, Q>
where
    T: SolverVariable + Send + Sync,
    C: SolverVariable + TryFrom<T> + TryFrom<usize> + Send + Sync,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "MultiRelocateShaker"
    }

    #[instrument(level = "info", skip_all)]
    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        _: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let quay_len = b.problem().quay_length();
            let quay_span =
                SpaceInterval::new(SpacePosition::zero(), SpacePosition::zero() + quay_len);

            let mut tx = b.begin();
            let mut done = 0usize;

            // Iterate one-at-a-time to avoid holding an immutable borrow
            while done < self.relocations {
                // pick the next movable (or stop)
                let maybe_cur = tx.with_explorer(|ex| ex.iter_movable_assignments().next());
                let Some(cur) = maybe_cur else {
                    break;
                };

                let req = cur.branded_request();
                let old_cost = cur.assignment().cost();
                let old_t = cur.start_time();
                let old_s = cur.start_position();

                // Local spatial band around old_s, clamped to quay span and request window
                let left = old_s.saturating_sub(self.local_space_radius);
                let right = old_s + self.local_space_radius;
                let band = SpaceInterval::new(left, right);
                let s_w = req
                    .feasible_space_window()
                    .intersection(&band)
                    .unwrap_or(band)
                    .intersection(&quay_span)
                    .unwrap_or(band);

                // Local time window around old_t, respecting arrival
                let arr = req.arrival_time();
                let t_lo = core::cmp::max(arr, old_t - self.local_time_radius);
                let t_hi = old_t + self.local_time_radius;
                if t_lo >= t_hi {
                    // cannot form a valid local time window; skip this one
                    // (optionally: try next movable instead of breaking)
                    break;
                }
                let t_w = TimeInterval::new(t_lo, t_hi);

                // Best improving nearby (outside of with_explorer borrow)
                let best =
                    tx.with_explorer(|_| best_improving_slot(&tx, &req, t_w, s_w, old_cost, 64));
                let Some((_d, slot)) = best else {
                    // no improvement found locally; optionally continue with next movable
                    break;
                };

                // Perform relocation (mutable borrows happen here, no explorer borrow alive)
                if tx.propose_unassign(&cur).is_ok() && tx.propose_assign(&req, slot).is_ok() {
                    done += 1;
                }
            }

            if done > 0 && tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}
