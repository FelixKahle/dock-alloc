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
use num_traits::{PrimInt, Signed, Zero};
use rand::{Rng, rngs::StdRng};
use tracing::instrument;

pub fn pick_random_asg<'alob, 'boob, 'p, 'bo, 'al, 'pb, T, C, Q, R>(
    ex: &crate::framework::planning::Explorer<'alob, 'boob, 'p, 'bo, 'al, 'pb, T, C, Q>,
    rng: &mut R,
) -> Option<crate::registry::overlay::BrandedMovableAssignment<'alob, 'p, T, C>>
where
    T: dock_alloc_core::SolverVariable,
    C: dock_alloc_core::SolverVariable,
    Q: crate::berth::quay::QuayRead,
    R: Rng + ?Sized,
{
    let mut chosen = None;

    for (seen, a) in ex.iter_movable_assignments().enumerate() {
        if rng.random_range(0..seen) == 0 {
            chosen = Some(a);
        }
    }
    chosen
}

pub fn pick_two_random_asgs<'alob, 'boob, 'p, 'bo, 'al, 'pb, T, C, Q, R>(
    ex: &crate::framework::planning::Explorer<'alob, 'boob, 'p, 'bo, 'al, 'pb, T, C, Q>,
    rng: &mut R,
) -> Option<(
    crate::registry::overlay::BrandedMovableAssignment<'alob, 'p, T, C>,
    crate::registry::overlay::BrandedMovableAssignment<'alob, 'p, T, C>,
)>
where
    T: dock_alloc_core::SolverVariable,
    C: dock_alloc_core::SolverVariable,
    Q: crate::berth::quay::QuayRead,
    R: Rng + ?Sized,
{
    let mut r0 = None;
    let mut r1 = None;

    for (seen, a) in ex.iter_movable_assignments().enumerate() {
        if seen == 1 {
            r0 = Some(a);
        } else if seen == 2 {
            r1 = Some(a);
        } else {
            // replace with probability 2/i
            let j = rng.random_range(0..seen);
            if j == 0 {
                r0 = Some(a);
            } else if j == 1 {
                r1 = Some(a);
            }
        }
    }

    match (r0, r1) {
        (Some(a), Some(b)) => Some((a, b)),
        _ => None,
    }
}

#[allow(dead_code)]
fn reservoir_k<T, I, R>(iter: I, k: usize, rng: &mut R) -> Vec<T>
where
    I: IntoIterator<Item = T>,
    R: Rng + ?Sized,
{
    let mut res: Vec<T> = Vec::with_capacity(k);
    for (i, item) in iter.into_iter().enumerate() {
        if res.len() < k {
            res.push(item);
        } else {
            let j = rng.random_range(0..i);
            if j < k {
                res[j] = item;
            }
        }
    }
    res
}

pub struct RandomSwapOperator<T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    /// How many random pairs to try before giving up.
    pub attempts: usize,
    _phantom: std::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for RandomSwapOperator<T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            attempts: 8,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for RandomSwapOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "RandomSwap"
    }

    #[instrument(level = "info", skip_all, name = "RandomSwap")]
    fn propose<'p, 'al, 'bo>(
        &self,
        _iteration: usize,
        rng: &mut StdRng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let asgs = b.with_explorer(|ex| ex.iter_movable_assignments().collect::<Vec<_>>());
            let n = asgs.len();
            if n < 2 {
                return b.build();
            }

            for _ in 0..self.attempts {
                let pair = b.with_explorer(|ex| pick_two_random_asgs(ex, rng));
                let Some((a, bmv)) = pair else {
                    return b.build(); // fewer than 2 movables
                };

                // brand-preserving request handles
                let req_a = a.branded_request();
                let req_b = bmv.branded_request();

                // rectangles must match in size
                if req_a.length() != req_b.length()
                    || req_a.processing_duration() != req_b.processing_duration()
                {
                    continue;
                }

                let a_t = a.start_time();
                let a_s = a.start_position();
                let b_t = bmv.start_time();
                let b_s = bmv.start_position();

                if b_t < req_a.arrival_time() || a_t < req_b.arrival_time() {
                    continue;
                }

                let len = req_a.length();
                let a_win = req_a.feasible_space_window();
                let b_win = req_b.feasible_space_window();
                let a_target_ok = a_win.contains(b_s) && a_win.end() >= b_s + len;
                let b_target_ok = b_win.contains(a_s) && b_win.end() >= a_s + len;
                if !(a_target_ok && b_target_ok) {
                    continue;
                }

                // pre-check cost delta
                let old_cost = a.assignment().cost() + bmv.assignment().cost();
                let a_if_at_b =
                    dock_alloc_model::model::AssignmentRef::new(req_a.request(), b_s, b_t);
                let b_if_at_a =
                    dock_alloc_model::model::AssignmentRef::new(req_b.request(), a_s, a_t);
                let new_cost = a_if_at_b.cost() + b_if_at_a.cost();
                if new_cost >= old_cost {
                    continue;
                }

                // stage swap
                let reg_a = match b.propose_unassign(&a) {
                    Ok(r) => r,
                    Err(_) => continue,
                };
                let reg_b = match b.propose_unassign(&bmv) {
                    Ok(r) => r,
                    Err(_) => {
                        let _ = b.propose_assign_at(&req_a, &reg_a, a_t, a_s);
                        return b.build();
                    }
                };

                if b.propose_assign_at(&req_a, &reg_b, b_t, b_s).is_err() {
                    let _ = b.propose_assign_at(&req_a, &reg_a, a_t, a_s);
                    let _ = b.propose_assign_at(&req_b, &reg_b, b_t, b_s);
                    return b.build();
                }

                if b.propose_assign_at(&req_b, &reg_a, a_t, a_s).is_err() {
                    let _ = b.propose_assign_at(&req_a, &reg_a, a_t, a_s);
                    let _ = b.propose_assign_at(&req_b, &reg_b, b_t, b_s);
                    return b.build();
                }

                return b.build();
            }

            b.build()
        })
    }
}

pub struct RandomDestroyRepairOperator<T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    pub remove_frac: f64,
    pub min_remove: usize,
    pub max_remove: Option<usize>,
    /// soft upper bound for search
    pub horizon_end: T,
    /// local radius (time units) for peeking alternatives around current start
    pub local_time_radius: T,
    /// cap on scanned alternatives per request
    pub max_trials_per_request: usize,
    _phantom: std::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for RandomDestroyRepairOperator<T, C, Q>
where
    T: PrimInt + Signed + Zero,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            remove_frac: 0.10,
            min_remove: 10,
            max_remove: None,
            horizon_end: num_traits::cast::<i64, T>(10_000).unwrap_or(T::zero()),
            local_time_radius: num_traits::cast::<i64, T>(3_600).unwrap_or(T::zero()),
            max_trials_per_request: 64,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for RandomDestroyRepairOperator<T, C, Q>
where
    T: SolverVariable + Zero + Send + Sync,
    C: SolverVariable + Send + Sync + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "RandomDestroyRepairPeekSafe"
    }

    #[instrument(level = "info", skip_all, name = "RandomDestroyRepairPeekSafe")]
    fn propose<'p, 'al, 'bo>(
        &self,
        _iteration: usize,
        rng: &mut StdRng,
        ctx: PlanningContext<'p, 'al, 'bo, Self::Time, Self::Cost, Self::Quay>,
    ) -> Plan<'p, Self::Time, Self::Cost> {
        ctx.with_builder(|mut b| {
            // Snapshot current assignments once for this builder.
            let assignments =
                b.with_explorer(|ex| ex.iter_movable_assignments().collect::<Vec<_>>());
            let n = assignments.len();
            if n == 0 {
                return b.build();
            }

            let latest_end = b.with_explorer(|ex| {
                ex.iter_assignments()
                    .map(|a| a.start_time() + a.request().processing_duration())
                    .max()
            });
            let dyn_hi = latest_end.unwrap_or(TimePoint::new(T::zero()))
                + dock_alloc_core::time::TimeDelta::new(T::from(1_000).unwrap_or(T::zero()));
            let hi = {
                let he: T = self.horizon_end;
                let d: T = dyn_hi.value();
                TimePoint::new(core::cmp::max(he, d))
            };

            let time_window = TimeInterval::new(TimePoint::new(T::zero()), hi);

            // Sample k victims without replacement
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

            let mut any_change = false;

            for &ix in idxs.iter().take(k) {
                let picked = assignments[ix].clone(); // BrandedMovableAssignment (assigned)
                let old_t = picked.start_time();
                let old_s = picked.start_position();

                // Use the branded request directly
                let req_assigned = picked.branded_request();
                let space_window = req_assigned.feasible_space_window();

                // ---------- (A) PEEK: try to find an alternative while still assigned ----------
                let alt_slot_peek = b.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&req_assigned, time_window, space_window)
                        .filter(|slot| {
                            let s = slot.slot().space().start();
                            let t = slot.slot().start_time();
                            s != old_s || t != old_t
                        })
                        .take(self.max_trials_per_request)
                        .next()
                });

                // If peek found an alternative, we’ll unassign+assign to realize it.
                if let Some(slot) = alt_slot_peek {
                    // Free the old rectangle (keep region for safe rollback)
                    let Ok(region) = b.propose_unassign(&picked) else {
                        continue;
                    };

                    // After unassign, the same branded handle is now "unassigned" by type.
                    // We can safely assign to the new slot.
                    if b.propose_assign(&req_assigned, slot).is_ok() {
                        any_change = true;
                        continue;
                    } else {
                        // rollback to exact original placement
                        let _ = b.propose_assign_at(&req_assigned, &region, old_t, old_s);
                        continue;
                    }
                }

                // ---------- (B) FALLBACK: unassign first, then rescan (widens free regions) ----------
                let Ok(region) = b.propose_unassign(&picked) else {
                    continue;
                };

                // Try again with the assignment removed; exclude the original rectangle
                let alt_slot_after_free = b.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&req_assigned, time_window, space_window)
                        .take(self.max_trials_per_request)
                        .find(|slot| {
                            let s = slot.slot().space().start();
                            let t = slot.slot().start_time();
                            s != old_s || t != old_t
                        })
                });

                if let Some(slot) = alt_slot_after_free {
                    if b.propose_assign(&req_assigned, slot).is_ok() {
                        any_change = true;
                    } else {
                        // restore exactly
                        let _ = b.propose_assign_at(&req_assigned, &region, old_t, old_s);
                    }
                } else {
                    // Nothing better even after freeing → restore
                    let _ = b.propose_assign_at(&req_assigned, &region, old_t, old_s);
                }
            }

            if !any_change {
                // Return truly empty plan if nothing changed, so the engine can report “no candidates”.
                return b.build();
            }

            b.build()
        })
    }
}

pub struct RelocateLocal<T, C, Q>
where
    T: SolverVariable + Zero + Send + Sync,
    C: SolverVariable + Send + Sync + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    pub time_radius: T,      // e.g. 1200
    pub space_radius: usize, // e.g. 400
    pub max_trials: usize,   // e.g. 16
    _phantom: std::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for RelocateLocal<T, C, Q>
where
    T: SolverVariable + Zero + Send + Sync,
    C: SolverVariable + Send + Sync + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    fn default() -> Self {
        Self {
            time_radius: T::from(1200).unwrap_or(T::zero()),
            space_radius: 400,
            max_trials: 16,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for RelocateLocal<T, C, Q>
where
    T: SolverVariable + Zero + Send + Sync,
    C: SolverVariable + TryFrom<T> + TryFrom<usize> + Send + Sync,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "RelocateLocal"
    }

    #[instrument(level = "info", skip_all, name = "RelocateLocal")]
    fn propose<'p, 'al, 'bo>(
        &self,
        _it: usize,
        _rng: &mut StdRng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let Some(cur) = b.with_explorer(|ex| ex.iter_movable_assignments().next()) else {
                return b.build();
            };

            let old_t = cur.start_time();
            let old_s = cur.start_position();
            let old_cost = cur.assignment().cost();

            // brand-preserving request
            let req = cur.branded_request();

            // local space bounds around old_s ∩ feasible window
            let quay_len = b.problem().quay_length().value();
            let s_min = SpacePosition::new(old_s.value().saturating_sub(self.space_radius));
            let s_max =
                SpacePosition::new((old_s.value().saturating_add(self.space_radius)).min(quay_len));
            let local_band = SpaceInterval::new(s_min, s_max);
            let fw = req.feasible_space_window();
            let space_bounds = fw.intersection(&local_band).unwrap_or(fw);

            // local time window around old_t, clamped by arrival
            let arr = req.arrival_time();
            let t_lo = core::cmp::max(arr, TimePoint::new(old_t.value() - self.time_radius));
            let t_hi = TimePoint::new(old_t.value() + self.time_radius);
            if t_lo >= t_hi {
                return b.build();
            }
            let time_window = TimeInterval::new(t_lo, t_hi);

            // best strictly-improving candidate
            let mut best: Option<(dock_alloc_core::cost::Cost<C>, BrandedFreeSlot<'_, T>)> = None;

            b.with_explorer(|ex| {
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

            // stage: unassign then assign using the same branded request
            let Ok(region) = b.propose_unassign(&cur) else {
                return b.build();
            };

            if b.propose_assign(&req, chosen_slot).is_err() {
                // restore original
                let _ = b.propose_assign_at(&req, &region, old_t, old_s);
            }

            b.build()
        })
    }
}
