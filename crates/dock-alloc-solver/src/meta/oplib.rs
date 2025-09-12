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
use num_traits::{PrimInt, Signed, Zero};
use rand::Rng;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

/// Safe helper: choose two distinct *owned* items from a slice (uniform), or None if len < 2.
/// Requires T: Clone so we can return owned values compatible with engine expectations.
fn pick_two_distinct_owned<T: Clone>(v: &[T], rng: &mut ChaCha8Rng) -> Option<(T, T)> {
    let n = v.len();
    if n < 2 {
        return None;
    }
    let i = rng.random_range(0..n);
    let mut j = rng.random_range(0..(n - 1));
    if j >= i {
        j += 1; // j in 0..n and j != i
    }
    Some((v[i].clone(), v[j].clone()))
}

/// Reservoir sampling (k = 1) over Explorer::iter_movable_assignments().
/// Uniform single draw, total (never panics).
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
    for (i, a) in ex.iter_movable_assignments().enumerate() {
        if rng.random_range(0..=i) == 0 {
            chosen = Some(a);
        }
    }
    chosen
}

/// Reservoir sampling (k = 2) without panics, uniform over pairs.
/// Returns owned pair by cloning the reservoir items.
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
    let mut res: Vec<crate::registry::overlay::BrandedMovableAssignment<'alob, 'p, T, C>> =
        Vec::with_capacity(2);

    for (i, a) in ex.iter_movable_assignments().enumerate() {
        if res.len() < 2 {
            res.push(a);
        } else {
            let j = rng.random_range(0..=i);
            if j < 2 {
                res[j] = a;
            }
        }
    }

    if res.len() == 2 {
        Some((res[0].clone(), res[1].clone()))
    } else {
        None
    }
}

#[allow(dead_code)]
fn reservoir_k<T: Clone, I, R>(iter: I, k: usize, rng: &mut R) -> Vec<T>
where
    I: IntoIterator<Item = T>,
    R: Rng + ?Sized,
{
    let mut res: Vec<T> = Vec::with_capacity(k);
    for (i, item) in iter.into_iter().enumerate() {
        if res.len() < k {
            res.push(item);
        } else {
            let j = rng.random_range(0..=i);
            if j < k {
                res[j] = item;
            }
        }
    }
    res
}

// -----------------------------------------------------------------------------
// RandomSwapOperator
// -----------------------------------------------------------------------------

pub struct RandomSwapOperator<T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    /// How many random pairs to try before giving up.
    pub attempts: usize,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
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
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> RandomSwapOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    /// Heuristic from `&Problem`: try more pairs when there are more movables / higher congestion.
    pub fn from_problem(problem: &Problem<T, C>) -> Self {
        let m = problem.movable_count().max(1);
        let rho = problem.congestion_rho();
        // attempts ~ O(log m) scaled by rho in [0,2]
        let base = (m.max(1).ilog2() as usize) + 4;
        let scaled = (base as f64 * (1.0 + 0.5 * rho)).round() as usize;
        Self {
            attempts: scaled.clamp(6, 32),
            ..Self::default()
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
        rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let asgs = b.with_explorer(|ex| ex.iter_movable_assignments().collect::<Vec<_>>());
            if asgs.len() < 2 {
                return b.build(); // no-op
            }

            for _ in 0..self.attempts {
                let pair = b
                    .with_explorer(|ex| pick_two_random_asgs(ex, rng))
                    .or_else(|| pick_two_distinct_owned(&asgs, rng));
                let Some((a, bmv)) = pair else {
                    return b.build();
                };

                let req_a = a.branded_request();
                let req_b = bmv.branded_request();

                // must have identical footprint
                if req_a.length() != req_b.length()
                    || req_a.processing_duration() != req_b.processing_duration()
                {
                    continue;
                }

                let a_t = a.start_time();
                let a_s = a.start_position();
                let b_t = bmv.start_time();
                let b_s = bmv.start_position();

                // arrivals & windows
                if b_t < req_a.arrival_time() || a_t < req_b.arrival_time() {
                    continue;
                }
                let len = req_a.length();
                let a_win = req_a.feasible_space_window();
                let b_win = req_b.feasible_space_window();
                let a_ok = a_win.contains(b_s) && a_win.end() >= b_s + len;
                let b_ok = b_win.contains(a_s) && b_win.end() >= a_s + len;
                if !(a_ok && b_ok) {
                    continue;
                }

                // strict improvement pre-check
                let old_cost = a.assignment().cost() + bmv.assignment().cost();
                let a_if_at_b =
                    dock_alloc_model::model::AssignmentRef::new(req_a.request(), b_s, b_t);
                let b_if_at_a =
                    dock_alloc_model::model::AssignmentRef::new(req_b.request(), a_s, a_t);
                if a_if_at_b.cost() + b_if_at_a.cost() >= old_cost {
                    continue;
                }

                // --- Stage with precise rollbacks ---
                // Unassign A
                let reg_a = match b.propose_unassign(&a) {
                    Ok(r) => r,
                    Err(_) => continue, // nothing changed yet
                };

                // Unassign B (rollback A if we fail)
                let reg_b = match b.propose_unassign(&bmv) {
                    Ok(r) => r,
                    Err(_) => {
                        let _ = b.propose_assign_at(&req_a, &reg_a, a_t, a_s);
                        continue;
                    }
                };

                // Place A at B's spot (capture new handle)
                let a_new = match b.propose_assign_at(&req_a, &reg_b, b_t, b_s) {
                    Ok(h) => h,
                    Err(_) => {
                        // put both back
                        let _ = b.propose_assign_at(&req_a, &reg_a, a_t, a_s);
                        let _ = b.propose_assign_at(&req_b, &reg_b, b_t, b_s);
                        continue;
                    }
                };

                // Place B at A's spot (capture new handle)
                let b_new = match b.propose_assign_at(&req_b, &reg_a, a_t, a_s) {
                    Ok(h) => h,
                    Err(_) => {
                        // undo A-at-B, then restore originals
                        let _ = b.propose_unassign(&a_new);
                        let _ = b.propose_assign_at(&req_a, &reg_a, a_t, a_s);
                        let _ = b.propose_assign_at(&req_b, &reg_b, b_t, b_s);
                        continue;
                    }
                };

                // Full-assignment gate (paranoia)
                let fully_assigned =
                    b.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none());
                if !fully_assigned {
                    // rollback swap completely
                    let _ = b.propose_unassign(&a_new);
                    let _ = b.propose_unassign(&b_new);
                    let _ = b.propose_assign_at(&req_a, &reg_a, a_t, a_s);
                    let _ = b.propose_assign_at(&req_b, &reg_b, b_t, b_s);
                    continue;
                }

                // success
                return b.build();
            }

            b.build()
        })
    }
}

// -----------------------------------------------------------------------------
// RandomDestroyRepairOperator
// -----------------------------------------------------------------------------

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
    _phantom: core::marker::PhantomData<(T, C, Q)>,
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
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> RandomDestroyRepairOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    /// Heuristic from `&Problem` stats.
    pub fn from_problem(problem: &Problem<T, C>) -> Self {
        let stats = problem.stats();
        let m = stats.movable_count().max(1);
        let rho = problem.congestion_rho();

        // target remove count ~ frac * m; frac increases with congestion
        let base_frac = 0.06_f64; // baseline 6%
        let frac = (base_frac * (1.0 + rho)).clamp(0.02, 0.25);

        // min_remove grows slowly with size; leave room for tiny instances
        let min_remove = (m as f64 * 0.04).round() as usize;
        let min_remove = min_remove.clamp(2, 24);

        // local time radius from p50 proc (typed)
        let p50_proc = stats.p50_processing_time().value();

        // horizon end from latest completion time (typed)
        let horizon_end = stats.latest_completion_time().value();

        // trials ~ O(log m)
        let trials = (usize::ilog2(m as usize).max(1) as usize * 8).clamp(16, 96);

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
        rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, Self::Time, Self::Cost, Self::Quay>,
    ) -> Plan<'p, Self::Time, Self::Cost> {
        ctx.with_builder(|mut b| {
            let assignments =
                b.with_explorer(|ex| ex.iter_movable_assignments().collect::<Vec<_>>());
            let n = assignments.len();
            if n == 0 {
                return b.build();
            }

            // dynamic horizon: max(current latest end + buffer, configured horizon_end)
            let latest_end = b.with_explorer(|ex| {
                ex.iter_assignments()
                    .map(|a| a.start_time() + a.request().processing_duration())
                    .max()
            });
            let dyn_hi = latest_end.unwrap_or(TimePoint::new(T::zero()))
                + dock_alloc_core::time::TimeDelta::new(T::from(1_000).unwrap_or(T::zero()));
            let hi = TimePoint::new(core::cmp::max(self.horizon_end, dyn_hi.value()));
            let time_window = TimeInterval::new(TimePoint::new(T::zero()), hi);

            // Sample k victims without replacement (Fisher–Yates prefix)
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

            for &ix in idxs.iter().take(k) {
                let picked = assignments[ix].clone();
                let old_t = picked.start_time();
                let old_s = picked.start_position();
                let req = picked.branded_request();
                let space_window = req.feasible_space_window();

                // ---------- (A) Peek while assigned ----------
                let alt_slot_peek = b.with_explorer(|ex| {
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
                    // unassign -> try assign -> rollback if needed
                    if let Ok(region) = b.propose_unassign(&picked) {
                        if b.propose_assign(&req, slot).is_err() {
                            let _ = b.propose_assign_at(&req, &region, old_t, old_s);
                        }
                    } else {
                        // failed to unassign; keep going
                    }
                    continue;
                }

                // ---------- (B) Unassign then search ----------
                let Ok(region) = b.propose_unassign(&picked) else {
                    continue;
                };

                let alt_slot_after_free = b.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&req, time_window, space_window)
                        .take(self.max_trials_per_request)
                        .find(|slot| {
                            let s = slot.slot().space().start();
                            let t = slot.slot().start_time();
                            s != old_s || t != old_t
                        })
                });

                if let Some(slot) = alt_slot_after_free {
                    if b.propose_assign(&req, slot).is_err() {
                        let _ = b.propose_assign_at(&req, &region, old_t, old_s);
                    }
                } else {
                    // Nothing better even after freeing → restore
                    let _ = b.propose_assign_at(&req, &region, old_t, old_s);
                }
            }

            // full-assignment gate
            let fully_assigned =
                b.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none());
            if !fully_assigned {
                return b.build();
            }

            b.build()
        })
    }
}

// -----------------------------------------------------------------------------
// RelocateLocal
// -----------------------------------------------------------------------------

pub struct RelocateLocal<T, C, Q>
where
    T: SolverVariable + Zero + Send + Sync,
    C: SolverVariable + Send + Sync + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    pub time_radius: T,      // e.g. 1200
    pub space_radius: usize, // e.g. 400
    pub max_trials: usize,   // e.g. 16
    _phantom: core::marker::PhantomData<(T, C, Q)>,
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
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> RelocateLocal<T, C, Q>
where
    T: SolverVariable + Zero + Send + Sync,
    C: SolverVariable + Send + Sync + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    /// Heuristic from `&Problem`: local window sized by p50 length/proc and congestion.
    pub fn from_problem(problem: &Problem<T, C>) -> Self {
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
        let time_radius = {
            let tr = p50_proc + (p50_proc / T::from(2).unwrap_or(T::zero()));
            tr
        };

        // trials ~ O(log m)
        let trials = (usize::ilog2(m as usize).max(1) as usize * 4).clamp(8, 64);

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
        _rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let Some(cur) = b.with_explorer(|ex| ex.iter_movable_assignments().next()) else {
                return b.build();
            };

            let old_t = cur.start_time();
            let old_s = cur.start_position();
            let old_cost = cur.assignment().cost();
            let req = cur.branded_request();

            // local windows
            let quay_len = b.problem().quay_length().value();
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

            // find best improving slot (borrow via explorer)
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

            // unassign current, try assign to chosen; rollback on failure
            let Ok(region) = b.propose_unassign(&cur) else {
                return b.build();
            };

            if b.propose_assign(&req, chosen_slot).is_err() {
                let _ = b.propose_assign_at(&req, &region, old_t, old_s);
                return b.build();
            }

            // gate: remain fully assigned
            let fully_assigned =
                b.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none());
            if !fully_assigned {
                // rollback move
                if let Ok(new_handle) = b.with_explorer(|ex| {
                    // locate the (only) assignment for this request after the attempted move
                    ex.iter_movable_assignments()
                        .find(|m| m.branded_request().id() == req.id())
                        .ok_or(())
                }) {
                    let _ = b.propose_unassign(&new_handle);
                }
                let _ = b.propose_assign_at(&req, &region, old_t, old_s);
                return b.build();
            }

            b.build()
        })
    }
}
