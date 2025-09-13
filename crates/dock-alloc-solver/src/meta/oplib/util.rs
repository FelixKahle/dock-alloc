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

#![allow(dead_code)]

use dock_alloc_core::{
    SolverVariable,
    space::SpaceInterval,
    time::{TimeInterval, TimePoint},
};
use rand::Rng;

use crate::berth::{overlay::BrandedFreeSlot, quay::QuayRead};

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

pub fn reservoir_k<T: Clone, I, R>(iter: I, k: usize, rng: &mut R) -> Vec<T>
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

pub fn global_time_window<'p, 'al, 'bo, T, C, Q>(
    tx: &crate::framework::planning::Txn<'_, '_, '_, 'p, 'bo, 'al, T, C, Q>,
    soft_hi: TimePoint<T>,
) -> TimeInterval<T>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    let latest = tx.with_explorer(|ex| {
        ex.iter_assignments()
            .map(|a| a.start_time() + a.request().processing_duration())
            .max()
    });

    let dyn_hi = latest.unwrap_or(TimePoint::new(T::zero()))
        + dock_alloc_core::time::TimeDelta::new(T::from(1_000).unwrap_or(T::zero()));

    // Compare using the inner values
    let hi_val = core::cmp::max(soft_hi.value(), dyn_hi.value());
    let hi = TimePoint::new(hi_val);

    TimeInterval::new(TimePoint::new(T::zero()), hi)
}

pub fn best_improving_slot<'b, 'alob, 'boob, 'p, 'bo, 'al, T, C, Q>(
    tx: &'b crate::framework::planning::Txn<'_, 'alob, 'boob, 'p, 'bo, 'al, T, C, Q>,
    req: &crate::registry::overlay::BrandedMovableRequest<'alob, 'p, T, C>,
    time_w: dock_alloc_core::time::TimeInterval<T>,
    space_w: dock_alloc_core::space::SpaceInterval,
    old_cost: dock_alloc_core::cost::Cost<C>,
    max_trials: usize,
) -> Option<(dock_alloc_core::cost::Cost<C>, BrandedFreeSlot<'boob, T>)>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead,
{
    let mut best: Option<(dock_alloc_core::cost::Cost<C>, BrandedFreeSlot<'boob, T>)> = None;

    tx.with_explorer(|ex| {
        for slot in ex
            .iter_slots_for_request_within(req, time_w, space_w)
            .take(max_trials)
        {
            let t = slot.slot().start_time();
            let s = slot.slot().space().start();

            // Hypothetical assignment at (s, t)
            let hyp = dock_alloc_model::model::AssignmentRef::new(req.request(), s, t);
            let delta = hyp.cost() - old_cost;

            // Keep strictly improving candidates; track the best (most negative delta)
            if delta.value() < C::zero() && best.as_ref().is_none_or(|(bd, _)| delta < *bd) {
                best = Some((delta, slot));
            }
        }
    });

    best
}

pub fn req_windows<'alob, 'p, T, C>(
    req: &crate::registry::overlay::BrandedMovableRequest<'alob, 'p, T, C>,
    time_w: TimeInterval<T>,
    space_w: SpaceInterval,
) -> (TimeInterval<T>, SpaceInterval)
where
    T: SolverVariable,
    C: SolverVariable,
{
    // clamp by arrival and feasible space
    let arr = req.arrival_time();
    let t0 = if time_w.start() < arr {
        arr
    } else {
        time_w.start()
    };
    let t_w = TimeInterval::new(t0, time_w.end());
    let s_w = space_w
        .intersection(&req.feasible_space_window())
        .unwrap_or(req.feasible_space_window());
    (t_w, s_w)
}
