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
    berth::{
        domain::{FreeRegion, FreeSlot},
        slice::SliceView,
    },
    domain::SpaceTimeRectangle,
};
use dock_alloc_core::{
    domain::{SpaceInterval, SpaceLength, TimeDelta, TimeInterval, TimePoint},
    iter::MaybeIter,
    mem::DoubleBuf,
};
use num_traits::{One, PrimInt, Signed};
use std::iter::FusedIterator;

struct CandidateStartIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    view: &'a V,
    duration: TimeDelta<T>,
    time_window_end: TimePoint<T>,
    last_candidate: Option<TimePoint<T>>,
    first_candidate: TimePoint<T>,
}

impl<'a, T, V> CandidateStartIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    fn new(view: &'a V, time_window: TimeInterval<T>, duration: TimeDelta<T>) -> Self {
        Self {
            view,
            duration,
            time_window_end: time_window.end(),
            last_candidate: None,
            first_candidate: time_window.start(),
        }
    }
}

impl<'a, T, V> Iterator for CandidateStartIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    type Item = TimePoint<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let end = self.time_window_end;

        if self.last_candidate.is_none() {
            let first = self.first_candidate;
            if first + self.duration <= end {
                self.last_candidate = Some(first);
                return self.last_candidate;
            }
            return None;
        }

        let last = self.last_candidate.unwrap();
        if let Some(tp) = self.view.next_key_after(last) {
            if tp + self.duration <= end {
                self.last_candidate = Some(tp);
                return self.last_candidate;
            }
        } else if self.duration.is_zero() && last < end && self.view.has_key_at(end) {
            self.last_candidate = Some(end);
            return self.last_candidate;
        }

        None
    }
}

pub struct FreeSlotIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    view: &'a V,
    duration: TimeDelta<T>,
    required: SpaceLength,
    bounds: SpaceInterval,
    candidate_starts: CandidateStartIter<'a, T, V>,
    runs: DoubleBuf<SpaceInterval>,
    current_start: Option<TimePoint<T>>,
    emit_idx: usize,
    is_empty: bool,
}

impl<'a, T, V> FreeSlotIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    #[inline]
    pub(crate) fn new(
        view: &'a V,
        time_window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> Self {
        let duration = duration.max(TimeDelta::zero());
        let invalid =
            required > bounds.length() || time_window.start() + duration > time_window.end();
        Self {
            view,
            duration,
            required,
            bounds,
            candidate_starts: CandidateStartIter::new(view, time_window, duration),
            runs: DoubleBuf::new(),
            current_start: None,
            emit_idx: 0,
            is_empty: invalid,
        }
    }

    fn build_runs_for_start(&mut self, start: TimePoint<T>) {
        self.runs.clear();
        self.emit_idx = 0;
        self.current_start = None;

        let end = start + self.duration;
        eroded_runs(
            self.view,
            start,
            end,
            self.bounds,
            self.required,
            &mut self.runs,
        );

        if !self.runs.current().is_empty() {
            self.current_start = Some(start);
        }
    }
}

impl<'a, T, V> Iterator for FreeSlotIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    type Item = FreeSlot<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_empty {
            return None;
        }

        loop {
            if let Some(start_time) = self.current_start {
                if self.emit_idx < self.runs.current().len() {
                    let space_interval = self.runs.current()[self.emit_idx];
                    self.emit_idx += 1;
                    return Some(FreeSlot::new(space_interval, start_time));
                }
                self.current_start = None;
            }
            let candidate_start = self.candidate_starts.next()?;
            self.build_runs_for_start(candidate_start);
            if self.current_start.is_none() {
                continue;
            }
        }
    }
}

fn calculate_breakpoints<T, V>(
    view: &V,
    time_window: TimeInterval<T>,
    duration: TimeDelta<T>,
) -> Vec<TimePoint<T>>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T>,
{
    let tw_start = time_window.start();
    let latest_start = time_window.end() - duration;

    if tw_start > latest_start {
        return Vec::new();
    }

    let bps_left = collect_keys(view, tw_start, latest_start);
    let shifted_left = tw_start + duration;
    let shifted_right = latest_start + duration;
    let one = TimeDelta::new(T::one());

    let bps_right: Vec<_> = collect_keys_left_inclusive(view, shifted_left, shifted_right)
        .into_iter()
        .map(|t| t - duration + one)
        .filter(|&t| t > tw_start && t <= latest_start)
        .collect();

    let mut out = Vec::with_capacity(2 + bps_left.len() + bps_right.len());
    out.push(tw_start);

    let mut i = 0usize;
    let mut j = 0usize;
    let mut last: Option<TimePoint<T>> = out.last().copied();

    #[inline]
    fn push_if_new<Tp>(out: &mut Vec<Tp>, last: &mut Option<Tp>, x: Tp)
    where
        Tp: PartialEq + Copy,
    {
        if Some(x) != *last {
            out.push(x);
            *last = Some(x);
        }
    }

    while i < bps_left.len() && j < bps_right.len() {
        let a = bps_left[i];
        let b = bps_right[j];
        if a <= b {
            i += 1;
            push_if_new(&mut out, &mut last, a);
        } else {
            j += 1;
            push_if_new(&mut out, &mut last, b);
        }
    }

    while i < bps_left.len() {
        let a = bps_left[i];
        i += 1;
        push_if_new(&mut out, &mut last, a);
    }

    while j < bps_right.len() {
        let b = bps_right[j];
        j += 1;
        push_if_new(&mut out, &mut last, b);
    }

    if Some(latest_start) != last {
        out.push(latest_start);
    }
    out
}

fn collect_keys_left_inclusive<T, V>(
    view: &V,
    from: TimePoint<T>,
    to: TimePoint<T>,
) -> Vec<TimePoint<T>>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T>,
{
    let mut out = Vec::new();
    if view.has_key_at(from) {
        out.push(from);
    }
    let mut cursor = from;
    while let Some(tp) = view.next_key_after(cursor) {
        if tp >= to {
            break;
        }
        out.push(tp);
        cursor = tp;
    }
    out
}

fn collect_keys<T, V>(view: &V, from: TimePoint<T>, to: TimePoint<T>) -> Vec<TimePoint<T>>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T>,
{
    let mut out = Vec::new();
    let mut cursor = from;
    while let Some(tp) = view.next_key_after(cursor) {
        if tp >= to {
            break;
        }
        out.push(tp);
        cursor = tp;
    }
    out
}

pub struct FeasibleRegionIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    view: &'a V,
    duration: TimeDelta<T>,
    required: SpaceLength,
    bounds: SpaceInterval,
    breakpoints: Vec<TimePoint<T>>,
    bp_idx: usize,
    cur_runs: DoubleBuf<SpaceInterval>,
    run_idx: usize,
    seg_start: TimePoint<T>,
    seg_end: TimePoint<T>,
}

impl<'a, T, V> FeasibleRegionIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    #[inline]
    pub(crate) fn new(
        view: &'a V,
        time_window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> Self {
        let duration = duration.max(TimeDelta::zero());
        let latest_start = time_window.end() - duration;

        let breakpoints = if time_window.start() > latest_start || required > bounds.length() {
            Vec::new()
        } else {
            calculate_breakpoints(view, time_window, duration)
        };

        Self {
            view,
            duration,
            required,
            bounds,
            breakpoints,
            bp_idx: 0,
            cur_runs: DoubleBuf::new(),
            run_idx: 0,
            seg_start: time_window.start(),
            seg_end: time_window.start(),
        }
    }
}

#[inline]
fn rep_start<T: PrimInt + Signed + Copy + One>(a: TimePoint<T>, b: TimePoint<T>) -> TimePoint<T> {
    let one = TimeDelta::new(T::one());
    if a + one < b { a + one } else { a }
}

impl<'a, T, V> Iterator for FeasibleRegionIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    type Item = FreeRegion<T>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // If we have runs for the current time segment, yield them.
            if self.run_idx < self.cur_runs.current().len() {
                let space_interval = self.cur_runs.current()[self.run_idx];
                self.run_idx += 1;
                let rect = SpaceTimeRectangle::new(
                    space_interval,
                    TimeInterval::new(self.seg_start, self.seg_end),
                );
                return Some(FreeRegion::new(rect));
            }

            if self.bp_idx + 1 >= self.breakpoints.len() {
                return None;
            }
            self.seg_start = self.breakpoints[self.bp_idx];
            self.seg_end = self.breakpoints[self.bp_idx + 1];
            self.bp_idx += 1;

            if self.seg_start >= self.seg_end {
                continue;
            }

            let representative_start = rep_start(self.seg_start, self.seg_end);
            self.cur_runs.clear();
            eroded_runs(
                self.view,
                representative_start,
                representative_start + self.duration,
                self.bounds,
                self.required,
                &mut self.cur_runs,
            );
            self.run_idx = 0;

            if self.cur_runs.current().is_empty() {
                continue;
            }
        }
    }
}

#[inline]
pub(crate) fn runs_cover_interval<I>(runs: I, target: SpaceInterval) -> bool
where
    I: Iterator<Item = SpaceInterval>,
{
    if target.is_empty() {
        return true;
    }

    let mut runs = runs.peekable();
    let mut need_start = target.start();
    let need_end = target.end();

    while let Some(run) = runs.next() {
        if run.end() <= need_start {
            continue;
        }
        if run.start() > need_start {
            return false;
        }
        let mut covered_end = run.end();
        while let Some(next_run) = runs.peek().copied() {
            if next_run.start() > covered_end {
                break;
            }
            if next_run.end() > covered_end {
                covered_end = next_run.end();
            }
            runs.next();
        }

        if covered_end >= need_end {
            return true;
        }
        need_start = covered_end;
    }

    false
}

#[inline]
fn runs_at<'v, T, V>(
    view: &'v V,
    time_point: TimePoint<T>,
    bounds: SpaceInterval,
    min_len: SpaceLength,
) -> impl Iterator<Item = SpaceInterval> + 'v
where
    T: PrimInt + Signed,
    V: SliceView<T> + ?Sized + 'v,
{
    let inner = (bounds.length() >= min_len).then(|| {
        view.free_runs_at(time_point)
            .filter_map(move |iv| bounds.intersection(&iv))
            .filter(move |iv| iv.length() >= min_len)
    });

    MaybeIter::new(inner)
}

/// An iterator that intersects two sorted, non-overlapping iterators of `SpaceInterval`.
struct IntersectRuns<L, R>
where
    R: Iterator,
{
    left: L,
    right: std::iter::Peekable<R>,
    cur_left: Option<SpaceInterval>,
    cur_right: Option<SpaceInterval>,
    required: SpaceLength,
}

impl<L, R> IntersectRuns<L, R>
where
    L: Iterator<Item = SpaceInterval>,
    R: Iterator<Item = SpaceInterval>,
{
    #[inline]
    fn new(left: L, right: R, required: SpaceLength) -> Self {
        Self {
            left,
            right: right.peekable(),
            cur_left: None,
            cur_right: None,
            required,
        }
    }
}

impl<L, R> Iterator for IntersectRuns<L, R>
where
    L: Iterator<Item = SpaceInterval>,
    R: Iterator<Item = SpaceInterval>,
{
    type Item = SpaceInterval;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.cur_left.is_none() {
                self.cur_left = self.left.next();
            }
            if self.cur_right.is_none() {
                self.cur_right = self.right.next();
            }
            let (a, b) = match (self.cur_left, self.cur_right) {
                (Some(a), Some(b)) => (a, b),
                _ => return None,
            };

            let inter = a.intersection(&b);
            if a.end() <= b.end() {
                self.cur_left = None;
            } else {
                self.cur_right = None;
            }

            if let Some(iv) = inter
                && iv.length() >= self.required
            {
                return Some(iv);
            }
        }
    }
}

#[inline]
fn eroded_runs<'v, T, V>(
    view: &'v V,
    start: TimePoint<T>,
    end: TimePoint<T>,
    bounds: SpaceInterval,
    min_len: SpaceLength,
    out_runs: &mut DoubleBuf<SpaceInterval>,
) where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + ?Sized + 'v,
{
    let pred = match view.pred(start) {
        Some(p) => p,
        None => return,
    };
    let seed_tp = if view.has_key_at(start) { start } else { pred };

    out_runs.seed_from_iter(runs_at(view, seed_tp, bounds, min_len));

    if out_runs.current().is_empty() {
        return;
    }

    let mut cursor = start;
    while let Some(tp) = view.next_key_after(cursor) {
        if tp >= end {
            break;
        }
        cursor = tp;
        out_runs.step(|cur, next| {
            next.extend(IntersectRuns::new(
                cur.iter().copied(),
                runs_at(view, tp, bounds, min_len),
                min_len,
            ));
        });
        if out_runs.current().is_empty() {
            return;
        }
    }
}

#[derive(Clone)]
pub enum OverlayRunsIter<I>
where
    I: Iterator<Item = SpaceInterval>,
{
    Base(I),
    Owned(std::vec::IntoIter<SpaceInterval>),
}

impl<I> Iterator for OverlayRunsIter<I>
where
    I: Iterator<Item = SpaceInterval>,
{
    type Item = SpaceInterval;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            OverlayRunsIter::Base(it) => it.next(),
            OverlayRunsIter::Owned(it) => it.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            OverlayRunsIter::Base(it) => it.size_hint(),
            OverlayRunsIter::Owned(it) => it.size_hint(),
        }
    }
}

impl<I> FusedIterator for OverlayRunsIter<I> where I: Iterator<Item = SpaceInterval> + FusedIterator {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::berth::{berthocc::BerthOccupancy, quay::BooleanVecQuay};
    use num_traits::Zero;

    type T = i64;
    type BO = BerthOccupancy<T, BooleanVecQuay>;

    #[inline]
    fn pos(x: usize) -> dock_alloc_core::domain::SpacePosition {
        dock_alloc_core::domain::SpacePosition::new(x)
    }
    #[inline]
    fn len(x: usize) -> dock_alloc_core::domain::SpaceLength {
        dock_alloc_core::domain::SpaceLength::new(x)
    }
    #[inline]
    fn si(a: usize, b: usize) -> dock_alloc_core::domain::SpaceInterval {
        dock_alloc_core::domain::SpaceInterval::new(pos(a), pos(b))
    }
    #[inline]
    fn tp(t: T) -> dock_alloc_core::domain::TimePoint<T> {
        dock_alloc_core::domain::TimePoint::new(t)
    }
    #[inline]
    fn ti(a: T, b: T) -> dock_alloc_core::domain::TimeInterval<T> {
        dock_alloc_core::domain::TimeInterval::new(tp(a), tp(b))
    }
    #[inline]
    fn rect(
        tw: dock_alloc_core::domain::TimeInterval<T>,
        si: dock_alloc_core::domain::SpaceInterval,
    ) -> SpaceTimeRectangle<T> {
        SpaceTimeRectangle::new(si, tw)
    }

    fn collect_free_iter(
        v: &BO,
        tw: TimeInterval<T>,
        dur: TimeDelta<T>,
        need: SpaceLength,
        bounds: SpaceInterval,
    ) -> Vec<(T, (usize, usize))> {
        FreeSlotIter::new(v, tw, dur, need, bounds)
            .map(|f| {
                (
                    f.start_time().value(),
                    (f.space().start().value(), f.space().end().value()),
                )
            })
            .collect()
    }

    #[test]
    fn test_free_iter_fully_free_single_candidate() {
        let b = BO::new(len(8));
        let items = collect_free_iter(&b, ti(0, 10), TimeDelta::new(3), len(2), si(0, 5));
        assert_eq!(items, vec![(0, (0, 5))]);
    }

    #[test]
    fn test_free_iter_candidates_include_timepoints() {
        // Create extra slice keys at t=5 and t=6 without affecting bounds [0,5)
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 6), si(9, 10))).unwrap(); // keys 5,6

        let items = collect_free_iter(&b, ti(0, 10), TimeDelta::new(3), len(2), si(0, 5));
        assert_eq!(items, vec![(0, (0, 5)), (5, (0, 5)), (6, (0, 5))]);
    }

    #[test]
    fn test_free_iter_intersects_across_multiple_slices() {
        // At t=5 free: [0,2) ∪ [6,10); at t=7 free: [0,6) ∪ [9,10);
        // Intersection on [5,8) -> [0,2) and [9,10).
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 9), si(2, 6))).unwrap(); // key at 5
        b.occupy(&rect(ti(7, 12), si(6, 9))).unwrap(); // key at 7

        let items = collect_free_iter(&b, ti(5, 9), TimeDelta::new(3), len(1), si(0, 10));
        assert_eq!(items, vec![(5, (0, 2)), (5, (9, 10))]);
    }

    #[test]
    fn test_free_iter_filters_runs_shorter_than_required() {
        let b = BO::new(len(4));
        let items = collect_free_iter(&b, ti(0, 10), TimeDelta::new(2), len(3), si(0, 2));
        assert!(items.is_empty());
    }

    #[test]
    fn test_free_iter_empty_when_duration_exceeds_window() {
        let b = BO::new(len(10));
        let items = collect_free_iter(&b, ti(0, 4), TimeDelta::new(5), len(1), si(0, 10));
        assert!(items.is_empty());
    }

    #[test]
    fn test_free_iter_zero_duration_uses_pred_and_may_emit_window_end_if_key_exists() {
        let mut b = BO::new(len(10));
        // keys 0 and 5
        b.occupy(&rect(ti(0, 5), si(0, 1))).unwrap();

        // Duration 0 within [0,5): expect candidate at 0 and also 5 (since key exists at end)
        let items: Vec<_> = FreeSlotIter::new(&b, ti(0, 5), TimeDelta::new(0), len(1), si(0, 10))
            .map(|f| f.start_time().value())
            .collect();
        assert!(items.contains(&0));
        assert!(items.contains(&5));
    }

    #[test]
    fn test_runs_cover_interval_true_when_runs_coalesce_to_cover_target() {
        let runs = vec![si(0, 2), si(2, 5), si(7, 9)]; // [0,5) contiguous via adjacency
        let ok = runs_cover_interval(runs.into_iter(), si(1, 4));
        assert!(ok);
    }

    #[test]
    fn test_runs_cover_interval_false_on_gap() {
        let runs = vec![si(0, 2), si(3, 5)]; // gap at [2,3)
        let ok = runs_cover_interval(runs.into_iter(), si(1, 4));
        assert!(!ok);
    }

    #[test]
    fn test_runs_cover_interval_trivial_true_on_empty_target() {
        let runs = vec![si(1, 2)];
        assert!(runs_cover_interval(runs.into_iter(), si(3, 3)));
    }

    use std::collections::{BTreeMap, BTreeSet};

    fn iv_tuple(iv: SpaceInterval) -> (usize, usize) {
        (iv.start().value(), iv.end().value())
    }
    fn set_from_intervals(v: impl IntoIterator<Item = SpaceInterval>) -> BTreeSet<(usize, usize)> {
        v.into_iter().map(iv_tuple).collect()
    }

    fn collect_bands(
        v: &BO,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> BTreeMap<(T, T), BTreeSet<(usize, usize)>> {
        let mut out: BTreeMap<(T, T), Vec<SpaceInterval>> = BTreeMap::new();
        for r in FeasibleRegionIter::new(v, window, duration, required, bounds) {
            out.entry((
                r.rectangle().time().start().value(),
                r.rectangle().time().end().value(),
            ))
            .or_default()
            .push(r.rectangle().space());
        }
        out.into_iter()
            .map(|(k, v)| (k, set_from_intervals(v)))
            .collect()
    }

    fn slot_set_for_start(
        v: &BO,
        s: TimePoint<T>,
        mut duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> BTreeSet<(usize, usize)> {
        if duration.value() < T::zero() {
            duration = TimeDelta::new(T::zero());
        }
        let tw = TimeInterval::new(s, s + duration);
        FreeSlotIter::new(v, tw, duration, required, bounds)
            .filter(|fs| fs.start_time() == s)
            .map(|fs| iv_tuple(fs.space()))
            .collect()
    }

    fn sample_starts_in_band(a: T, b: T) -> Vec<T> {
        if a >= b {
            return vec![];
        }
        let one = T::one();
        let mut v = vec![a];
        let span = b - a;
        if span > one {
            v.push(a + (span / (one + one))); // approx midpoint
            v.push(b - one);
            v.sort_unstable();
            v.dedup();
        }
        v
    }

    fn assert_regions_match_slots(
        v: &BO,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) {
        let bands = collect_bands(v, window, duration, required, bounds);
        for ((ts, te), spaces) in bands {
            for s in sample_starts_in_band(ts, te) {
                let got = slot_set_for_start(v, TimePoint::new(s), duration, required, bounds);
                assert_eq!(
                    got, spaces,
                    "slots at start={} must equal region runs for band [{}, {})",
                    s, ts, te
                );
            }
        }
    }

    #[test]
    fn test_feasible_regions_vs_slots_free_case() {
        let b = BO::new(len(10));
        assert_regions_match_slots(&b, ti(0, 10), TimeDelta::new(3), len(2), si(0, 10));
    }

    #[test]
    fn test_feasible_regions_vs_slots_with_keys_and_intersections() {
        let mut b = BO::new(len(12));
        b.occupy(&rect(ti(4, 9), si(3, 7))).unwrap(); // key 4
        b.occupy(&rect(ti(7, 11), si(6, 10))).unwrap(); // keys 7,11
        assert_regions_match_slots(&b, ti(4, 11), TimeDelta::new(3), len(1), si(0, 12));
        assert_regions_match_slots(&b, ti(0, 12), TimeDelta::new(2), len(2), si(0, 12));
    }

    #[test]
    fn test_feasible_regions_respects_bounds_and_min_len() {
        let b = BO::new(len(10));
        assert!(collect_bands(&b, ti(0, 10), TimeDelta::new(2), len(6), si(1, 6)).is_empty());
        assert_regions_match_slots(&b, ti(0, 10), TimeDelta::new(2), len(5), si(1, 6));
    }

    #[test]
    fn test_feasible_regions_zero_and_negative_duration() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 6), si(2, 6))).unwrap(); // keys 5,6
        assert_regions_match_slots(&b, ti(0, 6), TimeDelta::new(0), len(2), si(0, 10));
        assert_regions_match_slots(&b, ti(0, 6), TimeDelta::new(-3), len(2), si(0, 10));
    }

    #[test]
    fn test_feasible_regions_empty_when_duration_exceeds_window() {
        let b = BO::new(len(10));
        let bands = collect_bands(&b, ti(0, 4), TimeDelta::new(5), len(1), si(0, 10));
        assert!(bands.is_empty());
    }

    #[test]
    fn test_overlay_runs_iter_base_and_owned_behave_like_underlying_iters() {
        // Base iterator: take(2) over [0,3) runs
        let vec_runs = vec![si(0, 1), si(1, 3)];
        let mut base = OverlayRunsIter::Base(vec_runs.clone().into_iter());
        assert_eq!(base.next(), Some(si(0, 1)));
        assert_eq!(base.next(), Some(si(1, 3)));
        assert_eq!(base.next(), None);

        // Owned iterator
        let mut owned: OverlayRunsIter<std::vec::IntoIter<SpaceInterval>> =
            OverlayRunsIter::Owned(vec_runs.into_iter());
        assert_eq!(owned.next(), Some(si(0, 1)));
        assert_eq!(owned.next(), Some(si(1, 3)));
        assert_eq!(owned.next(), None);
    }
}
