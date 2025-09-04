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

use crate::domain::SpaceTimeRectangle;
use crate::intervalset::IntervalSet;
use crate::quay::{Quay, QuayRead, QuayWrite};
use crate::timeline::Timeline;
use dock_alloc_core::domain::{
    SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use dock_alloc_core::mem::DoubleBuf;
use dock_alloc_model::Problem;
use num_traits::{PrimInt, Signed, Zero};
use std::collections::BTreeMap;
use std::iter::{Copied, Peekable};
use std::marker::PhantomData;
use std::ops::Bound::{Excluded, Unbounded};

pub trait SliceView<T: PrimInt + Signed> {
    fn pred(&self, t: TimePoint<T>) -> Option<TimePoint<T>>;
    fn next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>>;
    fn has_key_at(&self, t: TimePoint<T>) -> bool;
    fn adjusted_free_runs_at(
        &self,
        t: TimePoint<T>,
        bounds: SpaceInterval,
        min_len: SpaceLength,
        scratch_base: &mut SpaceIntervalSet,
        scratch_buf: &mut SpaceIntervalSet,
    ) -> SpaceIntervalSet;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimeSliceRef<'a, T, Q>
where
    T: PrimInt + Signed,
{
    time: TimePoint<T>,
    quay: &'a Q,
}

impl<'a, T, Q> TimeSliceRef<'a, T, Q>
where
    T: PrimInt + Signed,
{
    #[inline]
    pub fn new(time: TimePoint<T>, quay: &'a Q) -> Self {
        Self { time, quay }
    }

    #[inline]
    pub fn time(&self) -> TimePoint<T> {
        self.time
    }

    #[inline]
    pub fn quay(&self) -> &'a Q {
        self.quay
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Slices<'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    berth: &'a BerthOccupancy<T, Q>,
    start: TimePoint<T>,
    end: TimePoint<T>,
}

impl<'a, T, Q> Slices<'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    #[inline]
    pub fn new(berth: &'a BerthOccupancy<T, Q>, start: TimePoint<T>, end: TimePoint<T>) -> Self {
        let s = core::cmp::min(start, end);
        let e = core::cmp::max(start, end);
        Self {
            berth,
            start: s,
            end: e,
        }
    }

    #[inline]
    pub fn interior_keys(self) -> impl DoubleEndedIterator<Item = TimePoint<T>> + 'a {
        let start = self.start;
        let end = self.end;
        let tl = &self.berth.timeline;
        tl.keys((Excluded(start), Excluded(end)))
    }

    #[inline]
    pub fn interior_refs(self) -> impl DoubleEndedIterator<Item = TimeSliceRef<'a, T, Q>> + 'a {
        let start = self.start;
        let end = self.end;
        let tl = &self.berth.timeline;
        tl.entries((Excluded(start), Excluded(end)))
            .map(|(t, q)| TimeSliceRef::new(t, q))
    }

    #[inline]
    pub fn within_keys(self) -> impl DoubleEndedIterator<Item = TimePoint<T>> + 'a {
        let start = self.start;
        let end = self.end;
        let tl = &self.berth.timeline;
        tl.keys(start..end)
    }

    #[inline]
    pub fn within_refs(self) -> impl DoubleEndedIterator<Item = TimeSliceRef<'a, T, Q>> + 'a {
        let start = self.start;
        let end = self.end;
        let tl = &self.berth.timeline;
        tl.entries(start..end).map(|(t, q)| TimeSliceRef::new(t, q))
    }

    #[inline]
    pub fn covering_keys(self) -> impl DoubleEndedIterator<Item = TimePoint<T>> + 'a {
        let start = self.start;
        let end = self.end;
        let tl = &self.berth.timeline;

        let pred = tl.floor(start).map(|(t, _)| t);
        let tail = tl.keys((Excluded(start), Excluded(end)));

        pred.into_iter().chain(tail)
    }

    #[inline]
    pub fn covering_refs(self) -> impl DoubleEndedIterator<Item = TimeSliceRef<'a, T, Q>> + 'a {
        let start = self.start;
        let end = self.end;
        let tl = &self.berth.timeline;

        let pred = tl.floor(start).map(|(t, q)| TimeSliceRef::new(t, q));
        let tail = tl
            .entries((Excluded(start), Excluded(end)))
            .map(|(t, q)| TimeSliceRef::new(t, q));

        pred.into_iter().chain(tail)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BerthOccupancy<T, Q>
where
    T: PrimInt + Signed,
{
    quay_length: SpaceLength,
    timeline: Timeline<TimePoint<T>, Q>,
}

impl<T, Q> BerthOccupancy<T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead + Clone + PartialEq,
{
    #[inline]
    pub fn slices(&self, start: TimePoint<T>, end: TimePoint<T>) -> Slices<'_, T, Q> {
        Slices::new(self, start, end)
    }
}

impl<T, Q> SliceView<T> for BerthOccupancy<T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    fn pred(&self, t: TimePoint<T>) -> Option<TimePoint<T>> {
        self.slice_predecessor_timepoint(t)
    }
    fn next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>> {
        self.next_time_key_after(after)
    }

    fn has_key_at(&self, t: TimePoint<T>) -> bool {
        self.slice_predecessor_timepoint(t)
            .is_some_and(|tp| tp == t)
    }

    fn adjusted_free_runs_at(
        &self,
        t: TimePoint<T>,
        bounds: SpaceInterval,
        min_len: SpaceLength,
        base: &mut SpaceIntervalSet,
        _buf: &mut SpaceIntervalSet,
    ) -> SpaceIntervalSet {
        base.clear_and_fill_from_iter(
            self.snapshot_at(t)
                .expect("slice exists")
                .iter_free_intervals(SpaceLength::new(1), bounds),
        );
        core::mem::take(base).filter_min_length(min_len)
    }
}

impl<T, Q> BerthOccupancy<T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead + Clone + PartialEq,
{
    #[inline]
    pub fn new(quay_length: SpaceLength) -> Self {
        let origin = TimePoint::new(T::zero());
        let q0 = Q::new(quay_length, true);
        Self {
            quay_length,
            timeline: Timeline::new(origin, q0),
        }
    }

    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    #[inline]
    pub fn quay_space_interval(&self) -> SpaceInterval {
        SpaceInterval::new(SpacePosition::new(0), self.quay_end())
    }

    #[inline]
    fn quay_end(&self) -> SpacePosition {
        SpacePosition::new(self.quay_length.value())
    }

    #[inline]
    pub fn time_event_count(&self) -> usize {
        self.timeline.len()
    }

    #[inline]
    pub fn slice_predecessor_timepoint(&self, t: TimePoint<T>) -> Option<TimePoint<T>> {
        self.timeline.prev_key(t)
    }

    #[inline]
    pub fn space_within_quay(&self, si: SpaceInterval) -> bool {
        self.quay_space_interval().contains_interval(&si)
    }

    #[inline]
    pub fn next_time_key_after(&self, t: TimePoint<T>) -> Option<TimePoint<T>> {
        self.timeline.next_key(t)
    }

    #[inline]
    pub fn snapshot_at(&self, t: TimePoint<T>) -> Option<&Q> {
        self.timeline.at(t)
    }

    pub fn is_free(&self, rect: &SpaceTimeRectangle<T>) -> bool {
        if rect.is_empty() {
            return true;
        }
        debug_assert!(self.space_within_quay(rect.space()));
        let ti = rect.time();
        let start_time = ti.start();
        let end_time = ti.end();
        let si = rect.space();
        for s in self.slices(start_time, end_time).covering_refs() {
            if s.quay().check_occupied(si) {
                return false;
            }
        }
        true
    }

    #[inline]
    pub fn is_occupied(&self, rect: &SpaceTimeRectangle<T>) -> bool {
        !self.is_free(rect)
    }

    #[inline]
    pub fn iter_free(
        &self,
        time_window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> impl Iterator<Item = FreeSlot<T>> + '_ {
        FreeIter::new(self, time_window, duration, required_space, space_window)
    }

    pub fn iter_slice_free_runs<'a>(
        &'a self,
        ti: TimeInterval<T>,
        required_space: SpaceLength,
        search_space: SpaceInterval,
    ) -> impl Iterator<Item = (TimePoint<T>, <Q as QuayRead>::FreeIter<'a>)> + 'a {
        debug_assert!(self.space_within_quay(search_space));
        let start_time = ti.start();
        let end_time = ti.end();
        self.slices(start_time, end_time)
            .covering_refs()
            .map(move |s| {
                (
                    s.time(),
                    s.quay().iter_free_intervals(required_space, search_space),
                )
            })
    }
}

impl<T, Q> BerthOccupancy<T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead + QuayWrite + Clone + PartialEq,
{
    fn apply_in<F>(&mut self, rect: &SpaceTimeRectangle<T>, mut f: F)
    where
        F: FnMut(&mut Q, SpaceInterval),
    {
        if rect.is_empty() {
            return;
        }
        let ti = rect.time();
        let si = rect.space();
        debug_assert!(self.space_within_quay(si));
        self.timeline.edit_in(ti.start()..ti.end(), |quay_state| {
            f(quay_state, si);
        });
    }

    #[inline]
    pub fn occupy(&mut self, rect: &SpaceTimeRectangle<T>) {
        if rect.is_empty() {
            return;
        }
        self.apply_in(rect, |q, si| q.occupy(si));
    }

    #[inline]
    pub fn free(&mut self, rect: &SpaceTimeRectangle<T>) {
        if rect.is_empty() {
            return;
        }
        self.apply_in(rect, |q, si| q.free(si));
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FreeSlot<T>
where
    T: PrimInt + Signed,
{
    start_time: TimePoint<T>,
    space: SpaceInterval,
}

impl<T> FreeSlot<T>
where
    T: PrimInt + Signed,
{
    #[inline]
    fn new(space: SpaceInterval, start_time: TimePoint<T>) -> Self {
        Self { start_time, space }
    }

    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }

    #[inline]
    pub fn space(&self) -> SpaceInterval {
        self.space
    }
}

impl<T, C, Q> From<&Problem<T, C>> for BerthOccupancy<T, Q>
where
    T: PrimInt + Signed + Zero + Copy,
    C: PrimInt + Signed + Zero + Copy,
    Q: Quay,
{
    fn from(problem: &Problem<T, C>) -> Self {
        let mut berth_occupancy = BerthOccupancy::<T, Q>::new(problem.quay_length());
        for fixed in problem.preassigned().values() {
            let assignment = fixed.assignment();
            let request = assignment.request();
            let length = request.length();
            let processing_duration = request.processing_duration();
            let start_time = assignment.start_time();
            let end_time = start_time + processing_duration;
            let time_interval = TimeInterval::new(start_time, end_time);
            let start_position = assignment.start_position();
            let end_position = SpacePosition::new(start_position.value() + length.value());
            let space_interval = SpaceInterval::new(start_position, end_position);
            let rect = SpaceTimeRectangle::new(space_interval, time_interval);
            berth_occupancy.occupy(&rect);
        }
        berth_occupancy
    }
}

type SpaceIntervalSet = IntervalSet<SpacePosition>;

#[inline]
fn next_key_after<T: PrimInt + Signed, Q: Clone + QuayRead>(
    berth: &BerthOccupancy<T, Q>,
    overlay_free: &BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    overlay_occ: &BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    after: TimePoint<T>,
) -> Option<TimePoint<T>> {
    let nb = berth.next_time_key_after(after);
    let nf = overlay_free
        .range((Excluded(after), Unbounded))
        .next()
        .map(|(t, _)| *t);
    let no = overlay_occ
        .range((Excluded(after), Unbounded))
        .next()
        .map(|(t, _)| *t);

    match (nb, nf, no) {
        (None, None, None) => None,
        (Some(x), None, None) => Some(x),
        (None, Some(y), None) => Some(y),
        (None, None, Some(z)) => Some(z),
        _ => [nb, nf, no].into_iter().flatten().min(),
    }
}

#[derive(Clone, Debug)]
struct KeysUnion<'a, T: PrimInt + Signed> {
    a: Peekable<Copied<std::collections::btree_map::Keys<'a, TimePoint<T>, SpaceIntervalSet>>>,
    b: Peekable<Copied<std::collections::btree_map::Keys<'a, TimePoint<T>, SpaceIntervalSet>>>,
}

impl<'a, T: PrimInt + Signed> KeysUnion<'a, T> {
    #[inline]
    fn new(
        free: &'a BTreeMap<TimePoint<T>, SpaceIntervalSet>,
        occ: &'a BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    ) -> Self {
        Self {
            a: free.keys().copied().peekable(),
            b: occ.keys().copied().peekable(),
        }
    }
}

impl<'a, T: PrimInt + Signed> Iterator for KeysUnion<'a, T> {
    type Item = TimePoint<T>;
    fn next(&mut self) -> Option<Self::Item> {
        match (self.a.peek().copied(), self.b.peek().copied()) {
            (None, None) => None,
            (Some(x), None) => {
                self.a.next();
                Some(x)
            }
            (None, Some(y)) => {
                self.b.next();
                Some(y)
            }
            (Some(x), Some(y)) => {
                if x < y {
                    self.a.next();
                    Some(x)
                } else if y < x {
                    self.b.next();
                    Some(y)
                } else {
                    self.a.next();
                    self.b.next();
                    Some(x)
                }
            }
        }
    }
}

pub struct IntersectIter<'brand, 'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    overlay: &'a BerthOccupancyOverlay<'brand, 'a, T, Q>,
    required: SpaceLength,
    bounds: SpaceInterval,
    computed: bool,
    emit_idx: usize,
    acc: SpaceIntervalSet,
    tmp: SpaceIntervalSet,
}

impl<'brand, 'a, T, Q> IntersectIter<'brand, 'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    fn new(
        overlay: &'a BerthOccupancyOverlay<'brand, 'a, T, Q>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> Self {
        Self {
            overlay,
            required,
            bounds,
            computed: false,
            emit_idx: 0,
            acc: SpaceIntervalSet::new(),
            tmp: SpaceIntervalSet::new(),
        }
    }

    fn compute(&mut self) {
        if self.computed {
            return;
        }
        self.computed = true;

        // Iterate across overlay keys (free ∪ occupied); this preserves original semantics.
        let keys =
            KeysUnion::<'a, T>::new(&self.overlay.free_by_time, &self.overlay.occupied_by_time);

        let mut first = true;
        let mut saw_any_key = false;

        // Scratch buffers reused across iterations
        let mut base = SpaceIntervalSet::new();
        let mut buf = SpaceIntervalSet::new();

        for tp in keys {
            saw_any_key = true;

            // Adjusted runs at this slice timepoint
            let adj = self.overlay.adjusted_free_runs_at(
                tp,
                self.bounds,
                self.required,
                &mut base,
                &mut buf,
            );

            if first {
                self.acc = adj;
                first = false;
            } else {
                self.tmp.clear();
                self.acc.intersection_into(&adj, &mut self.tmp);
                core::mem::swap(&mut self.acc, &mut self.tmp);
                if self.acc.is_empty() {
                    break;
                }
            }
        }

        // No overlay keys → neutral element: just bounds (then filter by required)
        if !saw_any_key {
            self.acc = SpaceIntervalSet::from_vec(vec![self.bounds]);
        }

        self.acc.retain_min_length(self.required);
    }
}

impl<'brand, 'a, T, Q> Iterator for IntersectIter<'brand, 'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    type Item = SpaceInterval;
    fn next(&mut self) -> Option<Self::Item> {
        self.compute();
        if self.emit_idx >= self.acc.len() {
            return None;
        }
        let iv = self.acc.as_slice()[self.emit_idx];
        self.emit_idx += 1;
        Some(iv)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BerthOccupancyOverlay<'brand, 'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    berth_occupancy: &'a BerthOccupancy<T, Q>,
    free_by_time: BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    occupied_by_time: BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    _brand: PhantomData<&'brand ()>,
}

impl<'b, 'a, T, Q> SliceView<T> for BerthOccupancyOverlay<'b, 'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    fn pred(&self, t: TimePoint<T>) -> Option<TimePoint<T>> {
        self.berth_occupancy.slice_predecessor_timepoint(t)
    }

    fn next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>> {
        next_key_after(
            self.berth_occupancy,
            &self.free_by_time,
            &self.occupied_by_time,
            after,
        )
    }

    fn has_key_at(&self, t: TimePoint<T>) -> bool {
        self.berth_occupancy
            .slice_predecessor_timepoint(t)
            .is_some_and(|tp| tp == t)
            || self.free_by_time.contains_key(&t)
            || self.occupied_by_time.contains_key(&t)
    }

    fn adjusted_free_runs_at(
        &self,
        t: TimePoint<T>,
        bounds: SpaceInterval,
        min_len: SpaceLength,
        base: &mut SpaceIntervalSet,
        buf: &mut SpaceIntervalSet,
    ) -> SpaceIntervalSet {
        BerthOccupancyOverlay::adjusted_free_runs_at(self, t, bounds, min_len, base, buf)
    }
}

impl<'brand, 'a, T, Q> BerthOccupancyOverlay<'brand, 'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    pub fn new(berth_occupancy: &'a BerthOccupancy<T, Q>) -> Self {
        Self {
            berth_occupancy,
            free_by_time: BTreeMap::new(),
            occupied_by_time: BTreeMap::new(),
            _brand: PhantomData,
        }
    }

    #[inline]
    pub fn berth(&self) -> &'a BerthOccupancy<T, Q> {
        self.berth_occupancy
    }

    #[inline]
    pub fn add_occupy(&mut self, time: TimePoint<T>, space: SpaceInterval) {
        if space.start() >= space.end() {
            return;
        }
        self.occupied_by_time
            .entry(time)
            .or_default()
            .insert_and_coalesce(space);
    }

    pub fn occupy(&mut self, rect: &SpaceTimeRectangle<T>) {
        let time_window = rect.time();
        let start_time = time_window.start();
        let end_time = time_window.end();
        let space_interval = rect.space();

        if let Some(predecessor_timepoint) = self
            .berth_occupancy
            .slice_predecessor_timepoint(time_window.start())
        {
            self.add_occupy(predecessor_timepoint, space_interval);
        }
        for timepoint in self
            .berth_occupancy
            .slices(start_time, end_time)
            .interior_keys()
        {
            self.add_occupy(timepoint, space_interval);
        }
    }

    pub fn remove_occupy(&mut self, time: TimePoint<T>, space: SpaceInterval) {
        if space.start() >= space.end() {
            return;
        }
        let mut should_remove_key = false;
        if let Some(set) = self.occupied_by_time.get_mut(&time) {
            let new_set = set.subtract(&SpaceIntervalSet::from_vec(vec![space]));
            should_remove_key = new_set.is_empty();
            *set = new_set;
        }
        if should_remove_key {
            self.occupied_by_time.remove(&time);
        }
    }

    pub fn undo_occupy(&mut self, rect: &SpaceTimeRectangle<T>) {
        let time_window = rect.time();
        let start_time = time_window.start();
        let end_time = time_window.end();
        let space_interval = rect.space();

        if let Some(pred) = self
            .berth_occupancy
            .slice_predecessor_timepoint(time_window.start())
        {
            self.remove_occupy(pred, space_interval);
        }
        for tp in self
            .berth_occupancy
            .slices(start_time, end_time)
            .interior_keys()
        {
            self.remove_occupy(tp, space_interval);
        }
    }

    #[inline]
    pub fn add_free(&mut self, time: TimePoint<T>, space: SpaceInterval) {
        if space.start() >= space.end() {
            return;
        }
        self.free_by_time
            .entry(time)
            .or_default()
            .insert_and_coalesce(space);
    }

    pub fn free(&mut self, rect: &SpaceTimeRectangle<T>) {
        let time_window = rect.time();
        let start_time = time_window.start();
        let end_time = time_window.end();
        let space_interval = rect.space();

        if let Some(predecessor_timepoint) = self
            .berth_occupancy
            .slice_predecessor_timepoint(time_window.start())
        {
            self.add_free(predecessor_timepoint, space_interval);
        }
        for timepoint in self
            .berth_occupancy
            .slices(start_time, end_time)
            .interior_keys()
        {
            self.add_free(timepoint, space_interval);
        }
    }

    pub fn remove_free(&mut self, time: TimePoint<T>, space: SpaceInterval) {
        if space.start() >= space.end() {
            return;
        }

        let mut should_remove_key = false;
        if let Some(set) = self.free_by_time.get_mut(&time) {
            let new_set = set.subtract(&SpaceIntervalSet::from_vec(vec![space]));
            should_remove_key = new_set.is_empty();
            *set = new_set;
        }
        if should_remove_key {
            self.free_by_time.remove(&time);
        }
    }

    pub fn undo_free(&mut self, rect: &SpaceTimeRectangle<T>) {
        let time_window = rect.time();
        let start_time = time_window.start();
        let end_time = time_window.end();
        let space_interval = rect.space();

        if let Some(pred) = self
            .berth_occupancy
            .slice_predecessor_timepoint(time_window.start())
        {
            self.remove_free(pred, space_interval);
        }
        for tp in self
            .berth_occupancy
            .slices(start_time, end_time)
            .interior_keys()
        {
            self.remove_free(tp, space_interval);
        }
    }

    pub fn is_free(&self, rect: &SpaceTimeRectangle<T>) -> bool {
        let time_window = rect.time();

        let space_interval = rect.space();

        self.iter_slice_timepoints_for(time_window).all(|tp| {
            if self.occupied_overlaps_at(tp, space_interval) {
                return false;
            }

            let qs = self
                .berth_occupancy
                .snapshot_at(tp)
                .expect("slice timepoint must exist");

            if qs.check_free(space_interval) {
                return true;
            }

            let base_free = SpaceIntervalSet::from_iter(
                qs.iter_free_intervals(SpaceLength::new(1), space_interval),
            );
            let adj = self.adjust_runs(tp, base_free, space_interval, SpaceLength::new(1));
            adj.covers(space_interval)
        })
    }

    pub fn is_occupied(&self, rect: &SpaceTimeRectangle<T>) -> bool {
        let time_window = rect.time();
        let space_interval = rect.space();

        self.iter_slice_timepoints_for(time_window).any(|tp| {
            if self.occupied_overlaps_at(tp, space_interval) {
                return true;
            }

            let qs = self
                .berth_occupancy
                .snapshot_at(tp)
                .expect("slice timepoint must exist");

            if qs.check_occupied(space_interval) {
                return true;
            }

            let base_free = SpaceIntervalSet::from_iter(
                qs.iter_free_intervals(SpaceLength::new(1), space_interval),
            );
            let adj = self.adjust_runs(tp, base_free, space_interval, SpaceLength::new(1));
            !adj.covers(space_interval)
        })
    }

    #[inline]
    pub fn iter_free_timepoints(&self) -> impl Iterator<Item = TimePoint<T>> + '_ {
        self.free_by_time.keys().copied()
    }

    #[inline]
    pub fn iter_occupied_timepoints(&self) -> impl Iterator<Item = TimePoint<T>> + '_ {
        self.occupied_by_time.keys().copied()
    }

    #[inline]
    pub fn iter_free(
        &'a self,
        time_window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> impl Iterator<Item = FreeSlot<T>> + 'a {
        FreeIter::new(self, time_window, duration, required_space, space_window)
    }

    #[inline]
    pub fn iter_intersect_free_runs(
        &self,
        required_length: SpaceLength,
        search_space: SpaceInterval,
    ) -> IntersectIter<'brand, '_, T, Q> {
        IntersectIter::new(self, required_length, search_space)
    }

    #[inline]
    fn iter_slice_timepoints_for(
        &self,
        time_window: TimeInterval<T>,
    ) -> impl Iterator<Item = TimePoint<T>> + '_ {
        let pred = self
            .berth_occupancy
            .slice_predecessor_timepoint(time_window.start());
        pred.into_iter().chain(
            self.berth_occupancy
                .slices(time_window.start(), time_window.end())
                .interior_keys(),
        )
    }

    #[inline]
    fn occupied_overlaps_at(&self, timepoint: TimePoint<T>, space_interval: SpaceInterval) -> bool {
        self.occupied_by_time
            .get(&timepoint)
            .is_some_and(|set| set.overlaps(space_interval))
    }

    #[inline]
    fn adjust_runs(
        &self,
        timepoint: TimePoint<T>,
        base_set: SpaceIntervalSet,
        bounds: SpaceInterval,
        min_length: SpaceLength,
    ) -> SpaceIntervalSet {
        let mut result_set = base_set;

        if let Some(free_set) = self.free_by_time.get(&timepoint) {
            let clamped_free = free_set.clamped(bounds);
            if !clamped_free.is_empty() {
                result_set = result_set.union(&clamped_free);
            }
        }

        if let Some(occupied_set) = self.occupied_by_time.get(&timepoint) {
            let clamped_occupied = occupied_set.clamped(bounds);
            if !clamped_occupied.is_empty() {
                result_set = result_set.subtract(&clamped_occupied);
            }
        }

        result_set.filter_min_length(min_length)
    }

    #[inline]
    fn adjusted_free_runs_at(
        &self,
        tp: TimePoint<T>,
        bounds: SpaceInterval,
        min_len: SpaceLength,
        scratch_base: &mut SpaceIntervalSet,
        scratch_buf: &mut SpaceIntervalSet,
    ) -> SpaceIntervalSet {
        // Base (quay) free runs inside bounds
        let qs = self.berth_occupancy.snapshot_at(tp).expect("slice exists");
        scratch_base.clear_and_fill_from_iter(qs.iter_free_intervals(SpaceLength::new(1), bounds));

        // + overlay free (union)
        let mut acc = core::mem::take(scratch_base);
        if let Some(free_set) = self.free_by_time.get(&tp) {
            scratch_buf.clear();
            free_set.clamped_into(bounds, scratch_buf);
            acc = acc.union(scratch_buf);
        }

        // - overlay occupied (subtract)
        if let Some(occ_set) = self.occupied_by_time.get(&tp) {
            scratch_buf.clear();
            occ_set.clamped_into(bounds, scratch_buf);
            acc = acc.subtract(scratch_buf);
        }

        acc.filter_min_length(min_len)
    }
}

struct CandidateStarts<'a, V, T>
where
    V: SliceView<T>,
    T: PrimInt + Signed + Copy,
{
    view: &'a V,
    time_window: TimeInterval<T>,
    duration: TimeDelta<T>,
    yielded_start: bool,
    last: Option<TimePoint<T>>,
}

impl<'a, V, T> CandidateStarts<'a, V, T>
where
    V: SliceView<T>,
    T: PrimInt + Signed + Copy,
{
    fn new(view: &'a V, time_window: TimeInterval<T>, duration: TimeDelta<T>) -> Self {
        Self {
            view,
            time_window,
            duration,
            yielded_start: false,
            last: None,
        }
    }
}

impl<'a, V, T> Iterator for CandidateStarts<'a, V, T>
where
    V: SliceView<T>,
    T: PrimInt + Signed + Copy,
{
    type Item = TimePoint<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.time_window.start();
        let end = self.time_window.end();
        if start + self.duration > end {
            return None;
        }

        if !self.yielded_start {
            self.yielded_start = true;
            self.last = Some(start);
            return Some(start);
        }

        let last = self.last?;
        if let Some(tp) = self.view.next_key_after(last) {
            if tp + self.duration <= end {
                self.last = Some(tp);
                return Some(tp);
            }
        }

        if self.duration.value() == T::zero() && last < end && self.view.has_key_at(end) {
            self.last = Some(end);
            return Some(end);
        }

        None
    }
}

/// Generic free-space iterator usable by both base berth and overlay via `SliceView`.
pub struct FreeIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T>,
{
    view: &'a V,
    time_window: TimeInterval<T>,
    duration: TimeDelta<T>,
    required: SpaceLength,
    bounds: SpaceInterval,

    starts: CandidateStarts<'a, V, T>,
    runs: DoubleBuf<SpaceInterval>,
    emit_idx: usize,
    current_start: Option<TimePoint<T>>,
}

impl<'a, T, V> FreeIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T>,
{
    fn new(
        view: &'a V,
        time_window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> Self {
        Self {
            view,
            time_window,
            duration,
            required,
            bounds,
            starts: CandidateStarts::new(view, time_window, duration),
            runs: DoubleBuf::new(),
            emit_idx: 0,
            current_start: None,
        }
    }

    fn build_runs_for_start(&mut self, start: TimePoint<T>) {
        self.runs.clear();
        self.emit_idx = 0;
        self.current_start = None;

        // Early guard: required length exceeds bounds capacity
        let cap = self.bounds.end().value() - self.bounds.start().value();
        if self.required.value() > cap {
            return;
        }

        // Choose seed snapshot: prefer `start` if this view has a key exactly there,
        // otherwise seed from predecessor snapshot.
        let pred = self.view.pred(start).expect("timeline has origin snapshot");
        let seed_tp = if self.view.has_key_at(start) {
            start
        } else {
            pred
        };

        // Scratch sets reused within this build
        let mut scratch_base = SpaceIntervalSet::new();
        let mut scratch_buf = SpaceIntervalSet::new();

        // Seed with adjusted runs at `seed_tp`
        let seed = self.view.adjusted_free_runs_at(
            seed_tp,
            self.bounds,
            self.required,
            &mut scratch_base,
            &mut scratch_buf,
        );
        self.runs.seed_from_iter(seed.as_slice().iter().copied());
        if self.runs.current().is_empty() {
            return;
        }

        // Intersect with adjusted runs at `start`
        let start_set = self.view.adjusted_free_runs_at(
            start,
            self.bounds,
            self.required,
            &mut scratch_base,
            &mut scratch_buf,
        );
        let req = self.required;
        let start_slice = start_set.as_slice();
        self.runs.step(|cur, next| {
            intersect_sorted_min_len(req, cur, start_slice, next);
        });
        if self.runs.current().is_empty() {
            return;
        }

        // Intersect with each subsequent slice key inside (start, start+duration)
        let end = start + self.duration;
        let mut cursor = start;
        while let Some(tp) = self.view.next_key_after(cursor) {
            if tp >= end {
                break;
            }
            cursor = tp;
            if self.runs.current().is_empty() {
                break;
            }

            let adj_tp = self.view.adjusted_free_runs_at(
                tp,
                self.bounds,
                self.required,
                &mut scratch_base,
                &mut scratch_buf,
            );
            let adj_slice = adj_tp.as_slice();
            self.runs.step(|cur, next| {
                intersect_sorted_min_len(req, cur, adj_slice, next);
            });
        }

        if !self.runs.current().is_empty() {
            self.current_start = Some(start);
        }
    }
}

impl<'a, T, V> Iterator for FreeIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T>,
{
    type Item = FreeSlot<T>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(t0) = self.current_start {
                if self.emit_idx < self.runs.current().len() {
                    let iv = self.runs.current()[self.emit_idx];
                    self.emit_idx += 1;
                    return Some(FreeSlot::new(iv, t0));
                }
                self.current_start = None;
            }

            let cand = self.starts.next()?;
            if cand + self.duration > self.time_window.end() {
                return None;
            }
            self.build_runs_for_start(cand);
            if self.current_start.is_none() {
                continue;
            }
        }
    }
}

#[inline]
fn intersect_sorted_min_len(
    required: SpaceLength,
    left: &[SpaceInterval],
    right: &[SpaceInterval],
    out: &mut Vec<SpaceInterval>,
) {
    out.clear();
    let mut i = 0usize;
    let mut j = 0usize;
    while i < left.len() && j < right.len() {
        let a = left[i];
        let b = right[j];

        let start = if a.start().value() >= b.start().value() {
            a.start()
        } else {
            b.start()
        };
        let end = if a.end().value() <= b.end().value() {
            a.end()
        } else {
            b.end()
        };

        if end > start && (end.value() - start.value()) >= required.value() {
            out.push(SpaceInterval::new(start, end));
        }
        if a.end() < b.end() {
            i += 1;
        } else {
            j += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quay::BooleanVecQuay;

    type T = i64;
    type BO = BerthOccupancy<T, BooleanVecQuay>;

    fn pos(x: usize) -> SpacePosition {
        SpacePosition::new(x)
    }

    fn len(x: usize) -> SpaceLength {
        SpaceLength::new(x)
    }

    fn si(a: usize, b: usize) -> SpaceInterval {
        SpaceInterval::new(pos(a), pos(b))
    }

    fn tp(t: T) -> TimePoint<T> {
        TimePoint::new(t)
    }

    fn ti(a: T, b: T) -> TimeInterval<T> {
        TimeInterval::new(tp(a), tp(b))
    }

    fn rect(tw: TimeInterval<T>, si: SpaceInterval) -> SpaceTimeRectangle<T> {
        SpaceTimeRectangle::new(si, tw)
    }

    fn collect_free_iter(
        berth: &BO,
        tw: TimeInterval<T>,
        dur: TimeDelta<T>,
        need: SpaceLength,
        bounds: SpaceInterval,
    ) -> Vec<(T, (usize, usize))> {
        berth
            .iter_free(tw, dur, need, bounds)
            .map(|f| {
                (
                    f.start_time().value(),
                    (f.space().start().value(), f.space().end().value()),
                )
            })
            .collect()
    }

    #[test]
    fn test_initial_state_is_free_single_event() {
        let quay_length = len(10);
        let berth_occupancy = BO::new(quay_length);

        assert_eq!(berth_occupancy.time_event_count(), 1);
        assert!(berth_occupancy.is_free(&rect(ti(0, 100), si(0, 10))));
        assert!(!berth_occupancy.is_occupied(&rect(ti(0, 100), si(0, 10))));
    }

    #[test]
    fn test_occupy_creates_boundaries_and_mutates_exact_span() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 10), si(2, 5)));

        // boundaries at 0 (origin), 5, 10
        assert_eq!(berth_occupancy.time_event_count(), 3);

        // before 5 -> free
        assert!(berth_occupancy.is_free(&rect(ti(0, 5), si(2, 5))));

        // [5,10) occupied in [2,5)
        assert!(berth_occupancy.is_occupied(&rect(ti(5, 10), si(2, 5))));
        assert!(!berth_occupancy.is_free(&rect(ti(5, 10), si(2, 5))));

        // after 10 -> back to free
        assert!(berth_occupancy.is_free(&rect(ti(10, 20), si(2, 5))));
    }

    #[test]
    fn test_free_then_coalesce_back_to_single_event() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 10), si(2, 5)));
        berth_occupancy.free(&rect(ti(5, 10), si(2, 5)));

        // Should merge back to a single fully-free snapshot
        assert_eq!(berth_occupancy.time_event_count(), 1);
        assert!(berth_occupancy.is_free(&rect(ti(0, 100), si(0, 10))));
    }

    #[test]
    fn test_no_mutation_outside_interval() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 10), si(2, 5)));

        // Space outside [2,5) always free
        assert!(berth_occupancy.is_free(&rect(ti(0, 100), si(0, 2))));
        assert!(berth_occupancy.is_free(&rect(ti(0, 100), si(5, 10))));

        // Times outside [5,10) always free within [2,5)
        assert!(berth_occupancy.is_free(&rect(ti(0, 5), si(2, 5))));
        assert!(berth_occupancy.is_free(&rect(ti(10, 20), si(2, 5))));
    }

    #[test]
    fn test_empty_time_interval_and_empty_space_are_noops() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        // Empty time: [3,3)
        berth_occupancy.occupy(&rect(ti(3, 3), si(2, 4)));
        assert_eq!(berth_occupancy.time_event_count(), 1);

        // Empty space: [6,6)
        berth_occupancy.occupy(&rect(ti(0, 5), si(6, 6)));
        assert_eq!(
            berth_occupancy.time_event_count(),
            1,
            "empty space should be a no-op"
        );

        // But no mutation in the snapshot at t=0
        assert!(berth_occupancy.is_free(&rect(ti(0, 5), si(0, 10))));
    }

    #[test]
    fn test_overlapping_occupies_produce_multiple_boundaries() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 12), si(2, 4)));
        berth_occupancy.occupy(&rect(ti(8, 15), si(1, 3)));

        // boundaries: 0,5,8,12,15
        assert_eq!(berth_occupancy.time_event_count(), 5);

        // Check a few windows
        assert!(berth_occupancy.is_occupied(&rect(ti(6, 7), si(2, 4)))); // first occupy
        assert!(berth_occupancy.is_occupied(&rect(ti(9, 11), si(1, 3)))); // overlap of both
        assert!(berth_occupancy.is_free(&rect(ti(12, 15), si(3, 10)))); // free region in space
    }

    #[test]
    fn test_partial_free_does_not_fully_clear() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 10), si(2, 5)));
        berth_occupancy.free(&rect(ti(7, 9), si(3, 4)));

        // [7,9) now has [3,4) free but [2,3) and [4,5) still occupied
        assert!(berth_occupancy.is_occupied(&rect(ti(7, 9), si(2, 3))));
        assert!(berth_occupancy.is_free(&rect(ti(7, 9), si(3, 4))));
        assert!(berth_occupancy.is_occupied(&rect(ti(7, 9), si(4, 5))));
    }

    #[test]
    fn test_query_crossing_boundary_uses_predecessor_and_timepoints() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 10), si(2, 5)));

        // Query [4,6): must consider predecessor of 4 (t=0) and key 5 in (4,6)
        // Since at t=5 it becomes occupied, overall "is_free" must be false.
        assert!(!berth_occupancy.is_free(&rect(ti(4, 6), si(2, 5))));
        assert!(berth_occupancy.is_occupied(&rect(ti(4, 6), si(2, 5))));
    }

    #[test]
    fn test_iter_free_per_slice_reports_per_snapshot_gaps() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        // Occupy [5,10):[2,5)
        berth_occupancy.occupy(&rect(ti(5, 10), si(2, 5)));

        // For search_space [0,10), required >= 2
        let required_length = len(2);
        let search_interval = si(0, 10);

        let mut collected_slices: Vec<(T, Vec<(usize, usize)>)> = Vec::new();
        for (start_time, free_intervals_iterator) in
            berth_occupancy.iter_slice_free_runs(ti(0, 10), required_length, search_interval)
        {
            let mut intervals: Vec<(usize, usize)> = free_intervals_iterator
                .map(|interval| (interval.start().value(), interval.end().value()))
                .collect();
            intervals.sort_unstable();
            collected_slices.push((start_time.value(), intervals));
        }

        collected_slices.sort_by_key(|x| x.0);

        // Expect two slices: at t=0 (before 5) fully free; at t=5 (occupied [2,5))
        assert_eq!(collected_slices.len(), 2);

        // Slice starting at 0: entire [0,10) is free, length 10 >= 2
        assert_eq!(collected_slices[0].0, 0);
        assert_eq!(collected_slices[0].1, vec![(0, 10)]);

        // Slice starting at 5: free intervals are [0,2) and [5,10)
        assert_eq!(collected_slices[1].0, 5);
        assert_eq!(collected_slices[1].1, vec![(0, 2), (5, 10)]);
    }

    #[test]
    fn test_occupy_idempotent_over_same_region() {
        let quay_length = len(16);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(10, 20), si(4, 12)));
        let events_after_first = berth_occupancy.time_event_count();

        berth_occupancy.occupy(&rect(ti(10, 20), si(4, 12)));
        assert_eq!(
            berth_occupancy.time_event_count(),
            events_after_first,
            "idempotent occupy should not add events"
        );

        assert!(berth_occupancy.is_occupied(&rect(ti(10, 20), si(4, 12))));
    }

    #[test]
    fn test_free_idempotent_over_same_region() {
        let quay_length = len(16);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(10, 20), si(4, 12)));
        berth_occupancy.free(&rect(ti(10, 20), si(4, 12)));
        let events_after_first = berth_occupancy.time_event_count();

        berth_occupancy.free(&rect(ti(10, 20), si(4, 12)));
        assert_eq!(
            berth_occupancy.time_event_count(),
            events_after_first,
            "idempotent free should not add events"
        );
        assert!(berth_occupancy.is_free(&rect(ti(0, 100), si(0, 16))));
    }

    #[test]
    fn test_adjacent_updates_keep_half_open_semantics() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        // Occupy [2,5) left, then [5,7) right, on same space
        berth_occupancy.occupy(&rect(ti(2, 5), si(3, 6)));
        berth_occupancy.occupy(&rect(ti(5, 7), si(3, 6)));

        // At t=5 they just touch; the occupancy is continuous across [2,7).
        // With redundancy coalescing, the boundary at 5 is removed.
        assert!(berth_occupancy.is_occupied(&rect(ti(2, 7), si(3, 6))));
        assert_eq!(berth_occupancy.time_event_count(), 3); // keys: 0, 2, 7
    }

    #[test]
    fn test_coalesce_across_border_after_full_revert() {
        let quay_length = len(8);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(3, 6), si(2, 4)));
        // Now revert with two frees that exactly cancel
        berth_occupancy.free(&rect(ti(3, 4), si(2, 4)));
        berth_occupancy.free(&rect(ti(4, 6), si(2, 4)));

        // Should fully coalesce back to one event
        assert_eq!(berth_occupancy.time_event_count(), 1);
        assert!(berth_occupancy.is_free(&rect(ti(0, 10), si(0, 8))));
    }

    #[test]
    fn test_snapshot_at_reads_correct_state() {
        let quay_length = len(6);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(2, 4), si(1, 3)));

        // snapshot before 2: free
        {
            let quay_state = berth_occupancy.snapshot_at(tp(1)).unwrap();
            assert!(quay_state.check_free(si(0, 6)));
        }
        // snapshot at 2..4: occupied 1..3
        {
            let quay_state = berth_occupancy.snapshot_at(tp(2)).unwrap();
            assert!(quay_state.check_occupied(si(1, 3)));
            assert!(quay_state.check_free(si(0, 1)));
            assert!(quay_state.check_free(si(3, 6)));
        }
        // snapshot after 4: free
        {
            let quay_state = berth_occupancy.snapshot_at(tp(5)).unwrap();
            assert!(quay_state.check_free(si(0, 6)));
        }
    }

    #[test]
    fn free_iter_fully_free_single_start() {
        // Fully free berth; one candidate start at tw.start().
        let quay_length = len(8);
        let berth = BO::new(quay_length);

        let items = collect_free_iter(
            &berth,
            ti(0, 10),         // time window
            TimeDelta::new(3), // processing duration
            len(2),            // required length
            si(0, 5),          // search bounds
        );

        assert_eq!(items, vec![(0, (0, 5))]);
    }

    #[test]
    fn free_iter_multiple_candidates_from_timepoints() {
        // Create additional timeline keys at 5 and 6 without affecting the searched bounds.
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(&rect(ti(5, 6), si(9, 10))); // creates keys 5 and 6

        let items = collect_free_iter(
            &berth,
            ti(0, 10),         // time window
            TimeDelta::new(3), // processing duration
            len(2),            // required length
            si(0, 5),          // search bounds (independent of [9,10))
        );

        // Candidate starts at 0 (window start), 5, and 6.
        assert_eq!(items, vec![(0, (0, 5)), (5, (0, 5)), (6, (0, 5))]);
    }

    #[test]
    fn free_iter_intersects_across_multiple_slices() {
        // Make two slice keys inside the processing span so intersection actually happens.
        // At t=5 free space is [0,2) ∪ [6,10); at t=7 free space is [0,6) ∪ [9,10).
        // Intersection across [5,8) => runs [0,2) and [9,10).
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(&rect(ti(5, 9), si(2, 6))); // key at 5
        berth.occupy(&rect(ti(7, 12), si(6, 9))); // key at 7

        let items = collect_free_iter(
            &berth,
            ti(5, 9),          // time window
            TimeDelta::new(3), // processing duration (5..8)
            len(1),            // required length
            si(0, 10),         // search bounds
        );

        assert_eq!(items, vec![(5, (0, 2)), (5, (9, 10))]);
    }

    #[test]
    fn free_iter_filters_runs_shorter_than_required() {
        // Only a short run available inside bounds; require more than its length.
        let quay_length = len(4);
        let berth = BO::new(quay_length);

        // Bounds length = 2, but we require 3 → nothing should be yielded.
        let items = collect_free_iter(
            &berth,
            ti(0, 10),         // time window
            TimeDelta::new(2), // processing duration
            len(3),            // required length (too large for [0,2))
            si(0, 2),          // search bounds
        );

        assert!(items.is_empty());
    }

    #[test]
    fn free_iter_empty_when_duration_exceeds_window() {
        // Guard: if tw.start + duration > tw.end, the iterator is empty.
        let quay_length = len(10);
        let berth = BO::new(quay_length);

        let items = collect_free_iter(
            &berth,
            ti(0, 4),          // time window
            TimeDelta::new(5), // processing duration (too long)
            len(1),            // required length
            si(0, 10),         // search bounds
        );

        assert!(items.is_empty());
    }

    #[test]
    fn free_iter_zero_duration_uses_predecessor_snapshot_each_slice() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        // Occupied at t=5 only in [2,6)
        berth.occupy(&rect(ti(5, 6), si(2, 6)));

        // Keys: 0 (origin), 5, 6
        // With dur=0, we’ll check predecessor snapshot for each candidate start:
        // start=0 → free everywhere; start=5 → [2,6) blocked; start=6 → free everywhere again.
        let items: Vec<_> = berth
            .iter_free(ti(0, 6), TimeDelta::new(0), len(2), si(0, 10))
            .map(|f| {
                (
                    f.start_time().value(),
                    (f.space().start().value(), f.space().end().value()),
                )
            })
            .collect();

        // Expect runs at t=0 and t=6, none at t=5 for [2,6).
        assert!(items.contains(&(0, (0, 10))));
        assert!(items.contains(&(6, (0, 10))));
        // There should be no (5, (2,6)) entry; depending on your MockQuay’s splitting,
        // you may see (5, (0,2)) and (5, (6,10)) only.
        assert!(
            !items
                .iter()
                .any(|(time, span)| *time == 5 && *span == (2, 6))
        );
    }

    #[test]
    fn overlay_add_free_and_occupy_and_queries() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        // Base: occupy [5,10):[2,6)
        berth.occupy(&rect(ti(5, 10), si(2, 6)));

        let mut overlay = BerthOccupancyOverlay::new(&berth);

        // At t=5, override a subrange as free via overlay
        overlay.add_free(tp(5), si(2, 4));
        assert!(overlay.is_free(&rect(ti(5, 10), si(2, 4))));
        assert!(overlay.is_occupied(&rect(ti(5, 10), si(4, 6)))); // still blocked remainder

        // Add an overlay-occupy on otherwise-free area at t=0
        overlay.add_occupy(tp(0), si(0, 1));
        assert!(overlay.is_occupied(&rect(ti(0, 5), si(0, 1))));
        assert!(overlay.is_free(&rect(ti(0, 5), si(1, 10))));
    }

    #[test]
    fn overlay_free_and_undo_across_timepoints() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        // Create a base boundary at t=5 by occupying [2,6)
        berth.occupy(&rect(ti(5, 7), si(2, 6)));

        let mut overlay = BerthOccupancyOverlay::new(&berth);

        // Free [4,5) across [4,6): will place free at predecessor of 4 (t=0) and at timepoint 5
        overlay.free(&rect(ti(4, 6), si(4, 5)));
        assert!(overlay.is_free(&rect(ti(4, 6), si(4, 5))));

        // Undo the same free; should revert to base (occupied at t=5 in [2,6))
        overlay.undo_free(&rect(ti(4, 6), si(4, 5)));
        assert!(overlay.is_occupied(&rect(ti(5, 6), si(4, 5))));
    }

    #[test]
    fn snapshot_at_none_before_origin() {
        let berth = BO::new(len(10));
        // Using negative timepoint to test before origin
        assert!(berth.snapshot_at(tp(-1)).is_none());
    }

    #[test]
    fn slice_predecessor_equal_at_key() {
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(5, 7), si(2, 3))); // keys: 0,5,7
        assert_eq!(berth.slice_predecessor_timepoint(tp(5)), Some(tp(5)));
        assert_eq!(berth.slice_predecessor_timepoint(tp(6)), Some(tp(5)));
        assert_eq!(berth.slice_predecessor_timepoint(tp(7)), Some(tp(7)));
    }

    #[test]
    fn iter_timepoints_is_strictly_inside_half_open() {
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(5, 10), si(0, 1))); // keys 0,5,10
        let v: Vec<_> = berth
            .slices(5.into(), 10.into())
            .interior_keys()
            .map(|t| t.value())
            .collect();
        assert_eq!(v, Vec::<i64>::new());
    }

    #[test]
    fn space_within_quay_edges_and_outside() {
        let berth = BO::new(len(8));
        assert!(berth.space_within_quay(si(0, 8)));
        assert!(berth.space_within_quay(si(3, 5)));
        assert!(!berth.space_within_quay(si(7, 9)));
    }

    #[test]
    fn occupy_free_coalesce_chain_three_equal_states() {
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(3, 7), si(1, 2))); // 0,3,7
        berth.free(&rect(ti(3, 7), si(1, 2))); // should coalesce back to 0 only
        assert_eq!(berth.time_event_count(), 1);
    }

    #[test]
    fn overlay_remove_occupy_undo_occupy() {
        let quay_length = len(10);
        let berth = BO::new(quay_length);
        let mut overlay = BerthOccupancyOverlay::new(&berth);

        overlay.occupy(&rect(ti(2, 6), si(3, 5)));
        assert!(overlay.is_occupied(&rect(ti(3, 5), si(3, 5))));

        overlay.undo_occupy(&rect(ti(2, 6), si(3, 5)));
        assert!(overlay.is_free(&rect(ti(0, 10), si(0, 10))));
    }

    #[test]
    fn overlay_iter_intersect_free_runs_across_overlay_keys() {
        // Base berth: fully free
        let berth = BO::new(len(12));
        let mut overlay = BerthOccupancyOverlay::new(&berth);

        // Overlay "free" is additive (union with base free). Since base is fully free,
        // the intersection across keys stays the full bounds.
        overlay.add_free(tp(0), si(1, 8));
        overlay.add_free(tp(5), si(3, 10));

        let runs: Vec<_> = overlay
            .iter_intersect_free_runs(len(1), si(0, 12))
            .map(|iv| (iv.start().value(), iv.end().value()))
            .collect();

        // Expect the entire bounds because base is already free everywhere.
        assert_eq!(runs, vec![(0, 12)]);
    }

    #[test]
    fn overlay_iter_free_respects_overlay_through_duration() {
        // Base: occupy [5,9):[2,6). We'll "free" that space via overlay for the slices we care about.
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(5, 9), si(2, 6)));

        let mut overlay = BerthOccupancyOverlay::new(&berth);

        // We need overlay freeness at the predecessor of 5 (which is 5 itself here) AND at slice key 5,
        // so that the intersection over [5,8) includes [2,6).
        overlay.add_free(tp(0), si(2, 6));
        overlay.add_free(tp(5), si(2, 6));

        let items: Vec<_> = overlay
            .iter_free(ti(5, 9), TimeDelta::new(3), len(2), si(0, 10))
            .map(|f| {
                (
                    f.start_time().value(),
                    (f.space().start().value(), f.space().end().value()),
                )
            })
            .collect();

        // At start=5 there should be some free interval that *covers* [2,6) (it may be larger, e.g. [0,10))
        assert!(
            items
                .iter()
                .any(|(t, (s, e))| *t == 5 && *s <= 2 && *e >= 6),
            "Expected an interval at t=5 that covers [2,6), got: {:?}",
            items
        );
    }

    #[test]
    fn overlay_timepoint_iters_sorted() {
        let berth = BO::new(len(6));
        let mut overlay = BerthOccupancyOverlay::new(&berth);

        overlay.add_free(tp(10), si(0, 1));
        overlay.add_free(tp(0), si(0, 1));
        overlay.add_free(tp(5), si(0, 1));

        overlay.add_occupy(tp(7), si(1, 2));
        overlay.add_occupy(tp(3), si(1, 2));

        let free_keys: Vec<_> = overlay.iter_free_timepoints().map(|t| t.value()).collect();
        let occ_keys: Vec<_> = overlay
            .iter_occupied_timepoints()
            .map(|t| t.value())
            .collect();

        assert_eq!(free_keys, vec![0, 5, 10]);
        assert_eq!(occ_keys, vec![3, 7]);
    }

    #[test]
    fn intersect_iter_min_length_filtering() {
        // Base: fully free; create a *narrow* intersection via overlay OCCUPY (subtractive).
        let berth = BO::new(len(10));
        let mut overlay = BerthOccupancyOverlay::new(&berth);

        // t=0: occupy [2,10) → free is [0,2)
        overlay.add_occupy(tp(0), si(2, 10));
        // t=5: occupy [0,1) and [2,10) → free is [1,2)
        overlay.add_occupy(tp(5), si(0, 1));
        overlay.add_occupy(tp(5), si(2, 10));

        let bounds = si(0, 10);

        // Requiring length 2 should filter out [1,2)
        let none: Vec<_> = overlay.iter_intersect_free_runs(len(2), bounds).collect();
        assert!(none.is_empty());

        // Requiring length 1 should produce [1,2)
        let some: Vec<_> = overlay
            .iter_intersect_free_runs(len(1), bounds)
            .map(|iv| (iv.start().value(), iv.end().value()))
            .collect();
        assert_eq!(some, vec![(1, 2)]);
    }

    #[test]
    fn free_iter_zero_duration_yields_window_end_only_if_key_exists() {
        let mut berth = BO::new(len(10));
        // Ensure a key at end
        berth.occupy(&rect(ti(0, 5), si(0, 1))); // keys 0,5
        let items: Vec<_> = berth
            .iter_free(ti(0, 5), TimeDelta::new(0), len(1), si(0, 10))
            .map(|f| {
                (
                    f.start_time().value(),
                    (f.space().start().value(), f.space().end().value()),
                )
            })
            .collect();
        // both start=0 and end=5 should appear (end because a key exists at 5)
        assert!(items.iter().any(|(t, _)| *t == 0));
        assert!(items.iter().any(|(t, _)| *t == 5));
    }

    #[test]
    fn overlay_remove_occupy_drops_key_when_empty() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);
        ov.add_occupy(tp(5), si(2, 4));
        assert_eq!(
            ov.iter_occupied_timepoints().collect::<Vec<_>>(),
            vec![tp(5)]
        );
        ov.remove_occupy(tp(5), si(2, 4));
        assert!(ov.iter_occupied_timepoints().next().is_none());
    }

    #[test]
    fn overlay_remove_free_drops_key_when_empty() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);
        ov.add_free(tp(5), si(1, 3));
        assert_eq!(ov.iter_free_timepoints().collect::<Vec<_>>(), vec![tp(5)]);
        ov.remove_free(tp(5), si(1, 3));
        assert!(ov.iter_free_timepoints().next().is_none());
    }

    #[test]
    fn overlay_iter_free_uses_overlay_keys_as_candidates() {
        let berth = BO::new(len(10)); // fully free; no extra keys
        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Introduce an overlay key inside the window
        ov.add_occupy(tp(7), si(0, 1));
        // Duration 2 forces candidate starts at 0 and 7 (overlay key)
        let items: Vec<_> = ov
            .iter_free(ti(0, 10), TimeDelta::new(2), len(1), si(0, 10))
            .map(|f| f.start_time().value())
            .collect();
        assert!(items.contains(&0));
        assert!(items.contains(&7));
    }

    #[test]
    fn overlay_intersect_runs_no_overlay_keys_returns_bounds() {
        let berth = BO::new(len(10)); // fully free
        let ov = BerthOccupancyOverlay::new(&berth);
        let runs: Vec<_> = ov
            .iter_intersect_free_runs(len(1), si(2, 8))
            .map(|iv| (iv.start().value(), iv.end().value()))
            .collect();
        assert_eq!(runs, vec![(2, 8)]);
    }

    #[test]
    fn overlay_changes_at_start_are_applied_when_pred_differs() {
        type BO = BerthOccupancy<i64, BooleanVecQuay>;
        let mut berth = BO::new(SpaceLength::new(10)); // fully free
        berth.occupy(&rect(
            TimeInterval::new(TimePoint::new(7), TimePoint::new(9)),
            SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(6)),
        ));
        // keys now: 0,7,9

        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Make [2,6) occupied by default via overlay at pred=0, but free exactly at start=5
        ov.add_occupy(
            TimePoint::new(0),
            SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(6)),
        );
        ov.add_free(
            TimePoint::new(5),
            SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(6)),
        );

        let items: Vec<_> = ov
            .iter_free(
                TimeInterval::new(TimePoint::new(5), TimePoint::new(8)),
                TimeDelta::new(2),
                SpaceLength::new(3),
                SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10)),
            )
            .collect();

        assert!(
            items.iter().any(|f| f.start_time().value() == 5
                && f.space().start().value() <= 2
                && f.space().end().value() >= 6),
            "Expected overlay free at `start` to apply to the initial slice"
        );
    }
}
