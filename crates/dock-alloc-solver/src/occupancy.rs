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
use std::iter::{Copied, FusedIterator, Peekable};
use std::marker::PhantomData;
use std::ops::Bound::{Excluded, Unbounded};

/// A trait providing a view into a timeline of spatial availability.
///
/// This abstracts over `BerthOccupancy` and `BerthOccupancyOverlay`, allowing
/// generic algorithms like `FreeIter` to query for available space over time.
pub trait SliceView<T: PrimInt + Signed> {
    /// The specific iterator type returned by `free_runs_at`.
    type FreeRunsIter<'s>: Iterator<Item = SpaceInterval> + 's
    where
        Self: 's;

    /// Finds the timepoint of the slice active at `t` (inclusive).
    fn pred(&self, t: TimePoint<T>) -> Option<TimePoint<T>>;

    /// Finds the first key strictly after a given timepoint.
    fn next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>>;

    /// Checks if a key exists at the exact timepoint `t`.
    fn has_key_at(&self, t: TimePoint<T>) -> bool;

    /// Returns an iterator over all free space intervals at a given timepoint `t`.
    /// The caller is responsible for filtering these runs by required length and bounds.
    fn free_runs_at(&self, t: TimePoint<T>) -> Self::FreeRunsIter<'_>;
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

/// A factory for creating iterators over a specific time range of a `BerthOccupancy`.
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

/// Represents the spatio-temporal occupancy of a quay over time.
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
    type FreeRunsIter<'s>
        = <Q as QuayRead>::FreeIter<'s>
    where
        Self: 's;

    #[inline]
    fn pred(&self, t: TimePoint<T>) -> Option<TimePoint<T>> {
        self.slice_predecessor_timepoint(t)
    }

    #[inline]
    fn next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>> {
        self.next_time_key_after(after)
    }

    #[inline]
    fn has_key_at(&self, t: TimePoint<T>) -> bool {
        self.slice_predecessor_timepoint(t)
            .is_some_and(|tp| tp == t)
    }

    #[inline]
    fn free_runs_at(&self, t: TimePoint<T>) -> Self::FreeRunsIter<'_> {
        let bounds = self.quay_space_interval();
        self.snapshot_at(t)
            .expect("slice exists")
            .iter_free_intervals(SpaceLength::new(1), bounds)
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
    [nb, nf, no].into_iter().flatten().min()
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
        let peek_a = self.a.peek().copied();
        let peek_b = self.b.peek().copied();

        match (peek_a, peek_b) {
            (None, None) => None,
            (Some(_), None) => self.a.next(),
            (None, Some(_)) => self.b.next(),
            (Some(x), Some(y)) => match x.cmp(&y) {
                std::cmp::Ordering::Less => self.a.next(),
                std::cmp::Ordering::Greater => self.b.next(),
                std::cmp::Ordering::Equal => {
                    self.a.next();
                    self.b.next();
                    Some(x)
                }
            },
        }
    }
}

/// An iterator that computes the intersection of all free space runs across
/// every time slice defined by an overlay.
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

        let keys =
            KeysUnion::<'a, T>::new(&self.overlay.free_by_time, &self.overlay.occupied_by_time);
        let mut acc_opt: Option<SpaceIntervalSet> = None;
        let mut current_runs = SpaceIntervalSet::new();

        for tp in keys {
            current_runs.clear_and_fill_from_iter(
                self.overlay
                    .free_runs_at(tp)
                    .filter(|iv| self.bounds.intersects(iv))
                    .map(|iv| self.bounds.intersection(&iv).unwrap())
                    .filter(|iv| iv.length() >= self.required),
            );

            match acc_opt.as_mut() {
                None => {
                    acc_opt = Some(core::mem::take(&mut current_runs));
                }
                Some(acc) => {
                    self.tmp.clear();
                    acc.intersection_into(&current_runs, &mut self.tmp);
                    core::mem::swap(acc, &mut self.tmp);
                    if acc.is_empty() {
                        break;
                    }
                }
            }
        }

        self.acc = acc_opt.unwrap_or_else(|| SpaceIntervalSet::from_vec(vec![self.bounds]));
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

/// A view that combines a base `BerthOccupancy` with temporary changes.
/// This allows for hypothetical queries ("what if I place a ship here?")
/// without modifying the underlying base timeline.
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

impl<'brand, 'a, T, Q> SliceView<T> for BerthOccupancyOverlay<'brand, 'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    type FreeRunsIter<'s>
        = OverlayRunsIter<<Q as QuayRead>::FreeIter<'s>>
    where
        Self: 's;

    #[inline]
    fn pred(&self, t: TimePoint<T>) -> Option<TimePoint<T>> {
        self.berth_occupancy.slice_predecessor_timepoint(t)
    }

    #[inline]
    fn next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>> {
        next_key_after(
            self.berth_occupancy,
            &self.free_by_time,
            &self.occupied_by_time,
            after,
        )
    }

    #[inline]
    fn has_key_at(&self, t: TimePoint<T>) -> bool {
        self.free_by_time.contains_key(&t)
            || self.occupied_by_time.contains_key(&t)
            || self.berth_occupancy.has_key_at(t)
    }

    #[inline]
    fn free_runs_at(&self, t: TimePoint<T>) -> Self::FreeRunsIter<'_> {
        let f = self.free_by_time.get(&t);
        let o = self.occupied_by_time.get(&t);
        if f.is_none() && o.is_none() {
            return OverlayRunsIter::Base(self.berth_occupancy.free_runs_at(t));
        }

        let base_iter = self.berth_occupancy.free_runs_at(t);
        let (base_lo, base_hi) = base_iter.size_hint();
        let base_cap = base_hi.unwrap_or(base_lo);

        let f_len = f.map(|s| s.len()).unwrap_or(0);
        let o_len = o.map(|s| s.len()).unwrap_or(0);

        let mut a = SpaceIntervalSet::with_capacity(base_cap);
        a.clear_and_fill_from_iter(base_iter);
        let mut b = SpaceIntervalSet::with_capacity(a.len().saturating_add(f_len.max(o_len)));

        if let Some(fset) = f {
            a.union_into(fset, &mut b);
            core::mem::swap(&mut a, &mut b);
        }

        if let Some(oset) = o {
            a.subtract_into(oset, &mut b);
            core::mem::swap(&mut a, &mut b);
        }

        OverlayRunsIter::Owned(a.into_intervals().into_iter())
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
        if space.is_empty() {
            return;
        }
        debug_assert!(self.berth().space_within_quay(space));
        self.occupied_by_time
            .entry(time)
            .or_default()
            .insert_and_coalesce(space);
    }

    pub fn occupy(&mut self, rect: &SpaceTimeRectangle<T>) {
        let time_window = rect.time();
        let space_interval = rect.space();

        if let Some(pred) = self
            .berth()
            .slice_predecessor_timepoint(time_window.start())
        {
            self.add_occupy(pred, space_interval);
        }
        for timepoint in self
            .berth()
            .slices(time_window.start(), time_window.end())
            .interior_keys()
        {
            self.add_occupy(timepoint, space_interval);
        }
    }

    pub fn remove_occupy(&mut self, time: TimePoint<T>, space: SpaceInterval) {
        if space.is_empty() {
            return;
        }
        if let Some(set) = self.occupied_by_time.get_mut(&time) {
            set.subtract_interval(space);
            if set.is_empty() {
                self.occupied_by_time.remove(&time);
            }
        }
    }

    pub fn undo_occupy(&mut self, rect: &SpaceTimeRectangle<T>) {
        let time_window = rect.time();
        let space_interval = rect.space();

        if let Some(pred) = self
            .berth()
            .slice_predecessor_timepoint(time_window.start())
        {
            self.remove_occupy(pred, space_interval);
        }
        for tp in self
            .berth()
            .slices(time_window.start(), time_window.end())
            .interior_keys()
        {
            self.remove_occupy(tp, space_interval);
        }
    }

    #[inline]
    pub fn add_free(&mut self, time: TimePoint<T>, space: SpaceInterval) {
        if space.is_empty() {
            return;
        }
        debug_assert!(self.berth().space_within_quay(space));
        self.free_by_time
            .entry(time)
            .or_default()
            .insert_and_coalesce(space);
    }

    pub fn free(&mut self, rect: &SpaceTimeRectangle<T>) {
        let time_window = rect.time();
        let space_interval = rect.space();

        if let Some(pred) = self
            .berth()
            .slice_predecessor_timepoint(time_window.start())
        {
            self.add_free(pred, space_interval);
        }
        for timepoint in self
            .berth()
            .slices(time_window.start(), time_window.end())
            .interior_keys()
        {
            self.add_free(timepoint, space_interval);
        }
    }

    pub fn remove_free(&mut self, time: TimePoint<T>, space: SpaceInterval) {
        if space.is_empty() {
            return;
        }
        if let Some(set) = self.free_by_time.get_mut(&time) {
            set.subtract_interval(space);
            if set.is_empty() {
                self.free_by_time.remove(&time);
            }
        }
    }

    pub fn undo_free(&mut self, rect: &SpaceTimeRectangle<T>) {
        let time_window = rect.time();
        let space_interval = rect.space();

        if let Some(pred) = self
            .berth()
            .slice_predecessor_timepoint(time_window.start())
        {
            self.remove_free(pred, space_interval);
        }
        for tp in self
            .berth()
            .slices(time_window.start(), time_window.end())
            .interior_keys()
        {
            self.remove_free(tp, space_interval);
        }
    }

    fn covering_timepoints_union(
        &self,
        tw: TimeInterval<T>,
    ) -> impl Iterator<Item = TimePoint<T>> + '_ {
        let start = tw.start();
        let end = tw.end();

        let base_pred = self.berth().slice_predecessor_timepoint(start);
        let base_interior = self.berth().slices(start, end).interior_keys();

        let overlay_start = (self.free_by_time.contains_key(&start)
            || self.occupied_by_time.contains_key(&start))
        .then_some(start);

        let overlay_union = KeysUnion::new(&self.free_by_time, &self.occupied_by_time)
            .filter(move |&t| t > start && t < end);

        overlay_start
            .into_iter()
            .chain(base_pred)
            .chain(base_interior)
            .chain(overlay_union)
    }

    pub fn is_free(&self, rect: &SpaceTimeRectangle<T>) -> bool {
        let tw = rect.time();
        let si = rect.space();
        self.covering_timepoints_union(tw)
            .all(|tp| runs_cover_interval(self.free_runs_at(tp), si))
    }

    pub fn is_occupied(&self, rect: &SpaceTimeRectangle<T>) -> bool {
        !self.is_free(rect)
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
}

/// Generic iterator over free spatio-temporal slots.
///
/// This iterator is driven by a `SliceView` trait object, allowing it to operate
/// on either a base `BerthOccupancy` or a temporary `BerthOccupancyOverlay`.
/// It works by finding candidate start times and, for each, intersecting the
/// free space available across all relevant time slices over the required duration.
pub struct FreeIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    view: &'a V,
    time_window: TimeInterval<T>,
    duration: TimeDelta<T>,
    required: SpaceLength,
    bounds: SpaceInterval,
    last_candidate: Option<TimePoint<T>>,
    yielded_window_start: bool,
    current_start: Option<TimePoint<T>>,
    runs: DoubleBuf<SpaceInterval>,
    emit_idx: usize,
    is_empty: bool,
}

impl<'a, T, V> FreeIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    #[inline]
    pub fn new(
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
            last_candidate: None,
            yielded_window_start: false,
            current_start: None,
            runs: DoubleBuf::new(),
            emit_idx: 0,
            is_empty: required > bounds.length(),
        }
    }

    /// Finds the next valid timepoint that could begin a free slot.
    /// Candidates are the start of the window and any timepoint key within it.
    fn next_candidate_start(&mut self) -> Option<TimePoint<T>> {
        let start = self.time_window.start();
        let end = self.time_window.end();

        if start + self.duration > end {
            return None;
        }

        if !self.yielded_window_start {
            self.yielded_window_start = true;
            self.last_candidate = Some(start);
            return Some(start);
        }

        let last = self.last_candidate?;
        if let Some(tp) = self.view.next_key_after(last) {
            if tp + self.duration <= end {
                self.last_candidate = Some(tp);
                return Some(tp);
            }
        }

        // For zero-duration requests, also check the very end of the window if it's a key.
        if self.duration.is_zero() && last < end && self.view.has_key_at(end) {
            self.last_candidate = Some(end);
            return Some(end);
        }
        None
    }

    /// For a given start time, computes the intersection of all free runs
    /// over the interval `[start, start + duration)`.
    fn build_runs_for_start(&mut self, start: TimePoint<T>) {
        self.runs.clear();
        self.emit_idx = 0;
        self.current_start = None;

        let pred = match self.view.pred(start) {
            Some(p) => p,
            None => return,
        };
        let seed_tp = if self.view.has_key_at(start) {
            start
        } else {
            pred
        };
        let seed = runs_at(self.view, seed_tp, self.bounds, self.required);
        self.runs.seed_from_iter(seed);
        if seed_tp != start {
            let right = runs_at(self.view, start, self.bounds, self.required);
            let req = self.required;
            self.runs.step(|cur, next| {
                next.extend(IntersectRuns::new(cur.iter().copied(), right, req));
            });
        }

        if self.runs.current().is_empty() {
            return;
        }

        let end = start + self.duration;
        let mut cursor = start;
        while let Some(tp) = self.view.next_key_after(cursor) {
            if tp >= end {
                break;
            }
            cursor = tp;

            let right = runs_at(self.view, tp, self.bounds, self.required);
            let req = self.required;
            self.runs.step(|cur, next| {
                next.extend(IntersectRuns::new(cur.iter().copied(), right, req));
            });

            if self.runs.current().is_empty() {
                return;
            }
        }

        self.current_start = Some(start);
    }
}

impl<'a, T, V> Iterator for FreeIter<'a, T, V>
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
            if let Some(t0) = self.current_start {
                if self.emit_idx < self.runs.current().len() {
                    let iv = self.runs.current()[self.emit_idx];
                    self.emit_idx += 1;
                    return Some(FreeSlot::new(iv, t0));
                }
                self.current_start = None;
            }
            let cand = self.next_candidate_start()?;
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
fn runs_cover_interval<I>(runs: I, target: SpaceInterval) -> bool
where
    I: Iterator<Item = SpaceInterval>,
{
    if target.is_empty() {
        return true;
    }

    let mut runs = runs.peekable();
    let mut need_start = target.start();
    let need_end = target.end();

    while let Some(iv) = runs.next() {
        // Skip any runs that end before our current needed start
        if iv.end() <= need_start {
            continue;
        }

        // If there's a gap before the needed start, not covered
        if iv.start() > need_start {
            return false;
        }

        // iv.start <= need_start < iv.end ; extend coverage as far as possible
        let mut covered_end = iv.end();

        // Coalesce adjacency/overlap from subsequent runs without allocating
        while let Some(next) = runs.peek().copied() {
            // half-open semantics: touching is continuous if next.start() <= covered_end
            if next.start() > covered_end {
                break;
            }
            if next.end() > covered_end {
                covered_end = next.end();
            }
            runs.next(); // consume it
        }

        if covered_end >= need_end {
            return true;
        }

        // Continue needing coverage starting at the end of what we just covered
        need_start = covered_end;
    }

    false
}

#[inline]
fn runs_at<'v, T, V>(
    view: &'v V,
    t: TimePoint<T>,
    bounds: SpaceInterval,
    min_len: SpaceLength,
) -> impl Iterator<Item = SpaceInterval> + 'v
where
    T: PrimInt + Signed,
    V: SliceView<T> + ?Sized + 'v,
{
    view.free_runs_at(t)
        .filter_map(move |iv| bounds.intersection(&iv))
        .filter(move |iv| iv.length() >= min_len)
}

struct IntersectRuns<L, R>
where
    R: Iterator,
{
    left: L,
    right: std::iter::Peekable<R>,
    cur_l: Option<SpaceInterval>,
    cur_r: Option<SpaceInterval>,
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
            cur_l: None,
            cur_r: None,
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
            if self.cur_l.is_none() {
                self.cur_l = self.left.next();
            }
            if self.cur_r.is_none() {
                self.cur_r = self.right.next();
            }
            let (a, b) = match (self.cur_l, self.cur_r) {
                (Some(a), Some(b)) => (a, b),
                _ => return None,
            };

            // Compute intersection (half-open semantics assumed by your types).
            let out = a.intersection(&b);
            // Advance the side that ends first; on tie advance right (matches your slice version).
            if a.end() < b.end() {
                self.cur_l = None;
            } else {
                self.cur_r = None;
            }

            if let Some(iv) = out {
                if iv.length() >= self.required {
                    return Some(iv);
                }
            }
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
        // There should be no (5, (2,6)) entry; you will see (5, (0,2)) and (5, (6,10)) only.
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

        // We need overlay freeness at the predecessor of 5 (which is 0) AND at slice key 5,
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

        // At start=5 there should be some free interval that *covers* [2,6)
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
        let mut unique_items: Vec<_> = items;
        unique_items.sort();
        unique_items.dedup();

        assert!(unique_items.contains(&0));
        assert!(unique_items.contains(&7));
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

    #[test]
    fn runs_cover_interval_handles_touching() {
        let runs = vec![si(0, 5), si(5, 8)].into_iter();
        assert!(runs_cover_interval(runs, si(0, 8)));
    }
}
