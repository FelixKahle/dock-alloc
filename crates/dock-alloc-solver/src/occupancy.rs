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
use crate::quay::{Quay, QuayRead, QuaySpaceIntervalOutOfBoundsError, QuayWrite};
use crate::timeline::Timeline;
use dock_alloc_core::domain::{
    SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use dock_alloc_core::mem::DoubleBuf;
use dock_alloc_model::Problem;
use num_traits::{One, PrimInt, Signed, Zero};
use std::collections::BTreeMap;
use std::iter::{Copied, FusedIterator, Peekable};
use std::marker::PhantomData;
use std::ops::Bound::{Excluded, Unbounded};

pub trait SliceView<T: PrimInt + Signed> {
    type FreeRunsIter<'s>: Iterator<Item = SpaceInterval> + 's
    where
        Self: 's;

    fn pred(&self, t: TimePoint<T>) -> Option<TimePoint<T>>;
    fn next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>>;
    fn has_key_at(&self, t: TimePoint<T>) -> bool;
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

    #[inline]
    pub fn is_free(
        &self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        if rect.is_empty() {
            return Ok(true);
        }

        let ti = rect.time();
        let start_time = ti.start();
        let end_time = ti.end();
        let si = rect.space();
        for s in self.slices(start_time, end_time).covering_refs() {
            if s.quay().check_occupied(si)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    #[inline]
    pub fn is_occupied(
        &self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        Ok(!self.is_free(rect)?)
    }

    #[inline]
    pub fn iter_free_slots(
        &self,
        time_window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> impl Iterator<Item = FreeSlot<T>> + '_ {
        FreeSlotIter::new(self, time_window, duration, required_space, space_window)
    }

    #[inline]
    pub fn iter_free_regions(
        &self,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> impl Iterator<Item = SpaceTimeRectangle<T>> + '_ {
        FeasibleRegionIter::new(self, window, duration, required_space, space_window)
    }
}

impl<T, Q> BerthOccupancy<T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead + QuayWrite + Clone + PartialEq,
{
    fn apply_in<F>(
        &mut self,
        rect: &SpaceTimeRectangle<T>,
        mut f: F,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError>
    where
        F: FnMut(&mut Q, SpaceInterval) -> Result<(), QuaySpaceIntervalOutOfBoundsError>,
    {
        if rect.is_empty() {
            return Ok(());
        }
        let ti = rect.time();
        let si = rect.space();

        self.timeline
            .try_edit_in(ti.start()..ti.end(), |quay_state| f(quay_state, si))
    }

    #[inline]
    pub fn occupy(
        &mut self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        self.apply_in(rect, |q, si| q.occupy(si))
    }

    #[inline]
    pub fn free(
        &mut self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        self.apply_in(rect, |q, si| q.free(si))
    }
}

impl<'a, T, C, Q> TryFrom<&Problem<'a, T, C>> for BerthOccupancy<T, Q>
where
    T: PrimInt + Signed + Zero + Copy,
    C: PrimInt + Signed + Zero + Copy,
    Q: Quay,
{
    type Error = QuaySpaceIntervalOutOfBoundsError;
    fn try_from(problem: &Problem<T, C>) -> Result<Self, Self::Error> {
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
            berth_occupancy.occupy(&rect)?;
        }
        Ok(berth_occupancy)
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
    fn add_occupy(
        &mut self,
        time: TimePoint<T>,
        space: SpaceInterval,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        if !self.berth().space_within_quay(space) {
            return Err(QuaySpaceIntervalOutOfBoundsError::new(
                space,
                self.berth().quay_length(),
            ));
        }
        if space.is_empty() {
            return Ok(());
        }

        if let Some(fset) = self.free_by_time.get_mut(&time) {
            fset.subtract_interval(space);
            if fset.is_empty() {
                self.free_by_time.remove(&time);
            }
        }

        self.occupied_by_time
            .entry(time)
            .or_default()
            .insert_and_coalesce(space);
        Ok(())
    }

    pub fn occupy(
        &mut self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        if !self.berth().space_within_quay(rect.space()) {
            return Err(QuaySpaceIntervalOutOfBoundsError::new(
                rect.space(),
                self.berth().quay_length(),
            ));
        }

        let time_window = rect.time();
        let space_interval = rect.space();

        if let Some(pred) = self
            .berth()
            .slice_predecessor_timepoint(time_window.start())
        {
            self.add_occupy(pred, space_interval)?;
        }
        for timepoint in self
            .berth()
            .slices(time_window.start(), time_window.end())
            .interior_keys()
        {
            self.add_occupy(timepoint, space_interval)?;
        }

        Ok(())
    }

    #[inline]
    fn add_free(
        &mut self,
        time: TimePoint<T>,
        space: SpaceInterval,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        if !self.berth().space_within_quay(space) {
            return Err(QuaySpaceIntervalOutOfBoundsError::new(
                space,
                self.berth().quay_length(),
            ));
        }
        if space.is_empty() {
            return Ok(());
        }

        if let Some(oset) = self.occupied_by_time.get_mut(&time) {
            oset.subtract_interval(space);
            if oset.is_empty() {
                self.occupied_by_time.remove(&time);
            }
        }

        self.free_by_time
            .entry(time)
            .or_default()
            .insert_and_coalesce(space);
        Ok(())
    }

    pub fn free(
        &mut self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        if !self.berth().space_within_quay(rect.space()) {
            return Err(QuaySpaceIntervalOutOfBoundsError::new(
                rect.space(),
                self.berth().quay_length(),
            ));
        }

        let time_window = rect.time();
        let space_interval = rect.space();

        if let Some(pred) = self
            .berth()
            .slice_predecessor_timepoint(time_window.start())
        {
            self.add_free(pred, space_interval)?;
        }
        for timepoint in self
            .berth()
            .slices(time_window.start(), time_window.end())
            .interior_keys()
        {
            self.add_free(timepoint, space_interval)?;
        }

        Ok(())
    }

    fn covering_timepoints_union(
        &self,
        tw: TimeInterval<T>,
    ) -> impl Iterator<Item = TimePoint<T>> + '_ {
        let start = tw.start();
        let end = tw.end();

        // Base: predecessor at `start` (if any) + interior keys (Excluded bounds)
        let base = self.berth().slices(start, end).covering_keys().peekable();

        // Overlay keys inside [start, end)
        let overlay = KeysUnion::new(&self.free_by_time, &self.occupied_by_time)
            .filter(move |&t| t >= start && t < end)
            .peekable();

        // Merge two sorted, strictly ascending streams with de-dupe.
        std::iter::from_fn({
            let mut a = base;
            let mut b = overlay;
            let mut last: Option<TimePoint<T>> = None;

            move || loop {
                let na = a.peek().copied();
                let nb = b.peek().copied();
                let next = match (na, nb) {
                    (None, None) => return None,
                    (Some(x), None) => {
                        a.next();
                        Some(x)
                    }
                    (None, Some(y)) => {
                        b.next();
                        Some(y)
                    }
                    (Some(x), Some(y)) => match x.cmp(&y) {
                        std::cmp::Ordering::Less => {
                            a.next();
                            Some(x)
                        }
                        std::cmp::Ordering::Greater => {
                            b.next();
                            Some(y)
                        }
                        std::cmp::Ordering::Equal => {
                            a.next();
                            b.next();
                            Some(x)
                        }
                    },
                };
                if next != last {
                    last = next;
                    return last;
                }
            }
        })
    }

    pub fn is_free(
        &self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        let tw = rect.time();
        let si = rect.space();

        if !self.berth().space_within_quay(si) {
            return Err(QuaySpaceIntervalOutOfBoundsError::new(
                si,
                self.berth().quay_length(),
            ));
        }

        if rect.is_empty() {
            return Ok(true);
        }

        Ok(self
            .covering_timepoints_union(tw)
            .all(|tp| runs_cover_interval(self.free_runs_at(tp), si)))
    }

    #[inline]
    pub fn is_occupied(
        &self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        Ok(!self.is_free(rect)?)
    }

    #[inline]
    pub fn iter_free_slots(
        &'a self,
        time_window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> impl Iterator<Item = FreeSlot<T>> + 'a {
        FreeSlotIter::new(self, time_window, duration, required_space, space_window)
    }

    #[inline]
    pub fn iter_free_regions(
        &'a self,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> impl Iterator<Item = SpaceTimeRectangle<T>> + 'a {
        FeasibleRegionIter::new(self, window, duration, required_space, space_window)
    }
}

pub struct FreeSlotIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    view: &'a V,
    time_window: TimeInterval<T>,
    duration: TimeDelta<T>,
    required: SpaceLength,
    bounds: SpaceInterval,
    first_cand: TimePoint<T>,
    last_candidate: Option<TimePoint<T>>,
    yielded_window_start: bool,
    current_start: Option<TimePoint<T>>,
    runs: DoubleBuf<SpaceInterval>,
    emit_idx: usize,
    is_empty: bool,
}

impl<'a, T, V> FreeSlotIter<'a, T, V>
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
        let duration = clamp_nonnegative(duration);
        let first_cand = time_window.start();

        Self {
            view,
            time_window,
            duration,
            required,
            bounds,
            first_cand,
            last_candidate: None,
            yielded_window_start: false,
            current_start: None,
            runs: DoubleBuf::new(),
            emit_idx: 0,
            is_empty: required > bounds.length(),
        }
    }

    fn next_candidate_start(&mut self) -> Option<TimePoint<T>> {
        let start = self.first_cand;
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
        if let Some(tp) = self.view.next_key_after(last)
            && tp + self.duration <= end
        {
            self.last_candidate = Some(tp);
            return Some(tp);
        }
        if self.duration.is_zero() && last < end && self.view.has_key_at(end) {
            self.last_candidate = Some(end);
            return Some(end);
        }
        None
    }

    fn build_runs_for_start(&mut self, start: TimePoint<T>) {
        self.runs.clear();
        self.emit_idx = 0;
        self.current_start = None;

        let end = start + self.duration;
        let final_runs = eroded_runs(self.view, start, end, self.bounds, self.required);

        if final_runs.is_empty() {
            return;
        }

        self.runs.seed_from_iter(final_runs.into_iter());
        self.current_start = Some(start);
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

pub struct FeasibleRegionIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    view: &'a V,
    duration: TimeDelta<T>,
    required: SpaceLength,
    bounds: SpaceInterval,

    // Sorted, deduped start-time breakpoints inside [tw_start, latest_start]
    // where the feasibility set can change (keys or keys - duration).
    bps: Vec<TimePoint<T>>,
    bp_idx: usize,

    // per-segment emission
    cur_runs: Vec<SpaceInterval>,
    run_idx: usize,

    // segment time window
    seg_start: TimePoint<T>,
    seg_end: TimePoint<T>,
}

impl<'a, T, V> FeasibleRegionIter<'a, T, V>
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
        // No starts possible if required > bounds
        let mut bps: Vec<TimePoint<T>> = Vec::new();

        // latest start time allowed by the window:
        // any start s must satisfy s + duration <= time_window.end()
        let tw_start = time_window.start();
        let tw_end = time_window.end();

        // If duration is negative, treat like zero (no-op duration).
        let duration = if duration.value() < T::zero() {
            TimeDelta::new(T::zero())
        } else {
            duration
        };

        // If even the window start can't fit the duration, we will yield nothing.
        let latest_start = tw_end - duration;
        if tw_start > latest_start {
            return Self {
                view,
                duration,
                required,
                bounds,
                bps,
                bp_idx: 0,
                cur_runs: Vec::new(),
                run_idx: 0,
                seg_start: tw_start,
                seg_end: tw_start,
            };
        }

        // Collect interior keys in (tw_start, latest_start)
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

        // Keys where feasibility can change:
        //  - when the left edge of the duration window crosses a key   → keys in (start, latest_start)
        //  - when the right edge crosses a key                         → (keys in (start+dur, latest_start+dur)) shifted by -dur
        let mut keys_left = collect_keys(view, tw_start, latest_start);

        let shifted_left = tw_start + duration;
        let shifted_right = latest_start + duration;
        let one = TimeDelta::new(T::one());
        let mut keys_right_shifted_back: Vec<_> =
            collect_keys_left_inclusive(view, shifted_left, shifted_right)
                .into_iter()
                .map(|t| t - duration + one)
                .filter(|&t| t > tw_start && t <= latest_start)
                .collect();

        bps.reserve(2 + keys_left.len() + keys_right_shifted_back.len());
        bps.push(tw_start);
        bps.append(&mut keys_left);
        bps.append(&mut keys_right_shifted_back);
        bps.push(latest_start);

        // sort + dedup
        bps.sort_unstable_by_key(|t| t.value());
        bps.dedup_by_key(|t| t.value());

        Self {
            view,
            duration,
            required,
            bounds,
            bps,
            bp_idx: 0,
            cur_runs: Vec::new(),
            run_idx: 0,
            seg_start: tw_start,
            seg_end: tw_start,
        }
    }

    fn runs_for_start(&self, s: TimePoint<T>) -> Vec<SpaceInterval> {
        eroded_runs(self.view, s, s + self.duration, self.bounds, self.required)
    }
}

#[inline]
fn rep_start<T: PrimInt + Signed + Copy + One>(a: TimePoint<T>, b: TimePoint<T>) -> TimePoint<T> {
    // Prefer an interior point if it exists; otherwise stick with `a`.
    let one = TimeDelta::new(T::one());
    if a + one < b { a + one } else { a }
}

impl<'a, T, V> Iterator for FeasibleRegionIter<'a, T, V>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + 'a,
{
    type Item = SpaceTimeRectangle<T>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // If we have runs to emit for this segment, emit them one by one.
            if self.run_idx < self.cur_runs.len() {
                let iv = self.cur_runs[self.run_idx];
                self.run_idx += 1;
                return Some(SpaceTimeRectangle::new(
                    iv,
                    TimeInterval::new(self.seg_start, self.seg_end),
                ));
            }

            // Move to next start-time segment
            if self.bp_idx + 1 >= self.bps.len() {
                return None;
            }
            self.seg_start = self.bps[self.bp_idx];
            self.seg_end = self.bps[self.bp_idx + 1];
            self.bp_idx += 1;

            // Guard (zero-length segment)
            if self.seg_start >= self.seg_end {
                continue;
            }

            // Compute eroded runs for *this* start point. These runs are constant
            // for all starts in [seg_start, seg_end), by construction of breakpoints.
            // self.cur_runs = self.runs_for_start(self.seg_start);

            let s_rep = rep_start(self.seg_start, self.seg_end);
            self.cur_runs = self.runs_for_start(s_rep);
            self.run_idx = 0;

            if self.cur_runs.is_empty() {
                // Nothing feasible in this segment; advance again.
                continue;
            }

            // Loop back to emit runs
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
        if iv.end() <= need_start {
            continue;
        }
        if iv.start() > need_start {
            return false;
        }
        let mut covered_end = iv.end();
        while let Some(next) = runs.peek().copied() {
            if next.start() > covered_end {
                break;
            }
            if next.end() > covered_end {
                covered_end = next.end();
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
            let out = a.intersection(&b);
            if a.end() < b.end() {
                self.cur_left = None;
            } else {
                self.cur_right = None;
            }

            if let Some(iv) = out
                && iv.length() >= self.required
            {
                return Some(iv);
            }
        }
    }
}

type SpaceIntervalSet = IntervalSet<SpacePosition>;

#[derive(Clone, Debug)]
struct KeysUnion<'a, T: PrimInt + Signed> {
    free_keys:
        Peekable<Copied<std::collections::btree_map::Keys<'a, TimePoint<T>, SpaceIntervalSet>>>,
    occupied_keys:
        Peekable<Copied<std::collections::btree_map::Keys<'a, TimePoint<T>, SpaceIntervalSet>>>,
}

impl<'a, T: PrimInt + Signed> KeysUnion<'a, T> {
    #[inline]
    fn new(
        free: &'a BTreeMap<TimePoint<T>, SpaceIntervalSet>,
        occ: &'a BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    ) -> Self {
        Self {
            free_keys: free.keys().copied().peekable(),
            occupied_keys: occ.keys().copied().peekable(),
        }
    }
}

impl<'a, T: PrimInt + Signed> Iterator for KeysUnion<'a, T> {
    type Item = TimePoint<T>;
    fn next(&mut self) -> Option<Self::Item> {
        let peek_a = self.free_keys.peek().copied();
        let peek_b = self.occupied_keys.peek().copied();

        match (peek_a, peek_b) {
            (None, None) => None,
            (Some(_), None) => self.free_keys.next(),
            (None, Some(_)) => self.occupied_keys.next(),
            (Some(x), Some(y)) => match x.cmp(&y) {
                std::cmp::Ordering::Less => self.free_keys.next(),
                std::cmp::Ordering::Greater => self.occupied_keys.next(),
                std::cmp::Ordering::Equal => {
                    self.free_keys.next();
                    self.occupied_keys.next();
                    Some(x)
                }
            },
        }
    }
}

impl<'a, T: PrimInt + Signed> FusedIterator for KeysUnion<'a, T> {}

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

#[inline]
fn eroded_runs<'v, T, V>(
    view: &'v V,
    start: TimePoint<T>,
    end: TimePoint<T>,
    bounds: SpaceInterval,
    min_len: SpaceLength,
) -> Vec<SpaceInterval>
where
    T: PrimInt + Signed + Copy,
    V: SliceView<T> + ?Sized + 'v,
{
    use dock_alloc_core::mem::DoubleBuf;

    let pred = match view.pred(start) {
        Some(p) => p,
        None => return Vec::new(),
    };
    let seed_tp = if view.has_key_at(start) { start } else { pred };

    let mut db: DoubleBuf<SpaceInterval> = DoubleBuf::new();
    db.seed_from_iter(runs_at(view, seed_tp, bounds, min_len));

    if db.current().is_empty() {
        return Vec::new();
    }

    let mut cursor = start;
    while let Some(tp) = view.next_key_after(cursor) {
        if tp >= end {
            break;
        }
        cursor = tp;
        db.step(|cur, next| {
            next.extend(IntersectRuns::new(
                cur.iter().copied(),
                runs_at(view, tp, bounds, min_len),
                min_len,
            ));
        });
        if db.current().is_empty() {
            return Vec::new();
        }
    }

    db.current().to_vec()
}

#[inline]
fn clamp_nonnegative<T: PrimInt + Signed + Copy>(d: TimeDelta<T>) -> TimeDelta<T> {
    if d.value() < T::zero() {
        TimeDelta::new(T::zero())
    } else {
        d
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, fmt::Display};

    use num_traits::One;

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
            .iter_free_slots(tw, dur, need, bounds)
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
        assert!(
            berth_occupancy
                .is_free(&rect(ti(0, 100), si(0, 10)))
                .unwrap()
        );
        assert!(
            !berth_occupancy
                .is_occupied(&rect(ti(0, 100), si(0, 10)))
                .unwrap()
        );
    }

    #[test]
    fn test_occupy_creates_boundaries_and_mutates_exact_span() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();

        // boundaries at 0 (origin), 5, 10
        assert_eq!(berth_occupancy.time_event_count(), 3);

        // before 5 -> free
        assert!(berth_occupancy.is_free(&rect(ti(0, 5), si(2, 5))).unwrap());

        // [5,10) occupied in [2,5)
        assert!(
            berth_occupancy
                .is_occupied(&rect(ti(5, 10), si(2, 5)))
                .unwrap()
        );
        assert!(!berth_occupancy.is_free(&rect(ti(5, 10), si(2, 5))).unwrap());

        // after 10 -> back to free
        assert!(
            berth_occupancy
                .is_free(&rect(ti(10, 20), si(2, 5)))
                .unwrap()
        );
    }

    #[test]
    fn test_free_then_coalesce_back_to_single_event() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();
        berth_occupancy.free(&rect(ti(5, 10), si(2, 5))).unwrap();

        // Should merge back to a single fully-free snapshot
        assert_eq!(berth_occupancy.time_event_count(), 1);
        assert!(
            berth_occupancy
                .is_free(&rect(ti(0, 100), si(0, 10)))
                .unwrap()
        );
    }

    #[test]
    fn test_no_mutation_outside_interval() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();

        // Space outside [2,5) always free
        assert!(
            berth_occupancy
                .is_free(&rect(ti(0, 100), si(0, 2)))
                .unwrap()
        );
        assert!(
            berth_occupancy
                .is_free(&rect(ti(0, 100), si(5, 10)))
                .unwrap()
        );

        // Times outside [5,10) always free within [2,5)
        assert!(berth_occupancy.is_free(&rect(ti(0, 5), si(2, 5))).unwrap());
        assert!(
            berth_occupancy
                .is_free(&rect(ti(10, 20), si(2, 5)))
                .unwrap()
        );
    }

    #[test]
    fn test_empty_time_interval_and_empty_space_are_noops() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        // Empty time: [3,3)
        berth_occupancy.occupy(&rect(ti(3, 3), si(2, 4))).unwrap();
        assert_eq!(berth_occupancy.time_event_count(), 1);

        // Empty space: [6,6)
        berth_occupancy.occupy(&rect(ti(0, 5), si(6, 6))).unwrap();
        assert_eq!(
            berth_occupancy.time_event_count(),
            1,
            "empty space should be a no-op"
        );

        // But no mutation in the snapshot at t=0
        assert!(berth_occupancy.is_free(&rect(ti(0, 5), si(0, 10))).unwrap());
    }

    #[test]
    fn test_overlapping_occupies_produce_multiple_boundaries() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 12), si(2, 4))).unwrap();
        berth_occupancy.occupy(&rect(ti(8, 15), si(1, 3))).unwrap();

        // boundaries: 0,5,8,12,15
        assert_eq!(berth_occupancy.time_event_count(), 5);

        // Check a few windows
        assert!(
            berth_occupancy
                .is_occupied(&rect(ti(6, 7), si(2, 4)))
                .unwrap()
        ); // first occupy
        assert!(
            berth_occupancy
                .is_occupied(&rect(ti(9, 11), si(1, 3)))
                .unwrap()
        ); // overlap of both
        assert!(
            berth_occupancy
                .is_free(&rect(ti(12, 15), si(3, 10)))
                .unwrap()
        ); // free region in space
    }

    #[test]
    fn test_partial_free_does_not_fully_clear() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();
        berth_occupancy.free(&rect(ti(7, 9), si(3, 4))).unwrap();

        // [7,9) now has [3,4) free but [2,3) and [4,5) still occupied
        assert!(
            berth_occupancy
                .is_occupied(&rect(ti(7, 9), si(2, 3)))
                .unwrap()
        );
        assert!(berth_occupancy.is_free(&rect(ti(7, 9), si(3, 4))).unwrap());
        assert!(
            berth_occupancy
                .is_occupied(&rect(ti(7, 9), si(4, 5)))
                .unwrap()
        );
    }

    #[test]
    fn test_query_crossing_boundary_uses_predecessor_and_timepoints() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();

        // Query [4,6): must consider predecessor of 4 (t=0) and key 5 in (4,6)
        // Since at t=5 it becomes occupied, overall "is_free" must be false.
        assert!(!berth_occupancy.is_free(&rect(ti(4, 6), si(2, 5))).unwrap());
        assert!(
            berth_occupancy
                .is_occupied(&rect(ti(4, 6), si(2, 5)))
                .unwrap()
        );
    }

    #[test]
    fn test_occupy_idempotent_over_same_region() {
        let quay_length = len(16);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy
            .occupy(&rect(ti(10, 20), si(4, 12)))
            .unwrap();
        let events_after_first = berth_occupancy.time_event_count();

        berth_occupancy
            .occupy(&rect(ti(10, 20), si(4, 12)))
            .unwrap();
        assert_eq!(
            berth_occupancy.time_event_count(),
            events_after_first,
            "idempotent occupy should not add events"
        );

        assert!(
            berth_occupancy
                .is_occupied(&rect(ti(10, 20), si(4, 12)))
                .unwrap()
        );
    }

    #[test]
    fn test_free_idempotent_over_same_region() {
        let quay_length = len(16);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy
            .occupy(&rect(ti(10, 20), si(4, 12)))
            .unwrap();
        berth_occupancy.free(&rect(ti(10, 20), si(4, 12))).unwrap();
        let events_after_first = berth_occupancy.time_event_count();

        berth_occupancy.free(&rect(ti(10, 20), si(4, 12))).unwrap();
        assert_eq!(
            berth_occupancy.time_event_count(),
            events_after_first,
            "idempotent free should not add events"
        );
        assert!(
            berth_occupancy
                .is_free(&rect(ti(0, 100), si(0, 16)))
                .unwrap()
        );
    }

    #[test]
    fn test_adjacent_updates_keep_half_open_semantics() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        // Occupy [2,5) left, then [5,7) right, on same space
        berth_occupancy.occupy(&rect(ti(2, 5), si(3, 6))).unwrap();
        berth_occupancy.occupy(&rect(ti(5, 7), si(3, 6))).unwrap();

        // At t=5 they just touch; the occupancy is continuous across [2,7).
        // With redundancy coalescing, the boundary at 5 is removed.
        assert!(
            berth_occupancy
                .is_occupied(&rect(ti(2, 7), si(3, 6)))
                .unwrap()
        );
        assert_eq!(berth_occupancy.time_event_count(), 3); // keys: 0, 2, 7
    }

    #[test]
    fn test_coalesce_across_border_after_full_revert() {
        let quay_length = len(8);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(3, 6), si(2, 4))).unwrap();
        // Now revert with two frees that exactly cancel
        berth_occupancy.free(&rect(ti(3, 4), si(2, 4))).unwrap();
        berth_occupancy.free(&rect(ti(4, 6), si(2, 4))).unwrap();

        // Should fully coalesce back to one event
        assert_eq!(berth_occupancy.time_event_count(), 1);
        assert!(berth_occupancy.is_free(&rect(ti(0, 10), si(0, 8))).unwrap());
    }

    #[test]
    fn test_snapshot_at_reads_correct_state() {
        let quay_length = len(6);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(&rect(ti(2, 4), si(1, 3))).unwrap();

        // snapshot before 2: free
        {
            let quay_state = berth_occupancy.snapshot_at(tp(1)).unwrap();
            assert!(quay_state.check_free(si(0, 6)).unwrap());
        }
        // snapshot at 2..4: occupied 1..3
        {
            let quay_state = berth_occupancy.snapshot_at(tp(2)).unwrap();
            assert!(quay_state.check_occupied(si(1, 3)).unwrap());
            assert!(quay_state.check_free(si(0, 1)).unwrap());
            assert!(quay_state.check_free(si(3, 6)).unwrap());
        }
        // snapshot after 4: free
        {
            let quay_state = berth_occupancy.snapshot_at(tp(5)).unwrap();
            assert!(quay_state.check_free(si(0, 6)).unwrap());
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
    fn test_free_iter_multiple_candidates_from_timepoints() {
        // Create additional timeline keys at 5 and 6 without affecting the searched bounds.
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(&rect(ti(5, 6), si(9, 10))).unwrap(); // creates keys 5 and 6

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
    fn test_free_iter_intersects_across_multiple_slices() {
        // Make two slice keys inside the processing span so intersection actually happens.
        // At t=5 free space is [0,2) ∪ [6,10); at t=7 free space is [0,6) ∪ [9,10).
        // Intersection across [5,8) => runs [0,2) and [9,10).
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(&rect(ti(5, 9), si(2, 6))).unwrap(); // key at 5
        berth.occupy(&rect(ti(7, 12), si(6, 9))).unwrap(); // key at 7

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
    fn test_free_iter_filters_runs_shorter_than_required() {
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
    fn test_free_iter_empty_when_duration_exceeds_window() {
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
    fn test_free_iter_zero_duration_uses_predecessor_snapshot_each_slice() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        // Occupied at t=5 only in [2,6)
        berth.occupy(&rect(ti(5, 6), si(2, 6))).unwrap();

        // Keys: 0 (origin), 5, 6
        // With dur=0, we’ll check predecessor snapshot for each candidate start:
        // start=0 → free everywhere; start=5 → [2,6) blocked; start=6 → free everywhere again.
        let items: Vec<_> = berth
            .iter_free_slots(ti(0, 6), TimeDelta::new(0), len(2), si(0, 10))
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
    fn test_overlay_add_free_and_occupy_and_queries() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        // Base: occupy [5,10):[2,6)
        berth.occupy(&rect(ti(5, 10), si(2, 6))).unwrap();

        let mut overlay = BerthOccupancyOverlay::new(&berth);

        // At t=5, override a subrange as free via overlay
        overlay.add_free(tp(5), si(2, 4)).unwrap();
        assert!(overlay.is_free(&rect(ti(5, 10), si(2, 4))).unwrap());
        assert!(overlay.is_occupied(&rect(ti(5, 10), si(4, 6))).unwrap()); // still blocked remainder

        // Add an overlay-occupy on otherwise-free area at t=0
        overlay.add_occupy(tp(0), si(0, 1)).unwrap();
        assert!(overlay.is_occupied(&rect(ti(0, 5), si(0, 1))).unwrap());
        assert!(overlay.is_free(&rect(ti(0, 5), si(1, 10))).unwrap());
    }

    #[test]
    fn overlay_free_and_undo_across_timepoints() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        // Create a base boundary at t=5 by occupying [2,6)
        berth.occupy(&rect(ti(5, 7), si(2, 6))).unwrap();

        let mut overlay = BerthOccupancyOverlay::new(&berth);

        // Free [4,5) across [4,6): will place free at predecessor of 4 (t=0) and at timepoint 5
        overlay.free(&rect(ti(4, 6), si(4, 5))).unwrap();
        assert!(overlay.is_free(&rect(ti(4, 6), si(4, 5))).unwrap());
    }

    #[test]
    fn test_snapshot_at_none_before_origin() {
        let berth = BO::new(len(10));
        // Using negative timepoint to test before origin
        assert!(berth.snapshot_at(tp(-1)).is_none());
    }

    #[test]
    fn test_slice_predecessor_equal_at_key() {
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(5, 7), si(2, 3))).unwrap(); // keys: 0,5,7
        assert_eq!(berth.slice_predecessor_timepoint(tp(5)), Some(tp(5)));
        assert_eq!(berth.slice_predecessor_timepoint(tp(6)), Some(tp(5)));
        assert_eq!(berth.slice_predecessor_timepoint(tp(7)), Some(tp(7)));
    }

    #[test]
    fn test_iter_timepoints_is_strictly_inside_half_open() {
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(5, 10), si(0, 1))).unwrap(); // keys 0,5,10
        let v: Vec<_> = berth
            .slices(5.into(), 10.into())
            .interior_keys()
            .map(|t| t.value())
            .collect();
        assert_eq!(v, Vec::<i64>::new());
    }

    #[test]
    fn test_space_within_quay_edges_and_outside() {
        let berth = BO::new(len(8));
        assert!(berth.space_within_quay(si(0, 8)));
        assert!(berth.space_within_quay(si(3, 5)));
        assert!(!berth.space_within_quay(si(7, 9)));
    }

    #[test]
    fn test_occupy_free_coalesce_chain_three_equal_states() {
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(3, 7), si(1, 2))).unwrap(); // 0,3,7
        berth.free(&rect(ti(3, 7), si(1, 2))).unwrap(); // should coalesce back to 0 only
        assert_eq!(berth.time_event_count(), 1);
    }

    #[test]
    fn test_overlay_remove_occupy_undo_occupy() {
        let quay_length = len(10);
        let berth = BO::new(quay_length);
        let mut overlay = BerthOccupancyOverlay::new(&berth);

        overlay.occupy(&rect(ti(2, 6), si(3, 5))).unwrap();
        assert!(overlay.is_occupied(&rect(ti(3, 5), si(3, 5))).unwrap());
    }

    #[test]
    fn test_overlay_iter_free_respects_overlay_through_duration() {
        // Base: occupy [5,9):[2,6). We'll "free" that space via overlay for the slices we care about.
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(5, 9), si(2, 6))).unwrap();

        let mut overlay = BerthOccupancyOverlay::new(&berth);

        // We need overlay freeness at the predecessor of 5 (which is 0) AND at slice key 5,
        // so that the intersection over [5,8) includes [2,6).
        overlay.add_free(tp(0), si(2, 6)).unwrap();
        overlay.add_free(tp(5), si(2, 6)).unwrap();

        let items: Vec<_> = overlay
            .iter_free_slots(ti(5, 9), TimeDelta::new(3), len(2), si(0, 10))
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
    fn test_free_iter_zero_duration_yields_window_end_only_if_key_exists() {
        let mut berth = BO::new(len(10));
        // Ensure a key at end
        berth.occupy(&rect(ti(0, 5), si(0, 1))).unwrap(); // keys 0,5
        let items: Vec<_> = berth
            .iter_free_slots(ti(0, 5), TimeDelta::new(0), len(1), si(0, 10))
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
    fn test_overlay_iter_free_uses_overlay_keys_as_candidates() {
        let berth = BO::new(len(10)); // fully free; no extra keys
        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Introduce an overlay key inside the window
        ov.add_occupy(tp(7), si(0, 1)).unwrap();
        // Duration 2 forces candidate starts at 0 and 7 (overlay key)
        let items: Vec<_> = ov
            .iter_free_slots(ti(0, 10), TimeDelta::new(2), len(1), si(0, 10))
            .map(|f| f.start_time().value())
            .collect();
        let mut unique_items: Vec<_> = items;
        unique_items.sort();
        unique_items.dedup();

        assert!(unique_items.contains(&0));
        assert!(unique_items.contains(&7));
    }

    #[test]
    fn test_overlay_changes_at_start_are_applied_when_pred_differs() {
        type BO = BerthOccupancy<i64, BooleanVecQuay>;
        let mut berth = BO::new(SpaceLength::new(10)); // fully free
        berth
            .occupy(&rect(
                TimeInterval::new(TimePoint::new(7), TimePoint::new(9)),
                SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(6)),
            ))
            .unwrap();
        // keys now: 0,7,9

        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Make [2,6) occupied by default via overlay at pred=0, but free exactly at start=5
        ov.add_occupy(
            TimePoint::new(0),
            SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(6)),
        )
        .unwrap();
        ov.add_free(
            TimePoint::new(5),
            SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(6)),
        )
        .unwrap();

        let items: Vec<_> = ov
            .iter_free_slots(
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
    fn test_runs_cover_interval_handles_touching() {
        let runs = vec![si(0, 5), si(5, 8)].into_iter();
        assert!(runs_cover_interval(runs, si(0, 8)));
    }

    #[test]
    fn test_overlay_occupy_free_roundtrip() {
        let quay_length = len(10);
        let berth = BO::new(quay_length);
        let mut overlay = BerthOccupancyOverlay::new(&berth);

        let rect = rect(ti(2, 6), si(3, 5));
        overlay.occupy(&rect).unwrap();
        assert!(overlay.is_occupied(&rect).unwrap());
        overlay.free(&rect).unwrap();
        assert!(overlay.is_free(&rect).unwrap());
    }

    #[test]
    fn test_overlay_partial_overlap_last_wins_only_on_overlap() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);
        // occupy [3,7)×[3,6)
        let a = rect(ti(3, 7), si(3, 6));
        ov.occupy(&a).unwrap();
        // free partially [4,6)×[4,5)
        let b = rect(ti(4, 6), si(4, 5));
        ov.free(&b).unwrap();

        // overlap is free now
        assert!(ov.is_free(&b).unwrap());
        // non-overlapped rims remain occupied
        assert!(ov.is_occupied(&rect(ti(4, 6), si(3, 4))).unwrap());
        assert!(ov.is_occupied(&rect(ti(4, 6), si(5, 6))).unwrap());
    }

    fn iv_to_tuple(iv: SpaceInterval) -> (usize, usize) {
        (iv.start().value(), iv.end().value())
    }

    fn set_from_intervals(v: impl IntoIterator<Item = SpaceInterval>) -> BTreeSet<(usize, usize)> {
        v.into_iter().map(iv_to_tuple).collect()
    }

    /// Collect start-feasible bands as: time-band -> set of space runs
    fn collect_bands_base<T: PrimInt + Signed + Copy, Q: QuayRead + Clone + PartialEq>(
        berth: &BerthOccupancy<T, Q>,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> BTreeMap<(T, T), BTreeSet<(usize, usize)>> {
        let mut out: BTreeMap<(T, T), Vec<SpaceInterval>> = BTreeMap::new();
        for r in berth.iter_free_regions(window, duration, required, bounds) {
            out.entry((r.time().start().value(), r.time().end().value()))
                .or_default()
                .push(r.space());
        }
        out.into_iter()
            .map(|(k, v)| (k, set_from_intervals(v)))
            .collect()
    }

    fn collect_bands_overlay<'brand, 'a, T: PrimInt + Signed + Copy, Q: QuayRead>(
        ov: &BerthOccupancyOverlay<'brand, 'a, T, Q>,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> BTreeMap<(T, T), BTreeSet<(usize, usize)>> {
        let mut out: BTreeMap<(T, T), Vec<SpaceInterval>> = BTreeMap::new();
        for r in ov.iter_free_regions(window, duration, required, bounds) {
            out.entry((r.time().start().value(), r.time().end().value()))
                .or_default()
                .push(r.space());
        }
        out.into_iter()
            .map(|(k, v)| (k, set_from_intervals(v)))
            .collect()
    }

    fn slot_set_for_start_base<T, Q>(
        berth: &BerthOccupancy<T, Q>,
        s: TimePoint<T>,
        mut duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> BTreeSet<(usize, usize)>
    where
        T: PrimInt + Signed + Copy,
        Q: QuayRead + Clone + PartialEq,
    {
        if duration.value() < T::zero() {
            duration = TimeDelta::new(T::zero());
        }
        let tw = TimeInterval::new(s, s + duration);
        berth
            .iter_free_slots(tw, duration, required, bounds)
            .filter(|fs| fs.start_time() == s)
            .map(|fs| iv_to_tuple(fs.space()))
            .collect()
    }

    fn slot_set_for_start_overlay<'brand, 'a, T, Q>(
        ov: &BerthOccupancyOverlay<'brand, 'a, T, Q>,
        s: TimePoint<T>,
        mut duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> BTreeSet<(usize, usize)>
    where
        T: PrimInt + Signed + Copy,
        Q: QuayRead,
    {
        if duration.value() < T::zero() {
            duration = TimeDelta::new(T::zero());
        }
        let tw = TimeInterval::new(s, s + duration);
        ov.iter_free_slots(tw, duration, required, bounds)
            .filter(|fs| fs.start_time() == s)
            .map(|fs| iv_to_tuple(fs.space()))
            .collect()
    }

    /// Pick representative sample starts inside a half-open band [a,b)
    fn sample_starts_in_band<T: PrimInt + Signed + Copy + One>(a: T, b: T) -> Vec<T> {
        if a >= b {
            return vec![];
        }
        let one = T::one();
        let mut v = vec![a];
        let span = b - a;
        if span > one {
            // a middle point
            v.push(a + (span / (one + one))); // roughly midpoint
            // last valid discrete start (b-1)
            v.push(b - one);
            v.sort_unstable();
            v.dedup();
        }
        v
    }

    /// Assert that regions (bands) agree with slots for several starts within each band (BASE)
    fn assert_regions_match_slots_base<T, Q>(
        berth: &BerthOccupancy<T, Q>,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) where
        T: PrimInt + Signed + Copy + One + Display,
        Q: QuayRead + Clone + PartialEq,
    {
        let bands = collect_bands_base(berth, window, duration, required, bounds);
        for ((ts, te), spaces) in bands {
            for s in sample_starts_in_band(ts, te) {
                let got =
                    slot_set_for_start_base(berth, TimePoint::new(s), duration, required, bounds);
                assert_eq!(
                    got, spaces,
                    "slot set at start={} must equal region runs for band [{}, {})",
                    s, ts, te
                );
            }
        }
    }

    /// Assert that regions (bands) agree with slots for several starts within each band (OVERLAY)
    fn assert_regions_match_slots_overlay<'brand, 'a, T, Q>(
        ov: &BerthOccupancyOverlay<'brand, 'a, T, Q>,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) where
        T: PrimInt + Signed + Copy + One + Display,
        Q: QuayRead,
    {
        let bands = collect_bands_overlay(ov, window, duration, required, bounds);
        for ((ts, te), spaces) in bands {
            for s in sample_starts_in_band(ts, te) {
                let got =
                    slot_set_for_start_overlay(ov, TimePoint::new(s), duration, required, bounds);
                assert_eq!(
                    got, spaces,
                    "overlay slot set at start={} must equal region runs for band [{}, {})",
                    s, ts, te
                );
            }
        }
    }

    #[test]
    fn regions_vs_slots_fully_free_base() {
        let berth = BO::new(len(10));
        // window [0,10), dur=3 -> latest start = 7
        assert_regions_match_slots_base(&berth, ti(0, 10), TimeDelta::new(3), len(2), si(0, 10));
    }

    #[test]
    fn regions_vs_slots_single_occupy_base() {
        // Base occupy [5,10)×[2,5)
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();

        // Probe several durations & bounds
        assert_regions_match_slots_base(&berth, ti(0, 12), TimeDelta::new(3), len(1), si(0, 10));
        assert_regions_match_slots_base(&berth, ti(0, 12), TimeDelta::new(3), len(2), si(0, 10));
        assert_regions_match_slots_base(&berth, ti(0, 12), TimeDelta::new(4), len(3), si(0, 10));
    }

    #[test]
    fn regions_vs_slots_multiple_keys_intersections_base() {
        // Two overlapping occupies to force intersections inside the moving window
        let mut berth = BO::new(len(12));
        berth.occupy(&rect(ti(4, 9), si(3, 7))).unwrap(); // key 4
        berth.occupy(&rect(ti(7, 11), si(6, 10))).unwrap(); // key 7,11

        // The bands should match what slots say for starts throughout the window
        assert_regions_match_slots_base(&berth, ti(4, 11), TimeDelta::new(3), len(1), si(0, 12));
        assert_regions_match_slots_base(&berth, ti(0, 12), TimeDelta::new(2), len(2), si(0, 12));
    }

    #[test]
    fn regions_vs_slots_min_len_and_bounds_base() {
        let berth = BO::new(len(10)); // fully free
        // Require more than the bounds → no bands
        assert!(
            collect_bands_base(&berth, ti(0, 10), TimeDelta::new(2), len(6), si(1, 6)).is_empty()
        );

        // Feasible with exact bounds and min length
        assert_regions_match_slots_base(&berth, ti(0, 10), TimeDelta::new(2), len(5), si(1, 6));
    }

    #[test]
    fn regions_vs_slots_zero_and_negative_duration_base() {
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(5, 6), si(2, 6))).unwrap(); // keys 5,6

        // dur=0 behaves like per-slice feasibility, but returned as bands of starts.
        assert_regions_match_slots_base(&berth, ti(0, 6), TimeDelta::new(0), len(2), si(0, 10));

        // negative dur is treated as 0 inside FeasibleRegionIter
        assert_regions_match_slots_base(&berth, ti(0, 6), TimeDelta::new(-3), len(2), si(0, 10));
    }

    #[test]
    fn regions_empty_when_duration_exceeds_window_base() {
        let berth = BO::new(len(10));
        // tw [0,4), dur=5 → no starts fit
        let bands = collect_bands_base(&berth, ti(0, 4), TimeDelta::new(5), len(1), si(0, 10));
        assert!(bands.is_empty());
    }

    #[test]
    fn regions_vs_slots_overlay_free_override() {
        // Base: occupy [5,10)×[2,6)
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(5, 10), si(2, 6))).unwrap();

        let mut ov = BerthOccupancyOverlay::new(&berth);
        // At t=5 free the blocked band via overlay
        ov.add_free(tp(5), si(2, 6)).unwrap();

        // Starts in [5, 10-d) should see full space (within bounds) for dur in [1..4]
        assert_regions_match_slots_overlay(&ov, ti(5, 10), TimeDelta::new(3), len(1), si(0, 10));
        assert_regions_match_slots_overlay(&ov, ti(5, 10), TimeDelta::new(4), len(2), si(0, 10));
    }

    #[test]
    fn regions_vs_slots_overlay_union_of_keys() {
        // Base fully free
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        // Introduce overlay key at 7 by occupying [1,3)
        ov.add_occupy(tp(7), si(1, 3)).unwrap();

        // Bands should split at 7 for durations that straddle it
        assert_regions_match_slots_overlay(&ov, ti(5, 10), TimeDelta::new(2), len(1), si(0, 10));
        assert_regions_match_slots_overlay(&ov, ti(5, 10), TimeDelta::new(3), len(1), si(0, 10));
    }

    #[test]
    fn regions_vs_slots_overlay_start_edge_changes() {
        // Base boundary at 7 with occupation [2,6)
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(7, 9), si(2, 6))).unwrap(); // keys 0,7,9

        // Overlay: default occupy pred=0, but free exactly at window start=5
        let mut ov = BerthOccupancyOverlay::new(&berth);
        ov.add_occupy(tp(0), si(2, 6)).unwrap();
        ov.add_free(tp(5), si(2, 6)).unwrap();

        assert_regions_match_slots_overlay(&ov, ti(5, 8), TimeDelta::new(2), len(3), si(0, 10));
    }

    #[test]
    fn regions_vs_slots_bounds_empty_and_required_too_large_overlay() {
        let berth = BO::new(len(10));
        let ov = BerthOccupancyOverlay::new(&berth);

        // Empty bounds → no regions
        assert!(
            collect_bands_overlay(&ov, ti(0, 10), TimeDelta::new(2), len(1), si(3, 3)).is_empty()
        );

        // Required > bounds length → no regions
        assert!(
            collect_bands_overlay(&ov, ti(0, 10), TimeDelta::new(2), len(6), si(1, 6)).is_empty()
        );
    }
}
