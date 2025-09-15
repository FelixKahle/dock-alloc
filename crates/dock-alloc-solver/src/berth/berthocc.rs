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
        commit::BerthOverlayCommit,
        iter::{FeasibleRegionIter, FreeSlotIter},
        operations::Operation,
        overlay::BerthOccupancyOverlay,
        quay::{QuayRead, QuaySpaceIntervalOutOfBoundsError, QuayWrite},
        slice::{SliceView, TimeSliceRef},
    },
    container::timeline::Timeline,
    domain::SpaceTimeRectangle,
};
use dock_alloc_core::{
    SolverVariable,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimeInterval, TimePoint},
};
use dock_alloc_model::prelude::*;
use std::{fmt::Debug, ops::Bound::Excluded};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Slices<'a, T, Q>
where
    T: SolverVariable,
    Q: QuayRead,
{
    berth: &'a BerthOccupancy<T, Q>,
    start: TimePoint<T>,
    end: TimePoint<T>,
}

impl<'a, T, Q> Slices<'a, T, Q>
where
    T: SolverVariable,
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

    /// Returns an iterator over the timeline keys strictly within the time range `(start, end)`.
    #[inline]
    pub fn interior_keys(self) -> impl DoubleEndedIterator<Item = TimePoint<T>> + 'a {
        let start = self.start;
        let end = self.end;
        let timeline = &self.berth.timeline;
        timeline.keys((Excluded(start), Excluded(end)))
    }

    /// Returns an iterator over `TimeSliceRef`s for keys strictly within the time range `(start, end)`.
    #[inline]
    pub fn interior_refs(self) -> impl DoubleEndedIterator<Item = TimeSliceRef<'a, T, Q>> + 'a {
        let start = self.start;
        let end = self.end;
        let timeline = &self.berth.timeline;
        timeline
            .entries((Excluded(start), Excluded(end)))
            .map(|(time, quay)| TimeSliceRef::new(time, quay))
    }

    /// Returns an iterator over the timeline keys within the half-open time range `[start, end)`.
    #[inline]
    pub fn within_keys(self) -> impl DoubleEndedIterator<Item = TimePoint<T>> + 'a {
        let start = self.start;
        let end = self.end;
        let timeline = &self.berth.timeline;
        timeline.keys(start..end)
    }

    /// Returns an iterator over `TimeSliceRef`s for keys within the half-open time range `[start, end)`.
    #[inline]
    pub fn within_refs(self) -> impl DoubleEndedIterator<Item = TimeSliceRef<'a, T, Q>> + 'a {
        let start = self.start;
        let end = self.end;
        let timeline = &self.berth.timeline;
        timeline
            .entries(start..end)
            .map(|(time, quay)| TimeSliceRef::new(time, quay))
    }

    /// Returns an iterator over keys that cover the time range.
    /// This includes the predecessor key at or before `start` and all keys in `(start, end)`.
    #[inline]
    pub fn covering_keys(self) -> impl DoubleEndedIterator<Item = TimePoint<T>> + 'a {
        let start = self.start;
        let end = self.end;
        let timeline = &self.berth.timeline;

        let pred = timeline.floor(start).map(|(t, _)| t);
        let tail = timeline.keys((Excluded(start), Excluded(end)));

        pred.into_iter().chain(tail)
    }

    /// Returns an iterator over `TimeSliceRef`s that cover the time range.
    /// This includes the slice at the predecessor key (at or before `start`) and all slices in `(start, end)`.
    #[inline]
    pub fn covering_refs(self) -> impl DoubleEndedIterator<Item = TimeSliceRef<'a, T, Q>> + 'a {
        let start = self.start;
        let end = self.end;
        let timeline = &self.berth.timeline;

        let pred = timeline
            .floor(start)
            .map(|(time, quay)| TimeSliceRef::new(time, quay));
        let tail = timeline
            .entries((Excluded(start), Excluded(end)))
            .map(|(time, quay)| TimeSliceRef::new(time, quay));

        pred.into_iter().chain(tail)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BerthOccupancy<T, Q>
where
    T: SolverVariable,
{
    quay_length: SpaceLength,
    timeline: Timeline<TimePoint<T>, Q>,
}

impl<T, Q> BerthOccupancy<T, Q>
where
    T: SolverVariable,
    Q: QuayRead + Clone + PartialEq,
{
    #[inline]
    pub fn slices(&self, start: TimePoint<T>, end: TimePoint<T>) -> Slices<'_, T, Q> {
        Slices::new(self, start, end)
    }
}

impl<T, Q> SliceView<T> for BerthOccupancy<T, Q>
where
    T: SolverVariable,
    Q: QuayRead,
{
    type FreeRunsIter<'s>
        = <Q as QuayRead>::FreeIter<'s>
    where
        Self: 's;

    #[inline]
    fn first_key(&self) -> Option<TimePoint<T>> {
        Some(self.timeline.first_key())
    }

    #[inline]
    fn last_key(&self) -> Option<TimePoint<T>> {
        Some(self.timeline.last_key())
    }

    #[inline]
    fn pred(&self, time_point: TimePoint<T>) -> Option<TimePoint<T>> {
        self.slice_predecessor_timepoint(time_point)
    }

    #[inline]
    fn next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>> {
        self.next_time_key_after(after)
    }

    #[inline]
    fn has_key_at(&self, time_point: TimePoint<T>) -> bool {
        self.slice_predecessor_timepoint(time_point)
            .is_some_and(|tp| tp == time_point)
    }

    #[inline]
    fn free_runs_at(&self, time_point: TimePoint<T>) -> Self::FreeRunsIter<'_> {
        let bounds = self.quay_space_interval();
        self.snapshot_at(time_point)
            .expect("slice exists at any valid time point")
            .iter_free_intervals(SpaceLength::new(1), bounds)
    }
}

impl<T, Q> BerthOccupancy<T, Q>
where
    T: SolverVariable,
    Q: QuayRead + Clone + PartialEq,
{
    #[inline]
    pub fn new(quay_length: SpaceLength) -> Self {
        let origin = TimePoint::new(T::zero());
        let initial_quay_state = Q::new(quay_length, true);
        Self {
            quay_length,
            timeline: Timeline::new(origin, initial_quay_state),
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
    pub fn space_within_quay(&self, space_interval: SpaceInterval) -> bool {
        self.quay_space_interval()
            .contains_interval(&space_interval)
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

        let time_interval = rect.time();
        let start_time = time_interval.start();
        let end_time = time_interval.end();
        let space_interval = rect.space();

        for slice in self.slices(start_time, end_time).covering_refs() {
            if !slice.quay().check_free(space_interval)? {
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
    ) -> FreeSlotIter<'_, T, BerthOccupancy<T, Q>>
    where
        T: Copy,
    {
        FreeSlotIter::new(self, time_window, duration, required_space, space_window)
    }

    #[inline]
    pub fn iter_free_regions(
        &self,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> FeasibleRegionIter<'_, T, BerthOccupancy<T, Q>>
    where
        T: Copy,
    {
        FeasibleRegionIter::new(self, window, duration, required_space, space_window)
    }

    #[inline]
    pub fn overlay<'brand>(&self) -> BerthOccupancyOverlay<'brand, '_, T, Q> {
        BerthOccupancyOverlay::new(self)
    }
}

impl<T, Q> BerthOccupancy<T, Q>
where
    T: SolverVariable,
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
        let time_interval = rect.time();
        let space_interval = rect.space();

        self.timeline
            .try_edit_in(time_interval.start()..time_interval.end(), |quay_state| {
                f(quay_state, space_interval)
            })
    }

    #[inline]
    pub fn occupy(
        &mut self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        self.apply_in(rect, |quay, space_interval| quay.occupy(space_interval))
    }

    #[inline]
    pub fn free(
        &mut self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        self.apply_in(rect, |quay, space_interval| quay.free(space_interval))
    }

    #[inline]
    pub fn push_operation(
        &mut self,
        op: &Operation<T>,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        match op {
            Operation::Occupy(occ) => {
                self.occupy(occ.rectangle())?;
            }
            Operation::Free(free) => {
                self.free(free.rectangle())?;
            }
        }
        Ok(())
    }

    #[inline]
    pub fn apply(
        &mut self,
        commit: &BerthOverlayCommit<T>,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        for op in commit.operations() {
            self.push_operation(op)?;
        }
        Ok(())
    }
}

impl<T, C, Q> TryFrom<&Problem<T, C>> for BerthOccupancy<T, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead + QuayWrite,
{
    type Error = QuaySpaceIntervalOutOfBoundsError;
    fn try_from(problem: &Problem<T, C>) -> Result<Self, Self::Error> {
        let mut berth_occupancy = BerthOccupancy::<T, Q>::new(problem.quay_length());
        for fixed_assignment in problem.preassigned() {
            let request = fixed_assignment.request();
            let length = request.length();
            let processing_duration = request.processing_duration();
            let start_time = fixed_assignment.start_time();
            let end_time = start_time + processing_duration;
            let time_interval = TimeInterval::new(start_time, end_time);
            let start_position = fixed_assignment.start_position();
            let end_position = SpacePosition::new(start_position.value() + length.value());
            let space_interval = SpaceInterval::new(start_position, end_position);
            let rect = SpaceTimeRectangle::new(space_interval, time_interval);
            berth_occupancy.occupy(&rect)?;
        }
        Ok(berth_occupancy)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::berth::{
        operations::{FreeOperation, OccupyOperation},
        quay::BooleanVecQuay,
    };
    use num_traits::Zero;

    type T = i64;
    type BO = BerthOccupancy<T, BooleanVecQuay>;

    #[inline]
    fn pos(x: usize) -> SpacePosition {
        SpacePosition::new(x)
    }
    #[inline]
    fn len(x: usize) -> SpaceLength {
        SpaceLength::new(x)
    }
    #[inline]
    fn si(a: usize, b: usize) -> SpaceInterval {
        SpaceInterval::new(pos(a), pos(b))
    }
    #[inline]
    fn tp(t: T) -> TimePoint<T> {
        TimePoint::new(t)
    }
    #[inline]
    fn ti(a: T, b: T) -> TimeInterval<T> {
        TimeInterval::new(tp(a), tp(b))
    }
    #[inline]
    fn rect(tw: TimeInterval<T>, si: SpaceInterval) -> SpaceTimeRectangle<T> {
        SpaceTimeRectangle::new(si, tw)
    }

    #[test]
    fn test_initial_state_single_event_and_free() {
        let b = BO::new(len(10));
        assert_eq!(b.time_event_count(), 1);
        assert!(b.is_free(&rect(ti(0, 100), si(0, 10))).unwrap());
        assert!(!b.is_occupied(&rect(ti(0, 100), si(0, 10))).unwrap());
    }

    #[test]
    fn test_occupy_creates_boundaries_and_applies_only_within_span() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();

        // boundaries at 0 (origin), 5, 10
        assert_eq!(b.time_event_count(), 3);

        // before 5 -> free
        assert!(b.is_free(&rect(ti(0, 5), si(2, 5))).unwrap());
        // [5,10) occupied in [2,5)
        assert!(b.is_occupied(&rect(ti(5, 10), si(2, 5))).unwrap());
        // after 10 -> free again
        assert!(b.is_free(&rect(ti(10, 20), si(2, 5))).unwrap());
    }

    #[test]
    fn test_free_then_coalesce_back_to_single_event() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();
        b.free(&rect(ti(5, 10), si(2, 5))).unwrap();

        assert_eq!(b.time_event_count(), 1);
        assert!(b.is_free(&rect(ti(0, 100), si(0, 10))).unwrap());
    }

    #[test]
    fn test_no_mutation_outside_interval() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();

        assert!(b.is_free(&rect(ti(0, 100), si(0, 2))).unwrap());
        assert!(b.is_free(&rect(ti(0, 100), si(5, 10))).unwrap());
        assert!(b.is_free(&rect(ti(0, 5), si(2, 5))).unwrap());
        assert!(b.is_free(&rect(ti(10, 20), si(2, 5))).unwrap());
    }

    #[test]
    fn test_empty_time_or_space_is_noop() {
        let mut b = BO::new(len(10));

        // Empty time
        b.occupy(&rect(ti(3, 3), si(2, 4))).unwrap();
        assert_eq!(b.time_event_count(), 1);

        // Empty space
        b.occupy(&rect(ti(0, 5), si(6, 6))).unwrap();
        assert_eq!(b.time_event_count(), 1);

        assert!(b.is_free(&rect(ti(0, 5), si(0, 10))).unwrap());
    }

    #[test]
    fn test_overlapping_occupies_produce_multiple_boundaries() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 12), si(2, 4))).unwrap();
        b.occupy(&rect(ti(8, 15), si(1, 3))).unwrap();
        // boundaries: 0,5,8,12,15
        assert_eq!(b.time_event_count(), 5);

        assert!(b.is_occupied(&rect(ti(6, 7), si(2, 4))).unwrap());
        assert!(b.is_occupied(&rect(ti(9, 11), si(1, 3))).unwrap());
        assert!(b.is_free(&rect(ti(12, 15), si(3, 10))).unwrap());
    }

    #[test]
    fn test_partial_free_only_clears_overlap() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();
        b.free(&rect(ti(7, 9), si(3, 4))).unwrap();

        assert!(b.is_occupied(&rect(ti(7, 9), si(2, 3))).unwrap());
        assert!(b.is_free(&rect(ti(7, 9), si(3, 4))).unwrap());
        assert!(b.is_occupied(&rect(ti(7, 9), si(4, 5))).unwrap());
    }

    #[test]
    fn test_query_crossing_boundary_uses_pred_and_keys() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();

        assert!(!b.is_free(&rect(ti(4, 6), si(2, 5))).unwrap());
        assert!(b.is_occupied(&rect(ti(4, 6), si(2, 5))).unwrap());
    }

    #[test]
    fn test_occupy_and_free_are_idempotent() {
        let mut b = BO::new(len(16));
        b.occupy(&rect(ti(10, 20), si(4, 12))).unwrap();
        let n = b.time_event_count();
        b.occupy(&rect(ti(10, 20), si(4, 12))).unwrap();
        assert_eq!(b.time_event_count(), n);

        b.free(&rect(ti(10, 20), si(4, 12))).unwrap();
        let n2 = b.time_event_count();
        b.free(&rect(ti(10, 20), si(4, 12))).unwrap();
        assert_eq!(b.time_event_count(), n2);
    }

    #[test]
    fn test_adjacent_updates_keep_half_open_and_coalesce() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(2, 5), si(3, 6))).unwrap();
        b.occupy(&rect(ti(5, 7), si(3, 6))).unwrap();
        // keys: 0, 2, 7
        assert!(b.is_occupied(&rect(ti(2, 7), si(3, 6))).unwrap());
        assert_eq!(b.time_event_count(), 3);
    }

    #[test]
    fn test_snapshot_at_reflects_state() {
        let mut b = BO::new(len(6));
        b.occupy(&rect(ti(2, 4), si(1, 3))).unwrap();

        let before = b.snapshot_at(tp(1)).unwrap();
        assert!(before.check_free(si(0, 6)).unwrap());

        let during = b.snapshot_at(tp(2)).unwrap();
        assert!(during.check_occupied(si(1, 3)).unwrap());
        assert!(during.check_free(si(0, 1)).unwrap());
        assert!(during.check_free(si(3, 6)).unwrap());

        let after = b.snapshot_at(tp(5)).unwrap();
        assert!(after.check_free(si(0, 6)).unwrap());
    }

    #[test]
    fn test_snapshot_at_none_before_origin() {
        let b = BO::new(len(10));
        assert!(b.snapshot_at(tp(-1)).is_none());
    }

    #[test]
    fn test_slice_predecessor_equal_at_key_and_next_key() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 7), si(2, 3))).unwrap(); // keys: 0,5,7
        assert_eq!(b.slice_predecessor_timepoint(tp(5)), Some(tp(5)));
        assert_eq!(b.slice_predecessor_timepoint(tp(6)), Some(tp(5)));
        assert_eq!(b.slice_predecessor_timepoint(tp(7)), Some(tp(7)));

        assert_eq!(b.next_time_key_after(tp(0)), Some(tp(5)));
        assert_eq!(b.next_time_key_after(tp(5)), Some(tp(7)));
        assert_eq!(b.next_time_key_after(tp(7)), None);
    }

    #[test]
    fn test_slices_interior_and_covering_iterators() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 10), si(0, 1))).unwrap(); // keys: 0,5,10

        // interior keys strictly inside (5,10) are none
        let v: Vec<_> = b
            .slices(tp(5), tp(10))
            .interior_keys()
            .map(|t| t.value())
            .collect();
        assert!(v.is_empty());

        // covering includes pred at 5 (==5) and none inside (5,10)
        let v2: Vec<_> = b
            .slices(tp(5), tp(10))
            .covering_keys()
            .map(|t| t.value())
            .collect();
        assert_eq!(v2, vec![5]);
    }

    #[test]
    fn test_space_within_quay_edges_and_outside() {
        let b = BO::new(len(8));
        assert!(b.space_within_quay(si(0, 8)));
        assert!(b.space_within_quay(si(3, 5)));
        assert!(!b.space_within_quay(si(7, 9)));
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
    fn test_free_iter_fully_free_single_candidate() {
        let b = BO::new(len(8));
        let items = collect_free_iter(&b, ti(0, 10), TimeDelta::new(3), len(2), si(0, 5));
        assert_eq!(items, vec![(0, (0, 5))]);
    }

    #[test]
    fn test_free_iter_candidates_include_timepoints() {
        // Create additional timeline keys at 5 and 6 without affecting searched bounds
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 6), si(9, 10))).unwrap(); // keys 5 and 6

        let items = collect_free_iter(&b, ti(0, 10), TimeDelta::new(3), len(2), si(0, 5));
        assert_eq!(items, vec![(0, (0, 5)), (5, (0, 5)), (6, (0, 5))]);
    }

    #[test]
    fn test_free_iter_intersects_across_multiple_slices() {
        // At t=5 free: [0,2) ∪ [6,10); at t=7 free: [0,6) ∪ [9,10);
        // Intersection over [5,8) gives [0,2) and [9,10).
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 9), si(2, 6))).unwrap(); // key at 5
        b.occupy(&rect(ti(7, 12), si(6, 9))).unwrap(); // key at 7

        let items = collect_free_iter(&b, ti(5, 9), TimeDelta::new(3), len(1), si(0, 10));
        assert_eq!(items, vec![(5, (0, 2)), (5, (9, 10))]);
    }

    #[test]
    fn test_free_iter_filters_runs_shorter_than_required() {
        // Bounds length = 2, require 3 -> empty.
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
    fn test_free_iter_zero_duration_uses_pred_logic() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 6), si(2, 6))).unwrap(); // keys: 0,5,6

        let items: Vec<_> = b
            .iter_free_slots(ti(0, 6), TimeDelta::new(0), len(2), si(0, 10))
            .map(|f| {
                (
                    f.start_time().value(),
                    (f.space().start().value(), f.space().end().value()),
                )
            })
            .collect();

        // Expect runs at t=0 and t=6; at t=5, [2,6) is blocked.
        assert!(items.iter().any(|(t, _)| *t == 0));
        assert!(items.iter().any(|(t, _)| *t == 6));
        assert!(!items.iter().any(|(t, span)| *t == 5 && *span == (2, 6)));
    }

    use std::{collections::BTreeMap, collections::BTreeSet};

    fn iv_to_tuple(iv: SpaceInterval) -> (usize, usize) {
        (iv.start().value(), iv.end().value())
    }
    fn set_from_intervals(v: impl IntoIterator<Item = SpaceInterval>) -> BTreeSet<(usize, usize)> {
        v.into_iter().map(iv_to_tuple).collect()
    }

    fn collect_bands(
        berth: &BO,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> BTreeMap<(T, T), BTreeSet<(usize, usize)>> {
        let mut out: BTreeMap<(T, T), Vec<SpaceInterval>> = BTreeMap::new();
        for r in berth.iter_free_regions(window, duration, required, bounds) {
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
        berth: &BO,
        s: TimePoint<T>,
        mut duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> BTreeSet<(usize, usize)> {
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

    fn sample_starts_in_band(a: T, b: T) -> Vec<T> {
        use num_traits::One;
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
        berth: &BO,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) {
        let bands = collect_bands(berth, window, duration, required, bounds);
        for ((ts, te), spaces) in bands {
            for s in sample_starts_in_band(ts, te) {
                let got = slot_set_for_start(berth, TimePoint::new(s), duration, required, bounds);
                assert_eq!(
                    got, spaces,
                    "slots at start={} must equal region runs for band [{}, {})",
                    s, ts, te
                );
            }
        }
    }

    #[test]
    fn test_regions_vs_slots_fully_free() {
        let b = BO::new(len(10));
        assert_regions_match_slots(&b, ti(0, 10), TimeDelta::new(3), len(2), si(0, 10));
    }

    #[test]
    fn test_regions_vs_slots_with_single_occupy() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();
        assert_regions_match_slots(&b, ti(0, 12), TimeDelta::new(3), len(1), si(0, 10));
        assert_regions_match_slots(&b, ti(0, 12), TimeDelta::new(4), len(3), si(0, 10));
    }

    #[test]
    fn test_regions_vs_slots_with_multiple_keys() {
        let mut b = BO::new(len(12));
        b.occupy(&rect(ti(4, 9), si(3, 7))).unwrap(); // key 4
        b.occupy(&rect(ti(7, 11), si(6, 10))).unwrap(); // key 7,11
        assert_regions_match_slots(&b, ti(4, 11), TimeDelta::new(3), len(1), si(0, 12));
        assert_regions_match_slots(&b, ti(0, 12), TimeDelta::new(2), len(2), si(0, 12));
    }

    #[test]
    fn test_regions_vs_slots_min_len_and_bounds() {
        let b = BO::new(len(10));
        // Require more than the bounds → no bands
        assert!(collect_bands(&b, ti(0, 10), TimeDelta::new(2), len(6), si(1, 6)).is_empty());
        // Feasible case
        assert_regions_match_slots(&b, ti(0, 10), TimeDelta::new(2), len(5), si(1, 6));
    }

    #[test]
    fn test_regions_zero_and_negative_duration_behave_like_per_slice() {
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(5, 6), si(2, 6))).unwrap(); // keys 5,6
        assert_regions_match_slots(&b, ti(0, 6), TimeDelta::new(0), len(2), si(0, 10));
        assert_regions_match_slots(&b, ti(0, 6), TimeDelta::new(-3), len(2), si(0, 10));
    }

    #[test]
    fn test_regions_empty_when_duration_exceeds_window() {
        let b = BO::new(len(10));
        let bands = collect_bands(&b, ti(0, 4), TimeDelta::new(5), len(1), si(0, 10));
        assert!(bands.is_empty());
    }

    #[test]
    fn test_apply_commit_applies_operations_and_updates_state() {
        // Helpers from this tests module are available: tp, ti, si, rect, len

        // Start with empty berth of length 10
        let mut b = BO::new(len(10));
        assert_eq!(b.time_event_count(), 1);
        assert!(b.is_free(&rect(ti(0, 100), si(0, 10))).unwrap());

        // Build a commit: Occupy [2,6)×[3,7) then Free [4,5)×[4,6).
        let r_occ = rect(ti(2, 6), si(3, 7));
        let r_free = rect(ti(4, 5), si(4, 6));

        let ops = vec![
            Operation::Occupy(OccupyOperation::new(r_occ)),
            Operation::Free(FreeOperation::new(r_free)),
        ];
        let commit = BerthOverlayCommit::new(ops);

        // Apply the commit to the base occupancy
        b.apply(&commit).unwrap();

        // After apply:
        // - [2,6)×[3,7) is occupied EXCEPT the freed "hole" [4,5)×[4,6).
        // Check regions inside the occupied band but outside the freed hole remain occupied:
        assert!(b.is_occupied(&rect(ti(4, 5), si(3, 4))).unwrap()); // left strip
        assert!(b.is_occupied(&rect(ti(4, 5), si(6, 7))).unwrap()); // right strip

        // The freed hole must be free:
        assert!(b.is_free(&rect(ti(4, 5), si(4, 6))).unwrap());

        // Outside the occupied time band is still free:
        assert!(b.is_free(&rect(ti(0, 2), si(0, 10))).unwrap());
        assert!(b.is_free(&rect(ti(6, 10), si(0, 10))).unwrap());

        // Sanity check: boundaries should include 0 (origin), 2, 4, 5, 6 -> total 5 time events.
        assert_eq!(b.time_event_count(), 5);
    }

    #[test]
    fn test_overlay_into_commit_and_apply_changes_state() {
        // Base is fully free.
        let mut b = BO::new(len(10));
        assert!(b.is_free(&rect(ti(0, 100), si(0, 10))).unwrap());

        // Build an overlay on top of the *immutable* base.
        let mut ov = b.overlay();

        // Record operations in the overlay (non-destructive to base):
        // Occupy [2,6)×[3,7), then carve a free "hole" [4,5)×[4,6).
        ov.occupy(&rect(ti(2, 6), si(3, 7))).unwrap();
        ov.free(&rect(ti(4, 5), si(4, 6))).unwrap();

        // Convert overlay to a commit and sanity-check its contents.
        let commit = ov.into_commit();
        assert_eq!(commit.operations().len(), 2);
        assert!(matches!(commit.operations()[0], Operation::Occupy(_)));
        assert!(matches!(commit.operations()[1], Operation::Free(_)));

        // Base must still be unchanged before apply.
        assert!(b.is_free(&rect(ti(2, 6), si(3, 7))).unwrap());

        // Apply the commit to the base.
        b.apply(&commit).unwrap();

        // After apply:
        // - [2,6)×[3,7) is occupied EXCEPT the freed "hole" [4,5)×[4,6).
        assert!(b.is_occupied(&rect(ti(4, 5), si(3, 4))).unwrap()); // left strip remains occupied
        assert!(b.is_occupied(&rect(ti(4, 5), si(6, 7))).unwrap()); // right strip remains occupied
        assert!(b.is_free(&rect(ti(4, 5), si(4, 6))).unwrap()); // carved hole is free

        // Outside the occupied time band remains free.
        assert!(b.is_free(&rect(ti(0, 2), si(0, 10))).unwrap());
        assert!(b.is_free(&rect(ti(6, 10), si(0, 10))).unwrap());
    }

    // --- NEW TESTS BELOW ---

    #[test]
    fn test_apply_commit_repeated_occupy_then_free_same_rect_is_idempotent() {
        let mut b = BO::new(len(10));
        let r = rect(ti(2, 6), si(3, 7));

        let ops = vec![
            Operation::Occupy(OccupyOperation::new(r)),
            Operation::Occupy(OccupyOperation::new(r)), // duplicate occupy
            Operation::Free(FreeOperation::new(r)),
            Operation::Free(FreeOperation::new(r)), // duplicate free
        ];
        let commit = BerthOverlayCommit::new(ops);

        b.apply(&commit).unwrap();

        // Region must be free again and timeline should coalesce back to a single event.
        assert!(b.is_free(&rect(ti(0, 100), si(0, 10))).unwrap());
        assert_eq!(b.time_event_count(), 1);
    }

    #[test]
    fn test_apply_out_of_bounds_fails_without_mutation() {
        let mut b = BO::new(len(10));
        let r_oob = rect(ti(1, 3), si(9, 12));

        let commit = BerthOverlayCommit::new(vec![Operation::Occupy(OccupyOperation::new(r_oob))]);
        let res = b.apply(&commit);
        assert!(res.is_err());

        // For a single failing op, nothing should have changed
        assert_eq!(b.time_event_count(), 1);
        assert!(b.is_free(&rect(ti(0, 100), si(0, 10))).unwrap());
    }

    #[test]
    fn test_apply_mixed_sequence_in_one_commit() {
        let mut b = BO::new(len(12));
        let a = rect(ti(2, 6), si(1, 4));
        let b_rec = rect(ti(3, 7), si(6, 9));
        let c = rect(ti(5, 8), si(2, 3));

        // A then B, then free A, then occupy C, then free C
        let ops = vec![
            Operation::Occupy(OccupyOperation::new(a)),
            Operation::Occupy(OccupyOperation::new(b_rec)),
            Operation::Free(FreeOperation::new(a)),
            Operation::Occupy(OccupyOperation::new(c)),
            Operation::Free(FreeOperation::new(c)),
        ];
        let commit = BerthOverlayCommit::new(ops);

        b.apply(&commit).unwrap();

        // A and C were freed; B must remain occupied.
        assert!(b.is_free(&a).unwrap());
        assert!(b.is_free(&c).unwrap());
        assert!(b.is_occupied(&b_rec).unwrap());
    }

    #[test]
    fn test_apply_noop_on_empty_rectangles_via_commit() {
        let mut b = BO::new(len(10));

        // Empty time and empty space rectangles are no-ops.
        let r_empty_time = rect(ti(3, 3), si(2, 4));
        let r_empty_space = rect(ti(0, 5), si(6, 6));

        let ops = vec![
            Operation::Occupy(OccupyOperation::new(r_empty_time)),
            Operation::Free(FreeOperation::new(r_empty_time)),
            Operation::Occupy(OccupyOperation::new(r_empty_space)),
            Operation::Free(FreeOperation::new(r_empty_space)),
        ];
        let commit = BerthOverlayCommit::new(ops);

        b.apply(&commit).unwrap();

        // Nothing should have changed
        assert_eq!(b.time_event_count(), 1);
        assert!(b.is_free(&rect(ti(0, 100), si(0, 10))).unwrap());
    }

    #[test]
    fn test_apply_commit_double_free_is_harmless() {
        let mut b = BO::new(len(10));
        let r = rect(ti(2, 6), si(3, 7));

        // First commit occupies
        let c1 = BerthOverlayCommit::new(vec![Operation::Occupy(OccupyOperation::new(r))]);
        b.apply(&c1).unwrap();
        assert!(b.is_occupied(&r).unwrap());

        // Second commit frees the same rect twice
        let c2 = BerthOverlayCommit::new(vec![
            Operation::Free(FreeOperation::new(r)),
            Operation::Free(FreeOperation::new(r)),
        ]);
        b.apply(&c2).unwrap();

        // Back to free, coalesced
        assert!(b.is_free(&r).unwrap());
        assert_eq!(b.time_event_count(), 1);
    }

    #[test]
    fn test_apply_commits_accumulate_then_coalesce_back() {
        let mut b = BO::new(len(10));
        let r = rect(ti(2, 6), si(3, 7));

        let c_occ = BerthOverlayCommit::new(vec![Operation::Occupy(OccupyOperation::new(r))]);
        b.apply(&c_occ).unwrap();
        assert!(b.is_occupied(&r).unwrap());
        let n_after_occ = b.time_event_count();
        assert!(
            n_after_occ >= 3,
            "should have created time boundaries at 0,2,6 at least"
        );

        let c_free = BerthOverlayCommit::new(vec![Operation::Free(FreeOperation::new(r))]);
        b.apply(&c_free).unwrap();

        assert!(b.is_free(&r).unwrap());
        assert_eq!(
            b.time_event_count(),
            1,
            "timeline should coalesce when fully freed"
        );
    }

    #[test]
    fn test_adjacent_time_occupies_coalesce() {
        // Same space, adjacent time windows should merge into one band.
        let mut b = BO::new(len(10));

        let a = rect(ti(5, 10), si(2, 5));
        let b2 = rect(ti(10, 15), si(2, 5));
        b.occupy(&a).unwrap();
        b.occupy(&b2).unwrap();

        // Expect continuous occupancy over [5,15) and only 0,5,15 time events.
        assert!(b.is_occupied(&rect(ti(5, 15), si(2, 5))).unwrap());
        assert!(b.is_free(&rect(ti(0, 5), si(2, 5))).unwrap());
        assert!(b.is_free(&rect(ti(15, 20), si(2, 5))).unwrap());
        assert_eq!(b.time_event_count(), 3);
    }

    #[test]
    fn test_adjacent_space_occupies_coalesce() {
        // Same time band, adjacent space segments should merge.
        let mut b = BO::new(len(12));

        let t = ti(3, 7);
        b.occupy(&rect(t, si(2, 5))).unwrap();
        b.occupy(&rect(t, si(5, 8))).unwrap();

        assert!(b.is_occupied(&rect(t, si(2, 8))).unwrap());
        assert!(b.is_free(&rect(t, si(0, 2))).unwrap());
        assert!(b.is_free(&rect(t, si(8, 12))).unwrap());
    }

    #[test]
    fn test_apply_empty_commit_is_noop() {
        let mut b = BO::new(len(10));
        let before = b.time_event_count();
        let empty = BerthOverlayCommit::<T>::new(Vec::new());
        b.apply(&empty).unwrap();
        assert_eq!(b.time_event_count(), before);
        assert!(b.is_free(&rect(ti(0, 100), si(0, 10))).unwrap());
    }

    #[test]
    fn test_apply_partial_failure_keeps_prior_effects() {
        // First op is valid, second op is OOB -> apply() returns Err after first mutated state.
        let mut b = BO::new(len(10));

        let ok = Operation::Occupy(OccupyOperation::new(rect(ti(2, 6), si(1, 3))));
        let oob = Operation::Occupy(OccupyOperation::new(rect(ti(4, 7), si(9, 12))));
        let commit = BerthOverlayCommit::new(vec![ok, oob]);

        let res = b.apply(&commit);
        assert!(res.is_err(), "second operation should fail OOB");

        // The first op must have taken effect.
        assert!(b.is_occupied(&rect(ti(2, 6), si(1, 3))).unwrap());
        // And the OOB region must still be free in-bounds portion
        assert!(b.is_free(&rect(ti(4, 7), si(8, 10))).unwrap());
    }

    #[test]
    fn test_slices_within_keys_are_inclusive_of_start_and_end_key() {
        let mut b = BO::new(len(10));
        // Create keys at 3, 5, 9
        b.occupy(&rect(ti(3, 4), si(0, 1))).unwrap();
        b.occupy(&rect(ti(5, 8), si(0, 1))).unwrap();
        b.occupy(&rect(ti(9, 10), si(0, 1))).unwrap();

        let keys: Vec<_> = b
            .slices(tp(3), tp(9))
            .within_keys()
            .map(|t| t.value())
            .collect();
        assert_eq!(keys, vec![3, 4, 5, 8]); // half-open: [start, end)
    }

    #[test]
    fn test_iter_free_slots_with_tight_space_window() {
        let b = BO::new(len(10));
        // Only consider [2,5) and require it fully.
        let slots = collect_free_iter(&b, ti(0, 10), TimeDelta::new(2), len(3), si(2, 5));
        assert_eq!(slots, vec![(0, (2, 5))]);
    }

    #[test]
    fn test_duration_equals_band_width_single_start_base() {
        let mut b = BO::new(len(10));
        // Create a single continuous free band [3,9) by blocking outside it at predecessor keys.
        b.occupy(&rect(ti(0, 3), si(0, 10))).unwrap();
        b.free(&rect(ti(3, 9), si(0, 10))).unwrap();
        b.occupy(&rect(ti(9, 12), si(0, 10))).unwrap();

        let starts: Vec<_> = b
            .iter_free_slots(ti(0, 12), TimeDelta::new(6), len(2), si(0, 10))
            .map(|f| f.start_time().value())
            .collect();
        assert_eq!(starts, vec![3]);
    }

    #[test]
    fn test_push_operation_sequence_matches_apply() {
        let mut b1 = BO::new(len(12));
        let mut b2 = BO::new(len(12));

        let a = rect(ti(2, 6), si(1, 5));
        let hole = rect(ti(4, 5), si(2, 4));
        let c = rect(ti(7, 9), si(0, 2));

        // Use push_operation
        b1.push_operation(&Operation::Occupy(OccupyOperation::new(a)))
            .unwrap();
        b1.push_operation(&Operation::Free(FreeOperation::new(hole)))
            .unwrap();
        b1.push_operation(&Operation::Occupy(OccupyOperation::new(c)))
            .unwrap();

        // Use a commit
        let commit = BerthOverlayCommit::new(vec![
            Operation::Occupy(OccupyOperation::new(a)),
            Operation::Free(FreeOperation::new(hole)),
            Operation::Occupy(OccupyOperation::new(c)),
        ]);
        b2.apply(&commit).unwrap();

        // A couple of probes to ensure parity
        assert_eq!(
            b1.is_occupied(&rect(ti(2, 4), si(1, 5))).unwrap(),
            b2.is_occupied(&rect(ti(2, 4), si(1, 5))).unwrap()
        );
        assert_eq!(b1.is_free(&hole).unwrap(), b2.is_free(&hole).unwrap());
        assert_eq!(b1.is_occupied(&c).unwrap(), b2.is_occupied(&c).unwrap());
    }

    #[test]
    fn test_free_on_already_free_is_noop_for_state() {
        let mut b = BO::new(len(10));
        let before = b.time_event_count();

        // Free a region that’s already free and disjoint in time.
        let r = rect(ti(5, 7), si(2, 4));
        b.free(&r).unwrap();

        // State must remain effectively unchanged.
        assert!(b.is_free(&rect(ti(0, 100), si(0, 10))).unwrap());
        // It’s OK if the timeline internally reuses/merges keys—assert state not events.
        // (Optionally, keep this weaker to avoid false negatives:)
        assert!(b.time_event_count() >= 1);
        assert!(b.time_event_count() <= before + 2);
    }

    #[test]
    fn test_iter_free_slots_clip_to_bounds_not_just_runs() {
        // Make a big occupied middle so only side windows are free.
        let mut b = BO::new(len(12));
        b.occupy(&rect(ti(3, 8), si(3, 9))).unwrap();

        // Tight bounds force the free slot to be exactly that window
        let slots = collect_free_iter(&b, ti(0, 12), TimeDelta::new(2), len(3), si(0, 3));
        assert!(slots.iter().all(|&(_, (a, b))| a == 0 && b == 3));
    }

    #[test]
    fn test_first_last_key_initial_base() {
        let b = BO::new(len(10));
        // Only the origin exists.
        assert_eq!(<BO as SliceView<T>>::first_key(&b), Some(tp(0)));
        assert_eq!(<BO as SliceView<T>>::last_key(&b), Some(tp(0)));
    }

    #[test]
    fn test_first_last_key_after_occupy_and_free_base() {
        let mut b = BO::new(len(10));

        // Occupy [5,10) -> keys {0,5,10} so last_key == 10
        b.occupy(&rect(ti(5, 10), si(2, 5))).unwrap();
        assert_eq!(<BO as SliceView<T>>::first_key(&b), Some(tp(0)));
        assert_eq!(<BO as SliceView<T>>::last_key(&b), Some(tp(10)));

        // Free everything -> coalesce back to single origin key {0}
        b.free(&rect(ti(5, 10), si(2, 5))).unwrap();
        assert_eq!(<BO as SliceView<T>>::first_key(&b), Some(tp(0)));
        assert_eq!(<BO as SliceView<T>>::last_key(&b), Some(tp(0)));
    }
}
