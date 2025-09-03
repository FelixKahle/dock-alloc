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
use crate::quay::{Quay, QuayRead, QuayWrite};
use dock_alloc_core::domain::{
    SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use dock_alloc_core::mem::DoubleBuf;
use dock_alloc_model::Problem;
use num_traits::{PrimInt, Signed, Zero};
use std::collections::BTreeMap;
use std::iter::{Copied, Peekable};
use std::marker::PhantomData;
use std::ops::Bound::{self, Excluded, Included, Unbounded};

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

type TimeKeyRange<T> = (Bound<TimePoint<T>>, Bound<TimePoint<T>>);

#[inline]
fn time_key_range<T: PrimInt + Signed>(start: TimePoint<T>, end: TimePoint<T>) -> TimeKeyRange<T> {
    (Bound::Included(start), Bound::Excluded(end))
}

fn strict_predecessor_key<T: PrimInt + Signed, Q>(
    map: &BTreeMap<TimePoint<T>, Q>,
    t: TimePoint<T>,
) -> Option<TimePoint<T>> {
    map.range(..t).next_back().map(|(tp, _)| *tp)
}

#[inline]
fn first_key_after<T: PrimInt + Signed, Q>(
    map: &BTreeMap<TimePoint<T>, Q>,
    t: TimePoint<T>,
) -> Option<TimePoint<T>> {
    map.range((Excluded(t), Unbounded))
        .next()
        .map(|(tp, _)| *tp)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BerthOccupancy<T, Q>
where
    T: PrimInt + Signed,
{
    quay_length: SpaceLength,
    timeline: BTreeMap<TimePoint<T>, Q>,
}

impl<T, Q> BerthOccupancy<T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead + Clone + PartialEq,
{
    #[inline]
    pub fn new(quay_length: SpaceLength) -> Self {
        let mut timeline = BTreeMap::new();
        timeline.insert(TimePoint::new(T::zero()), Q::new(quay_length, true));
        Self {
            quay_length,
            timeline,
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
    pub fn snapshot_at(&self, time_point: TimePoint<T>) -> Option<&Q> {
        self.timeline
            .range(..=time_point)
            .next_back()
            .map(|(_, quay_state)| quay_state)
    }

    #[inline]
    pub fn snapshot_at_mut(&mut self, time_point: TimePoint<T>) -> Option<&mut Q> {
        self.split_at(time_point);
        self.timeline.get_mut(&time_point)
    }

    pub fn is_free(&self, rect: &SpaceTimeRectangle<T>) -> bool {
        if rect.is_empty() {
            return true;
        }
        debug_assert!(self.space_within_quay(rect.space()));
        let ti = rect.time();
        let si = rect.space();
        self.slices_covering(ti)
            .all(|s| !s.quay().check_occupied(si))
    }

    #[inline]
    pub fn is_occupied(&self, rect: &SpaceTimeRectangle<T>) -> bool {
        !self.is_free(rect)
    }

    pub fn iter_slice_free_runs<'a>(
        &'a self,
        time_interval: TimeInterval<T>,
        required_space: SpaceLength,
        search_space: SpaceInterval,
    ) -> impl Iterator<Item = (TimePoint<T>, <Q as QuayRead>::FreeIter<'a>)> + 'a {
        debug_assert!(self.space_within_quay(search_space));
        self.slices_covering(time_interval).map(move |s| {
            (
                s.time(),
                s.quay().iter_free_intervals(required_space, search_space),
            )
        })
    }

    #[inline]
    pub fn slice_predecessor_timepoint(&self, time_point: TimePoint<T>) -> Option<TimePoint<T>> {
        self.timeline
            .range(..=time_point)
            .next_back()
            .map(|(tp, _)| *tp)
    }

    #[inline]
    pub fn iter_timepoints(
        &self,
        interval: TimeInterval<T>,
    ) -> impl Iterator<Item = TimePoint<T>> + '_ {
        let start = interval.start();
        let end = interval.end();
        self.timeline
            .range((Excluded(start), Unbounded))
            .take_while(move |(tp, _)| *tp < &end)
            .map(|(time_key, _)| *time_key)
    }

    #[inline]
    pub fn iter_free(
        &self,
        time_window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> BerthOccupancyFreeIter<'_, T, Q> {
        BerthOccupancyFreeIter::new(self, time_window, duration, required_space, space_window)
    }

    #[inline]
    pub fn space_within_quay(&self, space_interval: SpaceInterval) -> bool {
        let quay_bounds = self.quay_space_interval();
        quay_bounds.contains_interval(&space_interval)
    }

    fn coalesce_range(&mut self, start_time: TimePoint<T>, end_time: TimePoint<T>) {
        if self.timeline.is_empty() {
            return;
        }

        // NOTE: use strict predecessor so we coalesce the key just before `start_time`
        let left_boundary =
            strict_predecessor_key(&self.timeline, start_time).unwrap_or(start_time);
        let right_boundary = first_key_after(&self.timeline, end_time).unwrap_or(end_time);

        // Collect necessary timepoints to avoid borrowing issues during iteration
        // We only need to coalesce at timepoints within [left_boundary, right_boundary]
        // Note: coalescing visits [left_boundary, right_boundary] inclusive;
        // that’s different from the normal half-open operational windows.
        let timepoints_in_range: Vec<_> = self
            .timeline
            .range((Included(left_boundary), Included(right_boundary)))
            .map(|(time_point, _)| *time_point)
            .collect();

        for time_point in timepoints_in_range {
            self.coalesce_at(time_point);
        }
    }

    fn split_at(&mut self, time_point: TimePoint<T>) {
        if self.timeline.contains_key(&time_point) {
            return;
        }
        debug_assert!(
            self.timeline
                .keys()
                .next()
                .is_none_or(|&timepoint| timepoint <= time_point),
            "split_at called with time_point earlier than origin"
        );
        if let Some((_, previous_state)) = self.timeline.range(..=time_point).next_back() {
            self.timeline.insert(time_point, previous_state.clone());
        }
    }

    fn coalesce_at(&mut self, time_point: TimePoint<T>) {
        let Some(current) = self.timeline.get(&time_point) else {
            return;
        };

        let previous_state_is_equal = self
            .timeline
            .range(..time_point)
            .next_back()
            .is_some_and(|(_, prev)| prev == current);

        let next_state_is_equal_or_none = match self
            .timeline
            .range((Excluded(time_point), Unbounded))
            .next()
        {
            None => true,
            Some((_, next)) => next == current,
        };

        if previous_state_is_equal && next_state_is_equal_or_none {
            self.timeline.remove(&time_point);
        }
    }

    #[inline]
    pub fn slices_covering(
        &self,
        interval: TimeInterval<T>,
    ) -> impl Iterator<Item = TimeSliceRef<'_, T, Q>> {
        let start = interval.start();
        let end = interval.end();

        let pred = self
            .timeline
            .range(..=start)
            .next_back()
            .map(|(t, q)| TimeSliceRef { time: *t, quay: q });

        let tail = self
            .timeline
            .range((Excluded(start), Unbounded))
            .take_while(move |(t, _)| *t < &end)
            .map(|(t, q)| TimeSliceRef { time: *t, quay: q });

        pred.into_iter().chain(tail)
    }
}

impl<T, Q> BerthOccupancy<T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead + QuayWrite + Clone + PartialEq,
{
    pub fn occupy(&mut self, rect: &SpaceTimeRectangle<T>) {
        if rect.is_empty() {
            return;
        }

        let time_interval = rect.time();
        let space_interval = rect.space();
        let (start_time, end_time) = (time_interval.start(), time_interval.end());

        debug_assert!(self.space_within_quay(space_interval));

        if self
            .slices_covering(time_interval)
            .all(|s| s.quay().check_occupied(space_interval))
        {
            return;
        }

        self.split_at(start_time);
        self.split_at(end_time);

        for (_, quay_state) in self
            .timeline
            .range_mut(time_key_range(start_time, end_time))
        {
            quay_state.occupy(space_interval);
        }

        self.coalesce_range(start_time, end_time);
    }

    pub fn free(&mut self, rect: &SpaceTimeRectangle<T>) {
        if rect.is_empty() {
            return;
        }

        let time_interval = rect.time();
        let space_interval = rect.space();
        let (start_time, end_time) = (time_interval.start(), time_interval.end());

        debug_assert!(self.space_within_quay(space_interval));

        if self
            .slices_covering(time_interval)
            .all(|s| s.quay().check_free(space_interval))
        {
            return;
        }

        self.split_at(start_time);
        self.split_at(end_time);

        for (_, quay_state) in self
            .timeline
            .range_mut(time_key_range(start_time, end_time))
        {
            quay_state.free(space_interval);
        }

        self.coalesce_range(start_time, end_time);
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

pub struct BerthOccupancyFreeIter<'a, T, Q>
where
    T: PrimInt + Signed + Copy,
    Q: QuayRead,
{
    berth: &'a BerthOccupancy<T, Q>,
    time_window: TimeInterval<T>,
    processing_duration: TimeDelta<T>,
    required_length: SpaceLength,
    search_bounds: SpaceInterval,

    yielded_window_start: bool,
    last_start_time: Option<TimePoint<T>>,
    current_start_time: Option<TimePoint<T>>,

    feasible_runs: DoubleBuf<SpaceInterval>,
    next_emit_index: usize,
}

impl<'a, T, Q> BerthOccupancyFreeIter<'a, T, Q>
where
    T: PrimInt + Signed + Copy,
    Q: QuayRead,
{
    fn new(
        berth: &'a BerthOccupancy<T, Q>,
        time_window: TimeInterval<T>,
        processing_duration: TimeDelta<T>,
        required_length: SpaceLength,
        search_bounds: SpaceInterval,
    ) -> Self {
        Self {
            berth,
            time_window,
            processing_duration,
            required_length,
            search_bounds,
            yielded_window_start: false,
            last_start_time: None,
            current_start_time: None,
            feasible_runs: DoubleBuf::new(),
            next_emit_index: 0,
        }
    }

    fn next_candidate_start_time(&mut self) -> Option<TimePoint<T>> {
        if self.time_window.start() + self.processing_duration > self.time_window.end() {
            return None;
        }
        if !self.yielded_window_start {
            self.yielded_window_start = true;
            let window_start = self.time_window.start();
            self.last_start_time = Some(window_start);
            return Some(window_start);
        }

        let last_emitted = self.last_start_time?;
        if let Some(next_key) = self
            .berth
            .iter_timepoints(TimeInterval::new(last_emitted, self.time_window.end()))
            .next()
            && next_key + self.processing_duration <= self.time_window.end()
        {
            self.last_start_time = Some(next_key);
            return Some(next_key);
        }
        let window_end = self.time_window.end();
        if self.processing_duration.value() == T::zero()
            && last_emitted < window_end
            && self
                .berth
                .slice_predecessor_timepoint(window_end)
                .is_some_and(|tp| tp == window_end)
        {
            self.last_start_time = Some(window_end);
            return Some(window_end);
        }

        None
    }

    fn intersect_source_runs_with_quay_into(
        quay_snapshot: &Q,
        bounds: SpaceInterval,
        required_length: SpaceLength,
        source_runs: &[SpaceInterval],
        destination_runs: &mut Vec<SpaceInterval>,
    ) {
        destination_runs.clear();

        let mut free_run_iter = quay_snapshot
            .iter_free_intervals(required_length, bounds)
            .peekable();

        let mut current_free_run_opt = free_run_iter.next();
        let mut source_index = 0usize;

        while source_index < source_runs.len() {
            let source_run = source_runs[source_index];

            while let Some(free_run) = current_free_run_opt
                && free_run.end() <= source_run.start()
            {
                current_free_run_opt = free_run_iter.next();
            }
            if current_free_run_opt.is_none() {
                break;
            }

            let mut free_run = current_free_run_opt.unwrap();
            while free_run.start() < source_run.end() {
                let intersection_start = if source_run.start().value() >= free_run.start().value() {
                    source_run.start()
                } else {
                    free_run.start()
                };
                let intersection_end = if source_run.end().value() <= free_run.end().value() {
                    source_run.end()
                } else {
                    free_run.end()
                };

                if intersection_end > intersection_start
                    && (intersection_end.value() - intersection_start.value())
                        >= required_length.value()
                {
                    destination_runs.push(SpaceInterval::new(intersection_start, intersection_end));
                }

                if source_run.end() <= free_run.end() {
                    break;
                } else {
                    current_free_run_opt = free_run_iter.next();
                    if current_free_run_opt.is_none() {
                        break;
                    }
                    free_run = current_free_run_opt.unwrap();
                }
            }

            source_index += 1;
        }
    }

    fn build_runs_for_start_time(&mut self, start_time: TimePoint<T>) {
        self.feasible_runs.clear();
        self.next_emit_index = 0;
        self.current_start_time = None;

        let predecessor_timepoint = self
            .berth
            .slice_predecessor_timepoint(start_time)
            .expect("timeline has origin snapshot");

        {
            let quay_snapshot = self
                .berth
                .snapshot_at(predecessor_timepoint)
                .expect("slice timepoint must exist");
            self.feasible_runs.seed_from_iter(
                quay_snapshot.iter_free_intervals(self.required_length, self.search_bounds),
            );
        }

        let end_time = start_time + self.processing_duration;
        for timepoint in self
            .berth
            .iter_timepoints(TimeInterval::new(start_time, end_time))
        {
            if self.feasible_runs.current().is_empty() {
                break;
            }
            let quay_snapshot = self
                .berth
                .snapshot_at(timepoint)
                .expect("slice timepoint must exist");

            let req = self.required_length;
            let bnd = self.search_bounds;
            self.feasible_runs.step(|current_runs, next_runs| {
                Self::intersect_source_runs_with_quay_into(
                    quay_snapshot,
                    bnd,
                    req,
                    current_runs,
                    next_runs,
                );
            });
        }

        if !self.feasible_runs.current().is_empty() {
            self.current_start_time = Some(start_time);
        }
    }
}

impl<'a, T, Q> Iterator for BerthOccupancyFreeIter<'a, T, Q>
where
    T: PrimInt + Signed + Copy,
    Q: QuayRead,
{
    type Item = FreeSlot<T>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(start_time) = self.current_start_time {
                if self.next_emit_index < self.feasible_runs.current().len() {
                    let run = self.feasible_runs.current()[self.next_emit_index];
                    self.next_emit_index += 1;
                    return Some(FreeSlot::new(run, start_time));
                }
                self.current_start_time = None;
            }

            let candidate_start = self.next_candidate_start_time()?;
            if candidate_start + self.processing_duration > self.time_window.end() {
                return None;
            }

            self.build_runs_for_start_time(candidate_start);

            if self.current_start_time.is_none() {
                continue;
            }
        }
    }
}

impl<T, C, Q> From<&Problem<T, C>> for BerthOccupancy<T, Q>
where
    T: PrimInt + Signed + Zero + Copy,
    C: PrimInt + Signed + Zero + Copy,
    Q: Quay,
{
    /// Creates a berth occupancy tracker from a problem with preassigned requests.
    ///
    /// This implementation initializes a berth with the specified quay length and then
    /// marks all preassigned requests as occupied in their assigned time and space intervals.
    /// This provides a starting state for solving scheduling problems with existing commitments.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::occupancy::BerthOccupancy;
    /// use dock_alloc_solver::quay::BTreeMapQuay;
    /// use dock_alloc_model::ProblemBuilder;
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// // Create an empty problem using the builder (in practice, this would have requests)
    /// let problem = ProblemBuilder::<i64, i32>::new(SpaceLength::new(200)).build();
    ///
    /// // Convert to berth occupancy with existing assignments
    /// let berth: BerthOccupancy<i64, BTreeMapQuay> = BerthOccupancy::from(&problem);
    ///
    /// assert_eq!(berth.quay_length(), SpaceLength::new(200));
    /// // The berth now has all preassigned requests marked as occupied
    /// ```
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

#[inline]
fn next_key_after<T: PrimInt + Signed, Q>(
    base: &BTreeMap<TimePoint<T>, Q>,
    overlay_free: &BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    overlay_occ: &BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    after: TimePoint<T>,
) -> Option<TimePoint<T>> {
    let nb = base
        .range((Excluded(after), Unbounded))
        .next()
        .map(|(t, _)| *t);
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

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct SpaceIntervalSet {
    intervals: Vec<SpaceInterval>,
}

impl SpaceIntervalSet {
    #[inline]
    fn new() -> Self {
        Self {
            intervals: Vec::new(),
        }
    }

    #[inline]
    fn with_capacity(capacity: usize) -> Self {
        Self {
            intervals: Vec::with_capacity(capacity),
        }
    }

    #[inline]
    fn from_vec(mut intervals: Vec<SpaceInterval>) -> Self {
        if !intervals.is_empty() {
            Self::coalesce_in_place(&mut intervals);
        }
        Self { intervals }
    }

    #[inline]
    fn len(&self) -> usize {
        self.intervals.len()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.intervals.is_empty()
    }

    #[inline]
    fn as_slice(&self) -> &[SpaceInterval] {
        &self.intervals
    }

    #[inline]
    fn clear(&mut self) {
        self.intervals.clear()
    }

    #[inline]
    fn clear_and_fill_from_iter<I: IntoIterator<Item = SpaceInterval>>(&mut self, iter: I) {
        self.clear();
        for iv in iter {
            self.push_coalesced(iv);
        }
    }

    #[inline]
    fn retain_min_length(&mut self, min_length: SpaceLength) {
        if min_length.value() > 1 {
            self.intervals.retain(|iv| iv.extent() >= min_length);
        }
    }

    #[inline]
    fn covers(&self, required_interval: SpaceInterval) -> bool {
        if required_interval.start() >= required_interval.end() {
            return true;
        }
        let mut cursor = required_interval.start();
        for interval in &self.intervals {
            if interval.end() <= cursor {
                continue;
            }
            if interval.start() > cursor {
                return false;
            }
            cursor = cursor.max(interval.end());
            if cursor >= required_interval.end() {
                return true;
            }
        }
        false
    }

    #[inline]
    fn overlaps(&self, interval_to_check: SpaceInterval) -> bool {
        if self.intervals.is_empty() {
            return false;
        }

        let mut low_index = 0usize;
        let mut high_index = self.intervals.len();
        while low_index < high_index {
            let mid_index = (low_index + high_index) / 2;
            if self.intervals[mid_index].start() < interval_to_check.start() {
                low_index = mid_index + 1;
            } else {
                high_index = mid_index;
            }
        }
        if low_index > 0 && self.intervals[low_index - 1].intersects(&interval_to_check) {
            return true;
        }
        if low_index < self.intervals.len()
            && self.intervals[low_index].intersects(&interval_to_check)
        {
            return true;
        }
        false
    }

    #[inline]
    fn clamped_linear(&self, bounds: SpaceInterval) -> Self {
        if self.is_empty() {
            return Self::new();
        }
        let self_intervals = &self.intervals;
        let mut start_index =
            match self_intervals.binary_search_by_key(&bounds.start(), |interval| interval.end()) {
                Ok(index) | Err(index) => index,
            };

        let mut result_set = Self::with_capacity(4.min(self_intervals.len()));
        while start_index < self_intervals.len()
            && self_intervals[start_index].start() < bounds.end()
        {
            let start_pos = core::cmp::max(self_intervals[start_index].start(), bounds.start());
            let end_pos = core::cmp::min(self_intervals[start_index].end(), bounds.end());
            if start_pos < end_pos {
                result_set
                    .intervals
                    .push(SpaceInterval::new(start_pos, end_pos));
            }
            start_index += 1;
        }
        result_set
    }

    #[inline]
    fn clamped_linear_into(&self, bounds: SpaceInterval, out: &mut Self) {
        out.clear();
        if self.is_empty() {
            return;
        }
        let self_intervals = &self.intervals;
        let mut idx = match self_intervals.binary_search_by_key(&bounds.start(), |i| i.end()) {
            Ok(i) | Err(i) => i,
        };
        while idx < self_intervals.len() && self_intervals[idx].start() < bounds.end() {
            let s = core::cmp::max(self_intervals[idx].start(), bounds.start());
            let e = core::cmp::min(self_intervals[idx].end(), bounds.end());
            if s < e {
                out.intervals.push(SpaceInterval::new(s, e));
            }
            idx += 1;
        }
    }

    #[inline]
    fn push_coalesced(&mut self, new_interval: SpaceInterval) {
        if new_interval.start() >= new_interval.end() {
            return;
        }
        let intervals = &mut self.intervals;
        let mut insertion_index = intervals
            .binary_search_by_key(&new_interval.start(), |i| i.start())
            .unwrap_or_else(|i| i);
        let mut merged_start = new_interval.start();
        let mut merged_end = new_interval.end();
        if insertion_index > 0 && intervals[insertion_index - 1].end() >= merged_start {
            insertion_index -= 1;
            merged_start = intervals[insertion_index].start().min(merged_start);
        }
        let mut merge_scan_index = insertion_index;
        while merge_scan_index < intervals.len()
            && intervals[merge_scan_index].start() <= merged_end
        {
            merged_end = intervals[merge_scan_index].end().max(merged_end);
            merge_scan_index += 1;
        }
        let merged_interval = SpaceInterval::new(merged_start, merged_end);
        if insertion_index == intervals.len() {
            intervals.push(merged_interval);
        } else if merge_scan_index == insertion_index {
            intervals.insert(insertion_index, merged_interval);
        } else {
            intervals[insertion_index] = merged_interval;
            if merge_scan_index > insertion_index + 1 {
                intervals.drain(insertion_index + 1..merge_scan_index);
            }
        }
    }

    #[inline]
    fn union(&self, other: &Self) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }

        let (self_intervals, other_intervals) = (&self.intervals, &other.intervals);
        let mut result_intervals = Vec::with_capacity(self_intervals.len() + other_intervals.len());
        let (mut self_index, mut other_index) = (0usize, 0usize);
        while self_index < self_intervals.len() && other_index < other_intervals.len() {
            let next_interval_to_merge =
                if self_intervals[self_index].start() <= other_intervals[other_index].start() {
                    let interval = self_intervals[self_index];
                    self_index += 1;
                    interval
                } else {
                    let interval = other_intervals[other_index];
                    other_index += 1;
                    interval
                };
            Self::push_and_merge(&mut result_intervals, next_interval_to_merge);
        }
        while self_index < self_intervals.len() {
            Self::push_and_merge(&mut result_intervals, self_intervals[self_index]);
            self_index += 1;
        }
        while other_index < other_intervals.len() {
            Self::push_and_merge(&mut result_intervals, other_intervals[other_index]);
            other_index += 1;
        }
        Self {
            intervals: result_intervals,
        }
    }

    #[inline]
    fn union_into(&self, other: &Self, out: &mut Self) {
        out.intervals.clear();
        if self.is_empty() {
            out.intervals.extend_from_slice(&other.intervals);
            return;
        }
        if other.is_empty() {
            out.intervals.extend_from_slice(&self.intervals);
            return;
        }
        let (a, b) = (&self.intervals, &other.intervals);
        let (mut i, mut j) = (0usize, 0usize);
        while i < a.len() && j < b.len() {
            let next = if a[i].start() <= b[j].start() {
                let v = a[i];
                i += 1;
                v
            } else {
                let v = b[j];
                j += 1;
                v
            };
            Self::push_and_merge(&mut out.intervals, next);
        }
        while i < a.len() {
            Self::push_and_merge(&mut out.intervals, a[i]);
            i += 1;
        }
        while j < b.len() {
            Self::push_and_merge(&mut out.intervals, b[j]);
            j += 1;
        }
    }

    #[inline]
    fn subtract(&self, other: &Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return self.clone();
        }

        let (minuend_intervals, subtrahend_intervals) = (&self.intervals, &other.intervals);
        let mut result_intervals: Vec<SpaceInterval> = Vec::with_capacity(minuend_intervals.len());
        let (mut minuend_index, mut subtrahend_scan_start_index) = (0usize, 0usize);

        while minuend_index < minuend_intervals.len() {
            let mut current_minuend_interval = minuend_intervals[minuend_index];
            while subtrahend_scan_start_index < subtrahend_intervals.len()
                && subtrahend_intervals[subtrahend_scan_start_index].end()
                    <= current_minuend_interval.start()
            {
                subtrahend_scan_start_index += 1;
            }
            let mut subtrahend_index = subtrahend_scan_start_index;
            let mut is_fully_consumed = false;

            while subtrahend_index < subtrahend_intervals.len()
                && subtrahend_intervals[subtrahend_index].start() < current_minuend_interval.end()
            {
                let current_subtrahend_interval = subtrahend_intervals[subtrahend_index];
                if current_subtrahend_interval.start() > current_minuend_interval.start() {
                    result_intervals.push(SpaceInterval::new(
                        current_minuend_interval.start(),
                        current_subtrahend_interval.start(),
                    ));
                }
                if current_subtrahend_interval.end() >= current_minuend_interval.end() {
                    is_fully_consumed = true;
                    break;
                }
                current_minuend_interval = SpaceInterval::new(
                    current_subtrahend_interval.end(),
                    current_minuend_interval.end(),
                );
                subtrahend_index += 1;
            }
            if !is_fully_consumed {
                result_intervals.push(current_minuend_interval);
            }
            subtrahend_scan_start_index = subtrahend_index;
            minuend_index += 1;
        }
        debug_assert!(Self::is_sorted_non_overlapping(&result_intervals));
        Self {
            intervals: result_intervals,
        }
    }

    #[inline]
    fn subtract_into(&self, other: &Self, out: &mut Self) {
        out.intervals.clear();
        if self.is_empty() {
            return;
        }
        if other.is_empty() {
            out.intervals.extend_from_slice(&self.intervals);
            return;
        }

        let (a, b) = (&self.intervals, &other.intervals);
        let (mut i, mut j) = (0usize, 0usize);

        while i < a.len() {
            let mut cur = a[i];
            while j < b.len() && b[j].end() <= cur.start() {
                j += 1;
            }
            let mut jj = j;
            let mut consumed = false;
            while jj < b.len() && b[jj].start() < cur.end() {
                let cut = b[jj];
                if cut.start() > cur.start() {
                    out.intervals
                        .push(SpaceInterval::new(cur.start(), cut.start()));
                }
                if cut.end() >= cur.end() {
                    consumed = true;
                    break;
                }
                cur = SpaceInterval::new(cut.end(), cur.end());
                jj += 1;
            }
            if !consumed {
                out.intervals.push(cur);
            }
            j = jj;
            i += 1;
        }
        debug_assert!(Self::is_sorted_non_overlapping(&out.intervals));
    }

    #[inline]
    fn intersection_into(&self, other: &Self, result_set: &mut Self) {
        if self.is_empty() || other.is_empty() {
            result_set.clear();
            return;
        }
        let (self_intervals, other_intervals) = (&self.intervals, &other.intervals);
        result_set.intervals.clear();
        result_set
            .intervals
            .reserve(self_intervals.len().min(other_intervals.len()));
        let (mut self_index, mut other_index) = (0usize, 0usize);
        while self_index < self_intervals.len() && other_index < other_intervals.len() {
            let intersection_start =
                if self_intervals[self_index].start() > other_intervals[other_index].start() {
                    self_intervals[self_index].start()
                } else {
                    other_intervals[other_index].start()
                };
            let intersection_end =
                if self_intervals[self_index].end() < other_intervals[other_index].end() {
                    self_intervals[self_index].end()
                } else {
                    other_intervals[other_index].end()
                };
            if intersection_start < intersection_end {
                result_set
                    .intervals
                    .push(SpaceInterval::new(intersection_start, intersection_end));
            }
            if self_intervals[self_index].end() < other_intervals[other_index].end() {
                self_index += 1
            } else {
                other_index += 1
            }
        }
        debug_assert!(Self::is_sorted_non_overlapping(&result_set.intervals));
    }

    #[inline]
    fn filter_min_length(mut self, min_length: SpaceLength) -> Self {
        if min_length.value() > 1 {
            self.intervals
                .retain(|interval| interval.extent() >= min_length);
        }
        self
    }

    #[inline]
    fn coalesce_in_place(intervals: &mut Vec<SpaceInterval>) {
        if intervals.len() < 2 {
            return;
        }
        intervals.sort_by_key(|interval| interval.start());
        let mut write_index = 0usize;
        for read_index in 1..intervals.len() {
            if intervals[write_index].end() >= intervals[read_index].start() {
                intervals[write_index] = SpaceInterval::new(
                    intervals[write_index].start(),
                    intervals[write_index]
                        .end()
                        .max(intervals[read_index].end()),
                );
            } else {
                write_index += 1;
                intervals[write_index] = intervals[read_index];
            }
        }
        intervals.truncate(write_index + 1);
        debug_assert!(Self::is_sorted_non_overlapping(intervals));
    }

    #[inline]
    fn push_and_merge(intervals: &mut Vec<SpaceInterval>, interval_to_push: SpaceInterval) {
        if let Some(last) = intervals.last_mut()
            && last.end() >= interval_to_push.start()
        {
            *last = SpaceInterval::new(last.start(), last.end().max(interval_to_push.end()));
            return;
        }
        intervals.push(interval_to_push);
    }

    #[inline]
    #[cfg(debug_assertions)]
    fn is_sorted_non_overlapping(intervals: &[SpaceInterval]) -> bool {
        intervals
            .windows(2)
            .all(|window| window[0].end() < window[1].start())
    }

    #[inline]
    #[cfg(not(debug_assertions))]
    fn is_sorted_non_overlapping(_intervals: &[SpaceInterval]) -> bool {
        true
    }
}

impl From<Vec<SpaceInterval>> for SpaceIntervalSet {
    fn from(intervals: Vec<SpaceInterval>) -> Self {
        Self::from_vec(intervals)
    }
}

impl FromIterator<SpaceInterval> for SpaceIntervalSet {
    fn from_iter<I: IntoIterator<Item = SpaceInterval>>(iter: I) -> Self {
        let mut intervals: Vec<SpaceInterval> = iter.into_iter().collect();
        if !intervals.is_empty() {
            Self::coalesce_in_place(&mut intervals);
        }
        Self { intervals }
    }
}

impl core::ops::Deref for SpaceIntervalSet {
    type Target = [SpaceInterval];
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.intervals
    }
}

impl<'a> IntoIterator for &'a SpaceIntervalSet {
    type Item = &'a SpaceInterval;
    type IntoIter = core::slice::Iter<'a, SpaceInterval>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.intervals.iter()
    }
}

impl<'a> IntoIterator for &'a mut SpaceIntervalSet {
    type Item = &'a mut SpaceInterval;
    type IntoIter = core::slice::IterMut<'a, SpaceInterval>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.intervals.iter_mut()
    }
}

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
    base: SpaceIntervalSet,
    adj: SpaceIntervalSet,
    clamp_buf: SpaceIntervalSet,
    union_buf: SpaceIntervalSet,
    sub_buf: SpaceIntervalSet,
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
            base: SpaceIntervalSet::new(),
            adj: SpaceIntervalSet::new(),
            clamp_buf: SpaceIntervalSet::new(),
            union_buf: SpaceIntervalSet::new(),
            sub_buf: SpaceIntervalSet::new(),
        }
    }

    fn compute(&mut self) {
        if self.computed {
            return;
        }
        self.computed = true;

        let keys =
            KeysUnion::<'a, T>::new(&self.overlay.free_by_time, &self.overlay.occupied_by_time);

        let mut first = true;
        let mut saw_any_key = false;

        for tp in keys {
            saw_any_key = true;

            // base free runs for this slice within bounds (no temp Vec; coalescing as we go)
            let qs = match self.overlay.berth_occupancy.snapshot_at(tp) {
                Some(q) => q,
                None => continue,
            };
            self.base
                .clear_and_fill_from_iter(qs.iter_free_intervals(SpaceLength::new(1), self.bounds));

            // apply overlay free additions
            self.adj.clear();
            if let Some(f) = self.overlay.free_by_time.get(&tp) {
                self.clamp_buf.clear();
                f.clamped_linear_into(self.bounds, &mut self.clamp_buf);
                self.base.union_into(&self.clamp_buf, &mut self.union_buf);
            } else {
                // no additions → union_buf := base
                self.union_buf = core::mem::take(&mut self.base);
            }

            // then subtract overlay occupied
            if let Some(o) = self.overlay.occupied_by_time.get(&tp) {
                o.clamped_linear_into(self.bounds, &mut self.clamp_buf);
                self.union_buf
                    .subtract_into(&self.clamp_buf, &mut self.sub_buf);
                core::mem::swap(&mut self.adj, &mut self.sub_buf);
            } else {
                core::mem::swap(&mut self.adj, &mut self.union_buf);
            }

            // intersect with accumulator
            if first {
                self.acc = core::mem::take(&mut self.adj);
                first = false;
            } else {
                self.tmp.clear();
                self.acc.intersection_into(&self.adj, &mut self.tmp);
                core::mem::swap(&mut self.acc, &mut self.tmp);
                if self.acc.is_empty() {
                    break;
                }
            }
        }

        // No overlay keys → neutral element: just the bounds (then filter by required)
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
            .push_coalesced(space);
    }

    pub fn occupy(&mut self, rect: &SpaceTimeRectangle<T>) {
        let time_window = rect.time();
        let space_interval = rect.space();

        if let Some(predecessor_timepoint) = self
            .berth_occupancy
            .slice_predecessor_timepoint(time_window.start())
        {
            self.add_occupy(predecessor_timepoint, space_interval);
        }
        for timepoint in self.berth_occupancy.iter_timepoints(time_window) {
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
        let space_interval = rect.space();

        if let Some(pred) = self
            .berth_occupancy
            .slice_predecessor_timepoint(time_window.start())
        {
            self.remove_occupy(pred, space_interval);
        }
        for tp in self.berth_occupancy.iter_timepoints(time_window) {
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
            .push_coalesced(space);
    }

    pub fn free(&mut self, rect: &SpaceTimeRectangle<T>) {
        let time_window = rect.time();
        let space_interval = rect.space();

        if let Some(predecessor_timepoint) = self
            .berth_occupancy
            .slice_predecessor_timepoint(time_window.start())
        {
            self.add_free(predecessor_timepoint, space_interval);
        }
        for timepoint in self.berth_occupancy.iter_timepoints(time_window) {
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
        let space_interval = rect.space();

        if let Some(pred) = self
            .berth_occupancy
            .slice_predecessor_timepoint(time_window.start())
        {
            self.remove_free(pred, space_interval);
        }
        for tp in self.berth_occupancy.iter_timepoints(time_window) {
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
    ) -> OverlayFreeIter<'brand, 'a, T, Q> {
        OverlayFreeIter::new(self, time_window, duration, required_space, space_window)
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
        pred.into_iter()
            .chain(self.berth_occupancy.iter_timepoints(time_window))
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
            let clamped_free_intervals = free_set.clamped_linear(bounds);
            if !clamped_free_intervals.is_empty() {
                result_set = result_set.union(&clamped_free_intervals);
            }
        }
        if let Some(occupied_set) = self.occupied_by_time.get(&timepoint) {
            let clamped_occupied_intervals = occupied_set.clamped_linear(bounds);
            if !clamped_occupied_intervals.is_empty() {
                result_set = result_set.subtract(&clamped_occupied_intervals);
            }
        }
        result_set.filter_min_length(min_length)
    }
}

pub struct OverlayFreeIter<'brand, 'a, T, Q>
where
    T: PrimInt + Signed + Copy,
    Q: QuayRead,
{
    overlay: &'a BerthOccupancyOverlay<'brand, 'a, T, Q>,
    time_window: TimeInterval<T>,
    duration: TimeDelta<T>,
    required: SpaceLength,
    bounds: SpaceInterval,

    yielded_window_start: bool,
    last_start: Option<TimePoint<T>>,
    current_start: Option<TimePoint<T>>,

    runs: DoubleBuf<SpaceInterval>,
    emit_idx: usize,
}

impl<'brand, 'a, T, Q> OverlayFreeIter<'brand, 'a, T, Q>
where
    T: PrimInt + Signed + Copy,
    Q: QuayRead,
{
    #[inline]
    fn new(
        overlay: &'a BerthOccupancyOverlay<'brand, 'a, T, Q>,
        time_window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> Self {
        Self {
            overlay,
            time_window,
            duration,
            required,
            bounds,
            yielded_window_start: false,
            last_start: None,
            current_start: None,
            runs: DoubleBuf::new(),
            emit_idx: 0,
        }
    }

    fn next_candidate_start(&mut self) -> Option<TimePoint<T>> {
        if self.time_window.start() + self.duration > self.time_window.end() {
            return None;
        }
        if !self.yielded_window_start {
            self.yielded_window_start = true;
            let t0 = self.time_window.start();
            self.last_start = Some(t0);
            return Some(t0);
        }

        let last = self.last_start?;
        let wnd_end = self.time_window.end();
        let next = next_key_after(
            &self.overlay.berth_occupancy.timeline,
            &self.overlay.free_by_time,
            &self.overlay.occupied_by_time,
            last,
        );

        if let Some(tp) = next {
            if tp + self.duration <= wnd_end {
                self.last_start = Some(tp);
                return Some(tp);
            }
        }

        if self.duration.value() == T::zero() && last < wnd_end {
            let berth_has_end = self
                .overlay
                .berth_occupancy
                .slice_predecessor_timepoint(wnd_end)
                .is_some_and(|tp| tp == wnd_end);
            let overlay_has_end = self.overlay.free_by_time.contains_key(&wnd_end)
                || self.overlay.occupied_by_time.contains_key(&wnd_end);
            if berth_has_end || overlay_has_end {
                self.last_start = Some(wnd_end);
                return Some(wnd_end);
            }
        }

        None
    }

    fn intersect_with_set_into(
        required: SpaceLength,
        source: &[SpaceInterval],
        set: &[SpaceInterval],
        out: &mut Vec<SpaceInterval>,
    ) {
        out.clear();
        let mut i = 0usize;
        let mut j = 0usize;
        while i < source.len() && j < set.len() {
            let a = source[i];
            let b = set[j];

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

            if a.end() < b.end() { i += 1 } else { j += 1 }
        }
    }

    fn build_runs_for_start(&mut self, start: TimePoint<T>) {
        self.runs.clear();
        self.emit_idx = 0;
        self.current_start = None;

        let berth = self.overlay.berth_occupancy;
        let pred = berth
            .slice_predecessor_timepoint(start)
            .expect("timeline has origin snapshot");

        let qs = berth.snapshot_at(pred).expect("slice timepoint must exist");
        let base =
            SpaceIntervalSet::from_iter(qs.iter_free_intervals(SpaceLength::new(1), self.bounds));

        let have_start_overlay = self.overlay.free_by_time.contains_key(&start)
            || self.overlay.occupied_by_time.contains_key(&start);

        let adj_seed = if have_start_overlay {
            self.overlay
                .adjust_runs(start, base, self.bounds, self.required)
        } else {
            self.overlay
                .adjust_runs(pred, base, self.bounds, self.required)
        };

        self.runs
            .seed_from_iter(adj_seed.as_slice().iter().copied());
        if self.runs.current().is_empty() {
            return;
        }

        let qs_start = berth
            .snapshot_at(start)
            .expect("slice timepoint must exist");
        let base_start = SpaceIntervalSet::from_iter(
            qs_start.iter_free_intervals(SpaceLength::new(1), self.bounds),
        );
        let adj_start = self
            .overlay
            .adjust_runs(start, base_start, self.bounds, self.required);

        let req = self.required;
        let adj_slice = adj_start.as_slice();
        self.runs.step(|cur, next| {
            Self::intersect_with_set_into(req, cur, adj_slice, next);
        });
        if self.runs.current().is_empty() {
            return;
        }
        let end = start + self.duration;

        let mut cursor = start;
        loop {
            let next_tp = next_key_after(
                &berth.timeline,
                &self.overlay.free_by_time,
                &self.overlay.occupied_by_time,
                cursor,
            );
            let Some(tp) = next_tp else { break };
            if tp >= end {
                break;
            }
            cursor = tp;

            if self.runs.current().is_empty() {
                break;
            }

            let qs_tp = berth.snapshot_at(tp).expect("slice timepoint must exist");
            let base_tp = SpaceIntervalSet::from_iter(
                qs_tp.iter_free_intervals(SpaceLength::new(1), self.bounds),
            );
            let adj_tp = self
                .overlay
                .adjust_runs(tp, base_tp, self.bounds, self.required);

            let req = self.required;
            let adj_slice = adj_tp.as_slice();
            self.runs.step(|cur, next| {
                Self::intersect_with_set_into(req, cur, adj_slice, next);
            });
        }

        if !self.runs.current().is_empty() {
            self.current_start = Some(start);
        }
    }
}

impl<'brand, 'a, T, Q> Iterator for OverlayFreeIter<'brand, 'a, T, Q>
where
    T: PrimInt + Signed + Copy,
    Q: QuayRead,
{
    type Item = FreeSlot<T>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // Emit pending runs for the current start time
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
    fn test_snapshot_at_mut_splits_on_demand() {
        let quay_length = len(8);
        let mut berth_occupancy = BO::new(quay_length);

        assert_eq!(berth_occupancy.time_event_count(), 1);

        {
            // Split at t=7 by asking for a mutable snapshot
            let quay_snapshot = berth_occupancy
                .snapshot_at_mut(tp(7))
                .expect("should exist");

            // Verify the cloned state is still fully free
            assert!(quay_snapshot.check_free(si(0, 8)));
            // `quay_snapshot` is dropped at the end of this block, releasing the mutable borrow
        }

        // Now it's legal to immutably borrow `berth_occupancy` again
        assert_eq!(berth_occupancy.time_event_count(), 2);
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

        // At t=5 they just touch; occupancy should be continuous across [2,7)
        assert!(berth_occupancy.is_occupied(&rect(ti(2, 7), si(3, 6))));
        // Boundaries: 0,2,5,7
        assert_eq!(berth_occupancy.time_event_count(), 4);
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
    fn set_coalescing_and_push() {
        // from_vec should coalesce and sort
        let set = SpaceIntervalSet::from_vec(vec![si(3, 6), si(1, 4), si(8, 10), si(6, 7)]);
        // Expect [1,7) and [8,10)
        assert_eq!(set.as_slice(), &[si(1, 7), si(8, 10)]);

        // push_coalesced maintains ordering and merging
        let mut set2 = SpaceIntervalSet::new();
        set2.push_coalesced(si(5, 7));
        set2.push_coalesced(si(1, 3));
        set2.push_coalesced(si(3, 5));
        set2.push_coalesced(si(9, 11));
        set2.push_coalesced(si(8, 9));
        assert_eq!(set2.as_slice(), &[si(1, 7), si(8, 11)]);
    }

    #[test]
    fn set_overlaps_and_covers() {
        let set = SpaceIntervalSet::from_vec(vec![si(0, 3), si(5, 8)]);
        assert!(set.overlaps(si(1, 2)));
        assert!(set.overlaps(si(2, 6))); // touches both ranges via overlap with [0,3) first
        assert!(set.overlaps(si(7, 9)));
        assert!(!set.overlaps(si(3, 5))); // gap

        assert!(set.covers(si(1, 2)));
        assert!(!set.covers(si(2, 6))); // gap breaks coverage
        assert!(set.covers(si(5, 8)));
        assert!(set.covers(si(0, 0))); // vacuously true for empty
    }

    #[test]
    fn set_clamp_and_clamp_linear_into() {
        let set = SpaceIntervalSet::from_vec(vec![si(0, 2), si(4, 7), si(9, 12)]);
        let clamped = set.clamped_linear(si(1, 10));
        assert_eq!(clamped.as_slice(), &[si(1, 2), si(4, 7), si(9, 10)]);

        let mut out = SpaceIntervalSet::new();
        set.clamped_linear_into(si(1, 10), &mut out);
        assert_eq!(out.as_slice(), &[si(1, 2), si(4, 7), si(9, 10)]);
    }

    #[test]
    fn set_union_and_union_into() {
        let a = SpaceIntervalSet::from_vec(vec![si(0, 3), si(5, 6)]);
        let b = SpaceIntervalSet::from_vec(vec![si(2, 5), si(8, 9)]);
        let u = a.union(&b);
        assert_eq!(u.as_slice(), &[si(0, 6), si(8, 9)]);

        let mut out = SpaceIntervalSet::new();
        a.union_into(&b, &mut out);
        assert_eq!(out.as_slice(), &[si(0, 6), si(8, 9)]);
    }

    #[test]
    fn set_subtract_and_subtract_into() {
        let a = SpaceIntervalSet::from_vec(vec![si(0, 10), si(12, 15)]);
        let b = SpaceIntervalSet::from_vec(vec![si(3, 4), si(8, 13)]);

        let s = a.subtract(&b);
        assert_eq!(s.as_slice(), &[si(0, 3), si(4, 8), si(13, 15)]);

        let mut out = SpaceIntervalSet::new();
        a.subtract_into(&b, &mut out);
        assert_eq!(out.as_slice(), &[si(0, 3), si(4, 8), si(13, 15)]);
    }

    #[test]
    fn set_retain_and_filter_min_length() {
        // retain_min_length (in-place, >= semantics)
        let mut set = SpaceIntervalSet::from_vec(vec![si(0, 3), si(5, 9), si(10, 11)]);
        set.retain_min_length(len(4)); // keep intervals with extent >= 4
        assert_eq!(set.as_slice(), &[si(5, 9)]);

        // filter_min_length (by value, >= semantics)
        let set2 = SpaceIntervalSet::from_vec(vec![si(0, 3), si(4, 6), si(10, 14)]);
        let filtered = set2.filter_min_length(len(3));
        assert_eq!(filtered.as_slice(), &[si(0, 3), si(10, 14)]);

        // both intervals have extent 2, so with min len 3 the result is empty
        let filtered2 =
            SpaceIntervalSet::from_vec(vec![si(0, 2), si(4, 6)]).filter_min_length(len(3));
        assert!(filtered2.as_slice().is_empty());
    }

    #[test]
    fn set_clear_and_fill_from_iter_and_into_iter() {
        let mut set = SpaceIntervalSet::new();
        // Out-of-order, overlapping -> should coalesce into [0,5)
        set.clear_and_fill_from_iter(vec![si(1, 3), si(0, 1), si(2, 5)]);
        assert_eq!(set.as_slice(), &[si(0, 5)]);

        // IntoIterator for &SpaceIntervalSet
        let collected: Vec<_> = (&set).into_iter().copied().collect();
        assert_eq!(collected, vec![si(0, 5)]);
    }

    #[test]
    fn keys_union_merges_sorted_without_duplicates() {
        // Build dummy maps keyed by TimePoint<T>
        let mut free = BTreeMap::new();
        let mut occ = BTreeMap::new();
        free.insert(tp(0), SpaceIntervalSet::from_vec(vec![si(0, 1)]));
        free.insert(tp(10), SpaceIntervalSet::from_vec(vec![si(0, 1)]));
        free.insert(tp(20), SpaceIntervalSet::from_vec(vec![si(0, 1)]));
        occ.insert(tp(5), SpaceIntervalSet::from_vec(vec![si(0, 1)]));
        occ.insert(tp(10), SpaceIntervalSet::from_vec(vec![si(0, 1)]));
        occ.insert(tp(30), SpaceIntervalSet::from_vec(vec![si(0, 1)]));

        let merged: Vec<_> = KeysUnion::<'_, T>::new(&free, &occ).collect();
        assert_eq!(merged, vec![tp(0), tp(5), tp(10), tp(20), tp(30)]);
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
            .iter_timepoints(ti(5, 10))
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
    fn set_covers_empty_interval_vacuously_true() {
        let s = SpaceIntervalSet::from_vec(vec![si(2, 4)]);
        assert!(s.covers(si(3, 3))); // empty
        assert!(s.covers(si(2, 3)));
        assert!(!s.covers(si(1, 3)));
    }

    #[test]
    fn set_overlaps_edge_touching_is_false_half_open() {
        let s = SpaceIntervalSet::from_vec(vec![si(1, 3)]);
        assert!(s.overlaps(si(2, 4))); // overlaps
        assert!(!s.overlaps(si(3, 5))); // touches at 3 only ⇒ false
    }

    #[test]
    fn set_clamped_linear_into_empty_and_bounds_outside() {
        let mut out = SpaceIntervalSet::new();
        SpaceIntervalSet::new().clamped_linear_into(si(0, 10), &mut out);
        assert!(out.is_empty());

        let s = SpaceIntervalSet::from_vec(vec![si(10, 12)]);
        s.clamped_linear_into(si(0, 10), &mut out);
        assert!(out.is_empty());
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
