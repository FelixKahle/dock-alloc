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

use crate::quay::{Quay, QuayRead, QuayWrite};
use dock_alloc_core::domain::{
    SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use dock_alloc_core::mem::DoubleBuf;
use dock_alloc_model::Problem;
use num_traits::{PrimInt, Signed, Zero};
use std::collections::BTreeMap;
use std::ops::Bound::{Excluded, Included, Unbounded};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

    pub fn is_free(&self, time_interval: TimeInterval<T>, space_interval: SpaceInterval) -> bool {
        if time_interval.is_empty() || space_interval.is_empty() {
            return true;
        }
        debug_assert!(self.space_within_quay(space_interval));

        for time_point in self.iter_timepoints_covering(time_interval.start(), time_interval.end())
        {
            let quay_state = self
                .timeline
                .get(&time_point)
                .expect("slice timepoint must exist");
            if quay_state.check_occupied(space_interval) {
                return false;
            }
        }
        true
    }

    #[inline]
    pub fn is_occupied(
        &self,
        time_interval: TimeInterval<T>,
        space_interval: SpaceInterval,
    ) -> bool {
        !self.is_free(time_interval, space_interval)
    }

    pub fn iter_free_per_slice<'a>(
        &'a self,
        time_interval: TimeInterval<T>,
        required_space: SpaceLength,
        search_space: SpaceInterval,
    ) -> impl Iterator<Item = (TimePoint<T>, <Q as QuayRead>::FreeIter<'a>)> + 'a {
        debug_assert!(self.space_within_quay(search_space));

        let timepoints = self.iter_timepoints_covering(time_interval.start(), time_interval.end());
        timepoints.map(move |time_point| {
            let quay_state = &self.timeline[&time_point];
            (
                time_point,
                quay_state.iter_free_intervals(required_space, search_space),
            )
        })
    }

    #[inline]
    pub fn slice_predecessor_timepoint(&self, time_point: TimePoint<T>) -> Option<TimePoint<T>>
    where
        T: PrimInt + Signed,
    {
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
            .range((Excluded(start), Included(end)))
            .map(|(time_key, _)| *time_key)
            .filter(move |time_key| *time_key != end)
    }

    #[inline]
    pub fn iter_free(
        &self,
        tw: TimeInterval<T>,
        dur: TimeDelta<T>,
        need: SpaceLength,
        bounds: SpaceInterval,
    ) -> FreeIter<'_, T, Q> {
        FreeIter {
            berth: self,
            time_window: tw,
            processing_duration: dur,
            required_length: need,
            search_bounds: bounds,
            yielded_window_start: false,
            last_start_time: None,
            current_start_time: None,
            feasible_runs: DoubleBuf::new(),
            next_emit_index: 0,
        }
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

        let left_boundary = self
            .timeline
            .range(..start_time)
            .next_back()
            .map(|(time_point, _)| *time_point)
            .unwrap_or(start_time);

        let right_boundary = self
            .timeline
            .range((Excluded(end_time), Unbounded))
            .next()
            .map(|(time_point, _)| *time_point)
            .unwrap_or(end_time);

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
        if !self.timeline.contains_key(&time_point) {
            return;
        }

        let current_quay_state = match self.timeline.get(&time_point) {
            Some(value) => value.clone(),
            None => return,
        };

        let previous_state_is_equal = self
            .timeline
            .range(..time_point)
            .next_back()
            .is_some_and(|(_, previous_quay_state)| *previous_quay_state == current_quay_state);

        let next_state_is_equal_or_none = match self
            .timeline
            .range((Excluded(time_point), Unbounded))
            .next()
        {
            None => true,
            Some((_, next_quay_state)) => *next_quay_state == current_quay_state,
        };

        if previous_state_is_equal && next_state_is_equal_or_none {
            self.timeline.remove(&time_point);
        }
    }

    #[inline]
    fn iter_timepoints_covering(
        &self,
        start: TimePoint<T>,
        end: TimePoint<T>,
    ) -> impl Iterator<Item = TimePoint<T>> + '_ {
        let pred = self
            .timeline
            .range(..=start)
            .next_back()
            .map(|(t, _)| *t)
            .into_iter();
        pred.chain(self.iter_timepoints(TimeInterval::new(start, end)))
    }
}

impl<T, Q> BerthOccupancy<T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead + QuayWrite + Clone + PartialEq,
{
    pub fn occupy(&mut self, time_interval: TimeInterval<T>, space_interval: SpaceInterval) {
        if time_interval.is_empty() {
            return;
        }

        let (start_time, end_time) = (time_interval.start(), time_interval.end());
        self.split_at(start_time);
        self.split_at(end_time);

        if space_interval.is_empty() {
            return;
        }

        debug_assert!(self.space_within_quay(space_interval));

        for (_, quay_state) in self
            .timeline
            .range_mut((Included(start_time), Excluded(end_time)))
        {
            quay_state.occupy(space_interval);
        }

        self.coalesce_range(start_time, end_time);
    }

    pub fn free(&mut self, time_interval: TimeInterval<T>, space_interval: SpaceInterval) {
        if time_interval.is_empty() {
            return;
        }

        let (start_time, end_time) = (time_interval.start(), time_interval.end());
        self.split_at(start_time);
        self.split_at(end_time);

        if space_interval.is_empty() {
            return;
        }

        debug_assert!(self.space_within_quay(space_interval));

        for (_, quay_state) in self
            .timeline
            .range_mut((Included(start_time), Excluded(end_time)))
        {
            quay_state.free(space_interval);
        }

        self.coalesce_range(start_time, end_time);
    }

    #[inline]
    pub fn occupy_at(
        &mut self,
        start_time: TimePoint<T>,
        duration: TimeDelta<T>,
        space_interval: SpaceInterval,
    ) {
        self.occupy(
            TimeInterval::new(start_time, start_time + duration),
            space_interval,
        );
    }

    #[inline]
    pub fn free_at(
        &mut self,
        start_time: TimePoint<T>,
        duration: TimeDelta<T>,
        space_interval: SpaceInterval,
    ) {
        self.free(
            TimeInterval::new(start_time, start_time + duration),
            space_interval,
        );
    }
}

pub struct FreeIter<'a, T, Q>
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

impl<'a, T, Q> FreeIter<'a, T, Q>
where
    T: PrimInt + Signed + Copy,
    Q: QuayRead,
{
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
            && next_key + self.processing_duration <= self.time_window.end() {
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
            .iter_free_intervals(SpaceLength::new(1), bounds)
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

impl<'a, T, Q> Iterator for FreeIter<'a, T, Q>
where
    T: PrimInt + Signed + Copy,
    Q: QuayRead,
{
    type Item = (TimePoint<T>, SpaceInterval);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(start_time) = self.current_start_time {
                if self.next_emit_index < self.feasible_runs.current().len() {
                    let run = self.feasible_runs.current()[self.next_emit_index];
                    self.next_emit_index += 1;
                    return Some((start_time, run));
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
            berth_occupancy.occupy(time_interval, space_interval);
        }
        berth_occupancy
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt;

    #[derive(Clone, PartialEq, Eq)]
    struct MockQuay {
        occupancy: Vec<bool>,
    }

    impl fmt::Debug for MockQuay {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            let occupancy_string: String = self
                .occupancy
                .iter()
                .map(|&is_occupied| if is_occupied { 'X' } else { '_' })
                .collect();
            write!(formatter, "MockQuay({})", occupancy_string)
        }
    }

    impl QuayRead for MockQuay {
        fn new(total_space: SpaceLength, initially_free: bool) -> Self
        where
            Self: Sized,
        {
            let num_units = total_space.value();
            MockQuay {
                occupancy: vec![!initially_free; num_units],
            }
        }

        fn capacity(&self) -> SpaceLength {
            SpaceLength::new(self.occupancy.len())
        }

        type FreeIter<'a> = std::vec::IntoIter<SpaceInterval>;

        fn check_free(&self, space: SpaceInterval) -> bool {
            let start_index = space.start().value();
            let end_index = space.end().value();
            self.occupancy[start_index..end_index]
                .iter()
                .all(|&is_occupied| !is_occupied)
        }

        fn check_occupied(&self, space: SpaceInterval) -> bool {
            let start_index = space.start().value();
            let end_index = space.end().value();
            self.occupancy[start_index..end_index]
                .iter()
                .any(|&is_occupied| is_occupied)
        }

        fn iter_free_intervals(
            &self,
            required_space: SpaceLength,
            search_range: SpaceInterval,
        ) -> Self::FreeIter<'_> {
            let required_length = required_space.value();
            let start_index = search_range.start().value();
            let end_index = search_range.end().value();
            let mut result_intervals: Vec<SpaceInterval> = Vec::new();

            if start_index >= end_index {
                return result_intervals.into_iter();
            }

            let mut index = start_index;
            while index < end_index {
                while index < end_index && self.occupancy[index] {
                    index += 1;
                }
                if index >= end_index {
                    break;
                }
                let start_of_free_space = index;
                while index < end_index && !self.occupancy[index] {
                    index += 1;
                }
                let end_of_free_space = index;
                if end_of_free_space - start_of_free_space >= required_length {
                    result_intervals.push(SpaceInterval::new(
                        SpacePosition::new(start_of_free_space),
                        SpacePosition::new(end_of_free_space),
                    ));
                }
            }
            result_intervals.into_iter()
        }
    }

    impl QuayWrite for MockQuay {
        fn occupy(&mut self, space: SpaceInterval) {
            let start_index = space.start().value();
            let end_index = space.end().value();
            for index in start_index..end_index {
                self.occupancy[index] = true;
            }
        }
        fn free(&mut self, space: SpaceInterval) {
            let start_index = space.start().value();
            let end_index = space.end().value();
            for index in start_index..end_index {
                self.occupancy[index] = false;
            }
        }
    }

    type T = i64;
    type BO = BerthOccupancy<T, MockQuay>;

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

    fn collect_free_iter(
        berth: &BO,
        tw: TimeInterval<T>,
        dur: TimeDelta<T>,
        need: SpaceLength,
        bounds: SpaceInterval,
    ) -> Vec<(T, (usize, usize))> {
        berth
            .iter_free(tw, dur, need, bounds)
            .map(|(t0, space)| (t0.value(), (space.start().value(), space.end().value())))
            .collect()
    }

    #[test]
    fn test_initial_state_is_free_single_event() {
        let quay_length = len(10);
        let berth_occupancy = BO::new(quay_length);

        assert_eq!(berth_occupancy.time_event_count(), 1);
        assert!(berth_occupancy.is_free(ti(0, 100), si(0, 10)));
        assert!(!berth_occupancy.is_occupied(ti(0, 100), si(0, 10)));
    }

    #[test]
    fn test_occupy_creates_boundaries_and_mutates_exact_span() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(ti(5, 10), si(2, 5));

        // boundaries at 0 (origin), 5, 10
        assert_eq!(berth_occupancy.time_event_count(), 3);

        // before 5 -> free
        assert!(berth_occupancy.is_free(ti(0, 5), si(2, 5)));

        // [5,10) occupied in [2,5)
        assert!(berth_occupancy.is_occupied(ti(5, 10), si(2, 5)));
        assert!(!berth_occupancy.is_free(ti(5, 10), si(2, 5)));

        // after 10 -> back to free
        assert!(berth_occupancy.is_free(ti(10, 20), si(2, 5)));
    }

    #[test]
    fn test_free_then_coalesce_back_to_single_event() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(ti(5, 10), si(2, 5));
        berth_occupancy.free(ti(5, 10), si(2, 5));

        // Should merge back to a single fully-free snapshot
        assert_eq!(berth_occupancy.time_event_count(), 1);
        assert!(berth_occupancy.is_free(ti(0, 100), si(0, 10)));
    }

    #[test]
    fn test_no_mutation_outside_interval() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(ti(5, 10), si(2, 5));

        // Space outside [2,5) always free
        assert!(berth_occupancy.is_free(ti(0, 100), si(0, 2)));
        assert!(berth_occupancy.is_free(ti(0, 100), si(5, 10)));

        // Times outside [5,10) always free within [2,5)
        assert!(berth_occupancy.is_free(ti(0, 5), si(2, 5)));
        assert!(berth_occupancy.is_free(ti(10, 20), si(2, 5)));
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
        berth_occupancy.occupy(ti(3, 3), si(2, 4));
        assert_eq!(berth_occupancy.time_event_count(), 1);

        // Empty space: [6,6)
        berth_occupancy.occupy(ti(0, 5), si(6, 6));
        assert_eq!(
            berth_occupancy.time_event_count(),
            2,
            "split_at(t0) still occurs"
        );

        // But no mutation in the snapshot at t=0
        assert!(berth_occupancy.is_free(ti(0, 5), si(0, 10)));
    }

    #[test]
    fn test_overlapping_occupies_produce_multiple_boundaries() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(ti(5, 12), si(2, 4));
        berth_occupancy.occupy(ti(8, 15), si(1, 3));

        // boundaries: 0,5,8,12,15
        assert_eq!(berth_occupancy.time_event_count(), 5);

        // Check a few windows
        assert!(berth_occupancy.is_occupied(ti(6, 7), si(2, 4))); // first occupy
        assert!(berth_occupancy.is_occupied(ti(9, 11), si(1, 3))); // overlap of both
        assert!(berth_occupancy.is_free(ti(12, 15), si(3, 10))); // free region in space
    }

    #[test]
    fn test_partial_free_does_not_fully_clear() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(ti(5, 10), si(2, 5));
        berth_occupancy.free(ti(7, 9), si(3, 4));

        // [7,9) now has [3,4) free but [2,3) and [4,5) still occupied
        assert!(berth_occupancy.is_occupied(ti(7, 9), si(2, 3)));
        assert!(berth_occupancy.is_free(ti(7, 9), si(3, 4)));
        assert!(berth_occupancy.is_occupied(ti(7, 9), si(4, 5)));
    }

    #[test]
    fn test_query_crossing_boundary_uses_predecessor_and_timepoints() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(ti(5, 10), si(2, 5));

        // Query [4,6): must consider predecessor of 4 (t=0) and key 5 in (4,6)
        // Since at t=5 it becomes occupied, overall "is_free" must be false.
        assert!(!berth_occupancy.is_free(ti(4, 6), si(2, 5)));
        assert!(berth_occupancy.is_occupied(ti(4, 6), si(2, 5)));
    }

    #[test]
    fn test_iter_free_per_slice_reports_per_snapshot_gaps() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        // Occupy [5,10):[2,5)
        berth_occupancy.occupy(ti(5, 10), si(2, 5));

        // For search_space [0,10), required >= 2
        let required_length = len(2);
        let search_interval = si(0, 10);

        let mut collected_slices: Vec<(T, Vec<(usize, usize)>)> = Vec::new();
        for (start_time, free_intervals_iterator) in
            berth_occupancy.iter_free_per_slice(ti(0, 10), required_length, search_interval)
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

        berth_occupancy.occupy(ti(10, 20), si(4, 12));
        let events_after_first = berth_occupancy.time_event_count();

        berth_occupancy.occupy(ti(10, 20), si(4, 12));
        assert_eq!(
            berth_occupancy.time_event_count(),
            events_after_first,
            "idempotent occupy should not add events"
        );

        assert!(berth_occupancy.is_occupied(ti(10, 20), si(4, 12)));
    }

    #[test]
    fn test_free_idempotent_over_same_region() {
        let quay_length = len(16);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(ti(10, 20), si(4, 12));
        berth_occupancy.free(ti(10, 20), si(4, 12));
        let events_after_first = berth_occupancy.time_event_count();

        berth_occupancy.free(ti(10, 20), si(4, 12));
        assert_eq!(
            berth_occupancy.time_event_count(),
            events_after_first,
            "idempotent free should not add events"
        );
        assert!(berth_occupancy.is_free(ti(0, 100), si(0, 16)));
    }

    #[test]
    fn test_adjacent_updates_keep_half_open_semantics() {
        let quay_length = len(10);
        let mut berth_occupancy = BO::new(quay_length);

        // Occupy [2,5) left, then [5,7) right, on same space
        berth_occupancy.occupy(ti(2, 5), si(3, 6));
        berth_occupancy.occupy(ti(5, 7), si(3, 6));

        // At t=5 they just touch; occupancy should be continuous across [2,7)
        assert!(berth_occupancy.is_occupied(ti(2, 7), si(3, 6)));
        // Boundaries: 0,2,5,7
        assert_eq!(berth_occupancy.time_event_count(), 4);
    }

    #[test]
    fn test_coalesce_across_border_after_full_revert() {
        let quay_length = len(8);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(ti(3, 6), si(2, 4));
        // Now revert with two frees that exactly cancel
        berth_occupancy.free(ti(3, 4), si(2, 4));
        berth_occupancy.free(ti(4, 6), si(2, 4));

        // Should fully coalesce back to one event
        assert_eq!(berth_occupancy.time_event_count(), 1);
        assert!(berth_occupancy.is_free(ti(0, 10), si(0, 8)));
    }

    #[test]
    fn test_snapshot_at_reads_correct_state() {
        let quay_length = len(6);
        let mut berth_occupancy = BO::new(quay_length);

        berth_occupancy.occupy(ti(2, 4), si(1, 3));

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
        berth.occupy(ti(5, 6), si(9, 10)); // creates keys 5 and 6

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
        berth.occupy(ti(5, 9), si(2, 6)); // key at 5
        berth.occupy(ti(7, 12), si(6, 9)); // key at 7

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
        berth.occupy(ti(5, 6), si(2, 6));

        // Keys: 0 (origin), 5, 6
        // With dur=0, we’ll check predecessor snapshot for each candidate start:
        // start=0 → free everywhere; start=5 → [2,6) blocked; start=6 → free everywhere again.
        let items: Vec<_> = berth
            .iter_free(ti(0, 6), TimeDelta::new(0), len(2), si(0, 10))
            .map(|(t, s)| (t.value(), (s.start().value(), s.end().value())))
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
}
