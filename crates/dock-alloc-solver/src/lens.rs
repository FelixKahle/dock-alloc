// Copyright (c) 2025 Felix Kahle.
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to do so, subject to the following conditions:
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

use crate::occ::BerthOccupancy;
use crate::quay::{Quay, QuayRead, QuayWrite};
use dock_alloc_core::domain::{SpaceInterval, SpaceLength, TimeDelta, TimeInterval, TimePoint};
use num_traits::{PrimInt, Signed, Zero};
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SpaceIntervalSet {
    intervals: Vec<SpaceInterval>,
}

impl SpaceIntervalSet {
    #[inline]
    pub fn new() -> Self {
        Self {
            intervals: Vec::new(),
        }
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            intervals: Vec::with_capacity(capacity),
        }
    }

    #[inline]
    pub fn from_vec(mut intervals: Vec<SpaceInterval>) -> Self {
        if !intervals.is_empty() {
            Self::coalesce_in_place(&mut intervals);
        }
        Self { intervals }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.intervals.len()
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.intervals.is_empty()
    }

    #[inline]
    pub fn as_slice(&self) -> &[SpaceInterval] {
        &self.intervals
    }

    #[inline]
    pub fn clear(&mut self) {
        self.intervals.clear()
    }

    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.intervals.reserve(additional)
    }

    #[inline]
    pub fn into_vec(self) -> Vec<SpaceInterval> {
        self.intervals
    }

    #[inline]
    pub fn covers(&self, required_interval: SpaceInterval) -> bool {
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
    pub fn overlaps(&self, interval_to_check: SpaceInterval) -> bool {
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
    pub fn clamped_to(&self, bounds: SpaceInterval) -> Self {
        if self.is_empty() {
            return Self::new();
        }
        let mut result_set = Self::with_capacity(self.len());
        for interval in &self.intervals {
            if let Some(clamped_interval) = bounds.clamp(interval) {
                result_set.push_coalesced(clamped_interval);
            }
        }
        result_set
    }

    #[inline]
    pub fn clamped_linear(&self, bounds: SpaceInterval) -> Self {
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
    pub fn push_coalesced(&mut self, new_interval: SpaceInterval) {
        if new_interval.start() >= new_interval.end() {
            return;
        }
        let intervals = &mut self.intervals;
        let mut insertion_index = match intervals
            .binary_search_by_key(&new_interval.start(), |interval| interval.start())
        {
            Ok(index) => index,
            Err(index) => index,
        };
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
    pub fn union(&self, other: &Self) -> Self {
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
    pub fn subtract(&self, other: &Self) -> Self {
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
    pub fn intersection(&self, other: &Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return Self::new();
        }
        let (self_intervals, other_intervals) = (&self.intervals, &other.intervals);
        let mut result_intervals: Vec<SpaceInterval> =
            Vec::with_capacity(self_intervals.len().min(other_intervals.len()));
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
                result_intervals.push(SpaceInterval::new(intersection_start, intersection_end));
            }
            if self_intervals[self_index].end() < other_intervals[other_index].end() {
                self_index += 1
            } else {
                other_index += 1
            }
        }
        debug_assert!(Self::is_sorted_non_overlapping(&result_intervals));
        Self {
            intervals: result_intervals,
        }
    }

    #[inline]
    pub fn intersection_into(&self, other: &Self, result_set: &mut Self) {
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
    pub fn filter_min_length(mut self, min_length: SpaceLength) -> Self {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BerthOccupancyOverlay<T: PrimInt + Signed> {
    free_by_time: BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    occupied_by_time: BTreeMap<TimePoint<T>, SpaceIntervalSet>,
}

impl<T: PrimInt + Signed> Default for BerthOccupancyOverlay<T> {
    fn default() -> Self {
        Self {
            free_by_time: BTreeMap::new(),
            occupied_by_time: BTreeMap::new(),
        }
    }
}

impl<T: PrimInt + Signed> BerthOccupancyOverlay<T> {
    #[inline]
    pub fn new() -> Self {
        Self::default()
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

    #[inline]
    pub fn free_timepoints(&self) -> impl Iterator<Item = TimePoint<T>> + '_ {
        self.free_by_time.keys().copied()
    }

    #[inline]
    pub fn occupied_timepoints(&self) -> impl Iterator<Item = TimePoint<T>> + '_ {
        self.occupied_by_time.keys().copied()
    }

    #[inline]
    pub fn adjust_runs(
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

    #[inline]
    fn occupied_overlaps_at(&self, timepoint: TimePoint<T>, space_interval: SpaceInterval) -> bool {
        self.occupied_by_time
            .get(&timepoint)
            .is_some_and(|set| set.overlaps(space_interval))
    }

    pub fn occupy<Q>(
        &mut self,
        berth: &BerthOccupancy<T, Q>,
        time_window: TimeInterval<T>,
        space_interval: SpaceInterval,
    ) where
        T: Zero + Copy,
        Q: QuayRead + QuayWrite + Clone + PartialEq,
    {
        if let Some(predecessor_timepoint) = berth.slice_predecessor_timepoint(time_window.start())
        {
            self.add_occupy(predecessor_timepoint, space_interval);
        }
        for timepoint in berth.iter_timepoints(time_window) {
            self.add_occupy(timepoint, space_interval);
        }
    }

    #[inline]
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

    pub fn undo_occupy<Q>(
        &mut self,
        berth: &BerthOccupancy<T, Q>,
        time_window: TimeInterval<T>,
        space_interval: SpaceInterval,
    ) where
        Q: QuayRead + QuayWrite + Clone + PartialEq,
    {
        if let Some(pred) = berth.slice_predecessor_timepoint(time_window.start()) {
            self.remove_occupy(pred, space_interval);
        }
        for tp in berth.iter_timepoints(time_window) {
            self.remove_occupy(tp, space_interval);
        }
    }

    pub fn free<Q>(
        &mut self,
        berth: &BerthOccupancy<T, Q>,
        time_window: TimeInterval<T>,
        space_interval: SpaceInterval,
    ) where
        T: Zero + Copy,
        Q: QuayRead + QuayWrite + Clone + PartialEq,
    {
        if let Some(predecessor_timepoint) = berth.slice_predecessor_timepoint(time_window.start())
        {
            self.add_free(predecessor_timepoint, space_interval);
        }
        for timepoint in berth.iter_timepoints(time_window) {
            self.add_free(timepoint, space_interval);
        }
    }

    #[inline]
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

    pub fn undo_free<Q>(
        &mut self,
        berth: &BerthOccupancy<T, Q>,
        time_window: TimeInterval<T>,
        space_interval: SpaceInterval,
    ) where
        Q: QuayRead + QuayWrite + Clone + PartialEq,
    {
        if let Some(pred) = berth.slice_predecessor_timepoint(time_window.start()) {
            self.remove_free(pred, space_interval);
        }
        for tp in berth.iter_timepoints(time_window) {
            self.remove_free(tp, space_interval);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AvailabilityView<'a, T: PrimInt + Signed, Q: Quay> {
    berth: &'a BerthOccupancy<T, Q>,
    slice_timepoints: Vec<TimePoint<T>>,
}

impl<'a, T, Q> AvailabilityView<'a, T, Q>
where
    T: PrimInt + Signed + Zero + Copy,
    Q: QuayRead + QuayWrite + Clone + PartialEq,
{
    pub fn new(berth: &'a BerthOccupancy<T, Q>, time_window: TimeInterval<T>) -> Self {
        let mut slice_timepoints = Vec::<TimePoint<T>>::new();
        if let Some(predecessor_timepoint) = berth.slice_predecessor_timepoint(time_window.start())
        {
            slice_timepoints.push(predecessor_timepoint);
        }
        slice_timepoints.extend(berth.iter_timepoints(time_window));
        Self {
            berth,
            slice_timepoints,
        }
    }

    #[inline]
    pub fn slice_timepoints(&self) -> &[TimePoint<T>] {
        &self.slice_timepoints
    }

    #[inline]
    pub fn berth(&self) -> &BerthOccupancy<T, Q> {
        self.berth
    }

    pub fn is_free_under(
        &self,
        space_interval: SpaceInterval,
        overlay: Option<&BerthOccupancyOverlay<T>>,
    ) -> bool {
        for &timepoint in &self.slice_timepoints {
            let quay_snapshot = self
                .berth
                .snapshot_at(timepoint)
                .expect("slice timepoint must exist");

            if let Some(overlay_ref) = overlay
                && overlay_ref.occupied_overlaps_at(timepoint, space_interval)
            {
                return false;
            }

            if quay_snapshot.check_free(space_interval) {
                continue;
            }

            if let Some(overlay_ref) = overlay {
                let base_free_intervals = SpaceIntervalSet::from_iter(
                    quay_snapshot.iter_free_intervals(SpaceLength::new(1), space_interval),
                );
                let adjusted_free_intervals = overlay_ref.adjust_runs(
                    timepoint,
                    base_free_intervals,
                    space_interval,
                    SpaceLength::new(1),
                );
                if adjusted_free_intervals.covers(space_interval) {
                    continue;
                }
            }
            return false;
        }
        true
    }

    pub fn intersect_free_runs(
        &self,
        required_length: SpaceLength,
        search_space: SpaceInterval,
        overlay: Option<&BerthOccupancyOverlay<T>>,
    ) -> Vec<SpaceInterval> {
        if self.slice_timepoints.is_empty() {
            return Vec::new();
        }

        let mut is_first_iteration = true;
        let mut accumulator_set = SpaceIntervalSet::new();
        let mut temp_set = SpaceIntervalSet::new();

        for &timepoint in &self.slice_timepoints {
            let quay_snapshot = self
                .berth
                .snapshot_at(timepoint)
                .expect("slice timepoint must exist");

            let base_free_intervals = if overlay.is_some() {
                SpaceIntervalSet::from_iter(
                    quay_snapshot.iter_free_intervals(SpaceLength::new(1), search_space),
                )
            } else {
                SpaceIntervalSet::from_iter(
                    quay_snapshot.iter_free_intervals(required_length, search_space),
                )
            };

            let current_slice_free_runs = if let Some(overlay_ref) = overlay {
                overlay_ref.adjust_runs(
                    timepoint,
                    base_free_intervals,
                    search_space,
                    required_length,
                )
            } else {
                base_free_intervals.filter_min_length(required_length)
            };

            if is_first_iteration {
                accumulator_set = current_slice_free_runs;
                is_first_iteration = false;
            } else {
                temp_set.clear();
                accumulator_set.intersection_into(&current_slice_free_runs, &mut temp_set);
                core::mem::swap(&mut accumulator_set, &mut temp_set);
            }

            if accumulator_set.is_empty() {
                break;
            }
        }

        accumulator_set.into_vec()
    }
}

pub struct FreePlacementIter<T>
where
    T: PrimInt + Signed + Zero + Copy,
{
    processing_duration: TimeDelta<T>,
    all_slice_timepoints: Vec<TimePoint<T>>,
    free_runs_per_timepoint: Vec<SpaceIntervalSet>,
    potential_start_time_timepoints: Vec<TimePoint<T>>,
    start_timepoint_key_to_index_map: Vec<usize>,
    start_time_index: usize,
    run_index: usize,
    current_start_time: Option<TimePoint<T>>,
    intersection_buffer_a: SpaceIntervalSet,
    intersection_buffer_b: SpaceIntervalSet,
}

impl<T> FreePlacementIter<T>
where
    T: PrimInt + Signed + Zero + Copy,
{
    pub fn new<'a, Q>(
        berth: &'a BerthOccupancy<T, Q>,
        search_time: TimeInterval<T>,
        processing_duration: TimeDelta<T>,
        required_length: SpaceLength,
        search_space: SpaceInterval,
        overlay: Option<&'a BerthOccupancyOverlay<T>>,
    ) -> Self
    where
        Q: Quay + Clone + PartialEq,
    {
        let mut all_slice_timepoints = Vec::<TimePoint<T>>::new();
        if let Some(predecessor_timepoint) = berth.slice_predecessor_timepoint(search_time.start())
        {
            all_slice_timepoints.push(predecessor_timepoint);
        }
        all_slice_timepoints.extend(berth.iter_timepoints(search_time));

        let mut free_runs_per_timepoint: Vec<SpaceIntervalSet> =
            Vec::with_capacity(all_slice_timepoints.len());
        for &timepoint in &all_slice_timepoints {
            let quay_snapshot = berth
                .snapshot_at(timepoint)
                .expect("slice timepoint must exist");
            let base_free_intervals = if overlay.is_some() {
                SpaceIntervalSet::from_iter(
                    quay_snapshot.iter_free_intervals(SpaceLength::new(1), search_space),
                )
            } else {
                SpaceIntervalSet::from_iter(
                    quay_snapshot.iter_free_intervals(required_length, search_space),
                )
            };
            let free_runs = if let Some(overlay_ref) = overlay {
                overlay_ref.adjust_runs(
                    timepoint,
                    base_free_intervals,
                    search_space,
                    required_length,
                )
            } else {
                base_free_intervals.filter_min_length(required_length)
            };
            free_runs_per_timepoint.push(free_runs);
        }

        let mut potential_start_timepoints = Vec::<TimePoint<T>>::new();
        let mut start_timepoint_key_to_index_map = Vec::<usize>::new();
        for (index, &timepoint) in all_slice_timepoints.iter().enumerate() {
            let end_time = timepoint + processing_duration;
            if timepoint >= search_time.start() && end_time <= search_time.end() {
                potential_start_timepoints.push(timepoint);
                start_timepoint_key_to_index_map.push(index);
            }
        }

        Self {
            processing_duration,
            all_slice_timepoints,
            free_runs_per_timepoint,
            potential_start_time_timepoints: potential_start_timepoints,
            start_timepoint_key_to_index_map,
            start_time_index: 0,
            run_index: 0,
            current_start_time: None,
            intersection_buffer_a: SpaceIntervalSet::new(),
            intersection_buffer_b: SpaceIntervalSet::new(),
        }
    }

    #[inline]
    fn next_runs_for_next_t0(&mut self) -> bool {
        while self.start_time_index < self.potential_start_time_timepoints.len() {
            let start_time = self.potential_start_time_timepoints[self.start_time_index];
            let start_index = self.start_timepoint_key_to_index_map[self.start_time_index];
            self.start_time_index += 1;

            let end_time = start_time + self.processing_duration;
            self.intersection_buffer_a = self.free_runs_per_timepoint[start_index].clone();

            let mut intersection_index = start_index + 1;
            while intersection_index < self.all_slice_timepoints.len()
                && self.all_slice_timepoints[intersection_index] < end_time
            {
                if self.intersection_buffer_a.is_empty() {
                    break;
                }
                self.intersection_buffer_b.clear();
                self.intersection_buffer_a.intersection_into(
                    &self.free_runs_per_timepoint[intersection_index],
                    &mut self.intersection_buffer_b,
                );
                core::mem::swap(
                    &mut self.intersection_buffer_a,
                    &mut self.intersection_buffer_b,
                );
                intersection_index += 1;
            }

            if !self.intersection_buffer_a.is_empty() {
                self.run_index = 0;
                self.current_start_time = Some(start_time);
                return true;
            }
        }
        false
    }
}

impl<T> Iterator for FreePlacementIter<T>
where
    T: PrimInt + Signed + Zero + Copy,
{
    type Item = (TimePoint<T>, SpaceInterval);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let current_runs = self.intersection_buffer_a.as_slice();
            if self.run_index < current_runs.len() {
                let run = current_runs[self.run_index];
                self.run_index += 1;
                let start_time = self
                    .current_start_time
                    .expect("current_t0 set when cur runs available");
                return Some((start_time, run));
            }
            if !self.next_runs_for_next_t0() {
                return None;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quay::BTreeMapQuay;
    use dock_alloc_core::domain::SpacePosition;

    type T = i64;
    type BO = BerthOccupancy<T, BTreeMapQuay>;

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

    #[test]
    fn set_from_vec_and_push_coalesced() {
        let s = SpaceIntervalSet::from_vec(vec![si(5, 7), si(1, 3), si(3, 4), si(2, 5)]);
        assert_eq!(s.as_slice(), &[si(1, 7)]);
        let mut s2 = SpaceIntervalSet::new();
        s2.push_coalesced(si(2, 4));
        s2.push_coalesced(si(6, 8));
        s2.push_coalesced(si(4, 6));
        assert_eq!(s2.as_slice(), &[si(2, 8)]);
    }

    #[test]
    fn set_union_subtract_intersection() {
        let a = SpaceIntervalSet::from_vec(vec![si(0, 2), si(6, 9)]);
        let b = SpaceIntervalSet::from_vec(vec![si(1, 5), si(9, 10)]);
        assert_eq!(a.union(&b).as_slice(), &[si(0, 5), si(6, 10)]);

        let a = SpaceIntervalSet::from_vec(vec![si(0, 10)]);
        let b = SpaceIntervalSet::from_vec(vec![si(2, 4), si(6, 12)]);
        assert_eq!(a.subtract(&b).as_slice(), &[si(0, 2), si(4, 6)]);

        let a = SpaceIntervalSet::from_vec(vec![si(0, 3), si(5, 10)]);
        let b = SpaceIntervalSet::from_vec(vec![si(2, 6), si(8, 12)]);
        assert_eq!(
            a.intersection(&b).as_slice(),
            &[si(2, 3), si(5, 6), si(8, 10)]
        );
    }

    #[test]
    fn set_covers_and_overlaps() {
        let s = SpaceIntervalSet::from_vec(vec![si(0, 2), si(4, 8)]);
        assert!(s.covers(si(4, 6)));
        assert!(!s.covers(si(1, 5)));
        assert!(s.overlaps(si(1, 3)));
        assert!(!s.overlaps(si(2, 4)));
    }

    #[test]
    fn availability_is_free_without_overlay() {
        let quay_length = len(10);
        let berth = BO::new(quay_length);

        let view = AvailabilityView::new(&berth, ti(0, 10));
        assert!(view.is_free_under(si(0, 10), None));
        assert!(view.is_free_under(si(3, 7), None));
    }

    #[test]
    fn availability_overlay_occupy_blocks() {
        let quay_length = len(12);
        let berth = BO::new(quay_length);

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_occupy(tp(0), si(2, 5));

        let view = AvailabilityView::new(&berth, ti(0, 10));
        assert!(!view.is_free_under(si(2, 5), Some(&ov)));
        assert!(view.is_free_under(si(0, 2), Some(&ov)));
        assert!(view.is_free_under(si(5, 12), Some(&ov)));
    }

    #[test]
    fn availability_overlay_free_covers_base_occupied() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);

        berth.occupy(ti(5, 10), si(2, 6));
        let view = AvailabilityView::new(&berth, ti(5, 10));

        assert!(!view.is_free_under(si(2, 6), None));

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(2, 6));
        assert!(view.is_free_under(si(2, 6), Some(&ov)));
    }

    #[test]
    fn intersect_free_runs_overlay_union_and_subtract() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        berth.occupy(ti(5, 10), si(2, 6));
        let view = AvailabilityView::new(&berth, ti(5, 10));

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(2, 4));
        ov.add_occupy(tp(5), si(7, 9));

        let runs = view.intersect_free_runs(len(2), si(0, 10), Some(&ov));
        let pairs: Vec<(usize, usize)> = runs
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert_eq!(pairs, vec![(0, 4)]);
    }

    #[test]
    fn free_placement_iter_basic() {
        let quay_length = len(8);
        let berth = BO::new(quay_length);

        let search_time = ti(0, 10);
        let proc_len = TimeDelta::new(3);
        let required = len(2);
        let search_space = si(0, 5);

        let it =
            FreePlacementIter::new(&berth, search_time, proc_len, required, search_space, None);
        let items: Vec<(T, (usize, usize))> = it
            .map(|(t0, space)| (t0.value(), (space.start().value(), space.end().value())))
            .collect();

        assert_eq!(items, vec![(0, (0, 5))]);
    }

    #[test]
    fn intersect_free_runs_across_multiple_slices() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);

        berth.occupy(ti(5, 10), si(2, 6));
        berth.occupy(ti(10, 15), si(1, 3));

        let view = AvailabilityView::new(&berth, ti(5, 15));

        let runs = view.intersect_free_runs(len(1), si(0, 12), None);
        let pairs: Vec<(usize, usize)> = runs
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert_eq!(pairs, vec![(0, 1), (6, 12)]);
    }

    #[test]
    fn overlay_applies_to_predecessor_slice_timepoint() {
        let quay_length = len(10);
        let berth = BO::new(quay_length);

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_occupy(tp(0), si(3, 5));

        let view = AvailabilityView::new(&berth, ti(2, 6));
        assert!(!view.is_free_under(si(3, 5), Some(&ov)));
        assert!(view.is_free_under(si(0, 3), Some(&ov)));
    }

    #[test]
    fn free_placement_iter_with_overlay_creates_slots() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        berth.occupy(ti(5, 10), si(0, 10));

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(2, 6));

        let it = FreePlacementIter::new(
            &berth,
            ti(5, 10),
            TimeDelta::new(3),
            len(3),
            si(0, 10),
            Some(&ov),
        );
        let items: Vec<(T, (usize, usize))> = it
            .map(|(t0, space)| (t0.value(), (space.start().value(), space.end().value())))
            .collect();
        assert_eq!(items, vec![(5, (2, 6))]);
    }

    #[test]
    fn overlay_timepoint_population() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);

        berth.occupy(ti(5, 10), si(1, 2));
        let mut ov = BerthOccupancyOverlay::new();

        ov.occupy(&berth, ti(2, 9), si(3, 7));
        let occupied_timepoints: Vec<T> = ov.occupied_timepoints().map(|tp| tp.value()).collect();
        assert_eq!(occupied_timepoints, vec![0, 5]);

        let mut ov2 = BerthOccupancyOverlay::new();
        ov2.free(&berth, ti(6, 12), si(2, 8));
        let free_timepoints: Vec<T> = ov2.free_timepoints().map(|tp| tp.value()).collect();
        assert_eq!(free_timepoints, vec![5, 10]);
    }

    #[test]
    fn fully_occupied_slice_made_feasible_by_overlay() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 10), si(0, 10));

        let view = AvailabilityView::new(&berth, ti(5, 10));
        assert!(!view.is_free_under(si(3, 7), None));

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(3, 7));
        assert!(view.is_free_under(si(3, 7), Some(&ov)));

        let runs: Vec<_> = view
            .intersect_free_runs(len(2), si(0, 10), Some(&ov))
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert_eq!(runs, vec![(3, 7)]);
    }

    #[test]
    fn subtract_touching_edges_half_open() {
        let a = SpaceIntervalSet::from_vec(vec![si(0, 2), si(4, 6)]);
        let b = SpaceIntervalSet::from_vec(vec![si(2, 4)]);
        let out = a.subtract(&b).into_vec();
        let pairs: Vec<(usize, usize)> = out
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert_eq!(pairs, vec![(0, 2), (4, 6)]);
    }

    #[test]
    fn space_interval_set_push_coalesced_edge_cases() {
        let mut s = SpaceIntervalSet::new();
        // Insert touching and overlapping in mixed order
        s.push_coalesced(si(5, 7));
        s.push_coalesced(si(1, 3));
        s.push_coalesced(si(3, 5)); // touches [1,3) and [5,7) through [3,5) ⇒ full coalesce
        s.push_coalesced(si(10, 12));
        s.push_coalesced(si(8, 10)); // touches [10,12)
        s.push_coalesced(si(7, 8)); // touches [5,7) and [8,10) transitively
        assert_eq!(s.as_slice(), &[si(1, 12)]);
    }

    #[test]
    fn overlaps_touching_and_crossing() {
        let s = SpaceIntervalSet::from_vec(vec![si(2, 5), si(7, 10)]);
        assert!(s.overlaps(si(4, 8))); // crosses both runs
        assert!(s.overlaps(si(4, 5))); // ends inside [2,5)
        assert!(s.overlaps(si(7, 8))); // starts inside [7,10)
        assert!(!s.overlaps(si(5, 7))); // touches at 5 and 7 only (half-open)
        assert!(!s.overlaps(si(1, 2))); // touches at 2 only
        assert!(!s.overlaps(si(10, 12))); // touches at 10 only
        assert!(!s.overlaps(si(0, 1))); // fully before
        assert!(!s.overlaps(si(12, 13))); // fully after
    }

    #[test]
    fn clamped_to_clips_disjoint_preserves_order() {
        let s = SpaceIntervalSet::from_vec(vec![si(0, 3), si(5, 9)]);
        let c = s.clamped_to(si(2, 7));
        assert_eq!(c.as_slice(), &[si(2, 3), si(5, 7)]);
    }

    #[test]
    fn adjust_runs_applies_min_len_filter() {
        let base = SpaceIntervalSet::from_vec(vec![si(0, 1), si(2, 4), si(6, 7)]);
        let ov: BerthOccupancyOverlay<i64> = BerthOccupancyOverlay::new();
        let out = ov.adjust_runs(tp(0), base, si(0, 10), len(2));
        assert_eq!(out.as_slice(), &[si(2, 4)]); // only length ≥ 2 remains
    }

    #[test]
    fn availability_partial_overlay_not_enough() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 10), si(2, 6)); // base occupied

        let view = AvailabilityView::new(&berth, ti(5, 10));
        assert!(!view.is_free_under(si(2, 6), None)); // baseline sanity

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(3, 5)); // frees only a sub-portion
        assert!(!view.is_free_under(si(2, 6), Some(&ov))); // still not fully free
    }

    #[test]
    fn overlay_free_then_occupy_precedence_same_timepoint() {
        // Base fully occupied; overlay frees [2,7), but also occupies [4,6) → occupy wins inside
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 10), si(0, 10));

        let view = AvailabilityView::new(&berth, ti(5, 10));
        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(2, 7));
        ov.add_occupy(tp(5), si(4, 6)); // precedence: (base ∪ free) − occupy

        let runs = view
            .intersect_free_runs(len(1), si(0, 10), Some(&ov))
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect::<Vec<_>>();
        assert_eq!(runs, vec![(2, 4), (6, 7)]);
    }

    #[test]
    fn overlay_occupy_on_any_slice_blocks_is_free_under() {
        // Create slice keys 5 and 6; overlay occupies only at key=6
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 6), si(9, 10)); // just to create keys 5 and 6

        let view = AvailabilityView::new(&berth, ti(5, 7));
        // Without overlay the small rect is free
        assert!(view.is_free_under(si(0, 1), None));

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_occupy(tp(6), si(0, 1)); // occupy only on the second slice
        assert!(!view.is_free_under(si(0, 1), Some(&ov))); // must be false across all slices
    }

    #[test]
    fn intersect_free_runs_three_slices_intersection() {
        // Slices ~ at 5 and 8. Intersection across [5,8) and [8,12) leaves two small runs.
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 8), si(2, 6)); // free: [0,2) ∪ [6,10)
        berth.occupy(ti(8, 12), si(6, 9)); // free: [0,6) ∪ [9,10)

        let view = AvailabilityView::new(&berth, ti(5, 12));
        let runs = view
            .intersect_free_runs(len(1), si(0, 10), None)
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect::<Vec<_>>();
        assert_eq!(runs, vec![(0, 2), (9, 10)]);
    }

    #[test]
    fn intersect_free_runs_empties_if_any_slice_has_no_space() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 6), si(0, 10)); // slice at 5 fully occupied, slice at 6 free

        let view = AvailabilityView::new(&berth, ti(5, 7));
        let runs = view.intersect_free_runs(len(1), si(0, 10), None);
        assert!(
            runs.is_empty(),
            "intersection across slices should be empty"
        );
    }

    #[test]
    fn free_placement_iter_multiple_start_times_with_slice_timepoints() {
        // Ensure we get multiple t0 values when there are multiple slice keys.
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 6), si(9, 10)); // create keys 5 and 6; irrelevant to search_space

        let it = FreePlacementIter::new(
            &berth,
            ti(0, 10),         // search_time
            TimeDelta::new(3), // proc_len
            len(2),            // required length
            si(0, 5),          // search_space (keeps it independent from [9,10) occupancy)
            None,
        );

        let items: Vec<(T, (usize, usize))> = it
            .map(|(t0, space)| (t0.value(), (space.start().value(), space.end().value())))
            .collect();

        // keys_all ~ [0,5,6] → t0_keys ~ [0,5,6] since +3 ≤ 10 for each
        assert_eq!(items, vec![(0, (0, 5)), (5, (0, 5)), (6, (0, 5))]);
    }

    #[test]
    fn intersect_free_runs_overlay_creates_and_cuts_with_min_len() {
        // Base fully occupied; overlay frees two short runs, one is too short after subtract.
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 10), si(0, 12)); // block all

        let view = AvailabilityView::new(&berth, ti(5, 10));
        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(1, 3)); // length 2
        ov.add_free(tp(5), si(7, 10)); // length 3
        ov.add_occupy(tp(5), si(8, 9)); // carve a hole inside second run → splits into [7,8) ∪ [9,10)

        // Require at least length 2: keeps [1,3) (ok), drops [7,8) and [9,10) (length 1 each)
        let runs = view
            .intersect_free_runs(len(2), si(0, 12), Some(&ov))
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect::<Vec<_>>();
        assert_eq!(runs, vec![(1, 3)]);
    }
}
