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

//! IntervalSet: fast sorted, disjoint half-open interval set over `Interval<T>`.
//!
//! Invariants (always held):
//!    - intervals are sorted by `start()`
//!    - intervals are non-overlapping and coalesced
//!    - semantics are half-open `[start, end)`
//!
//! Complexity:
//!    - overlaps, contains_point, covers: `O(log n + k)`
//!    - union/subtract/intersection: `O(n + m)`
//!    - clamped: `O(log n + k)`

use core::ops::Deref;
use dock_alloc_core::primitives::Interval;
use std::{fmt::Debug, ops::Sub};

/// A collection of sorted, disjoint, half-open `[start, end)` intervals.
///
/// `IntervalSet` maintains a set of non-overlapping intervals, automatically
/// sorting and merging them to preserve its invariants. This structure is
/// highly efficient for set-based operations like union, intersection, and
/// subtraction, as well as for spatial queries like checking for overlaps
/// or point containment.
///
/// The half-open `[start, end)` semantic means that the start of an interval
/// is inclusive, while the end is exclusive.
///
/// ## Invariants
///
/// 1.  **Sorted**: Intervals are always sorted in ascending order based on their `start` value.
/// 2.  **Disjoint**: No two intervals in the set overlap. Adjacent intervals are merged
///     (e.g., `[1, 3)` and `[3, 5)` become `[1, 5)`).
///
/// These invariants are upheld by all methods that modify the set.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct IntervalSet<T> {
    intervals: Vec<Interval<T>>,
}

impl<T> IntervalSet<T> {
    /// Creates a new, empty `IntervalSet`.
    ///
    /// The underlying vector does not allocate until the first element is pushed.
    #[inline]
    pub fn new() -> Self {
        Self {
            intervals: Default::default(),
        }
    }

    /// Creates a new, empty `IntervalSet` with at least the specified capacity.
    ///
    /// The set will be able to hold at least `capacity` intervals without
    /// reallocating. If `capacity` is 0, the set will not allocate.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            intervals: Vec::with_capacity(capacity),
        }
    }

    /// Creates a new `IntervalSet` from a vector of intervals.
    ///
    /// The input vector is sorted and its intervals are coalesced in-place
    /// to satisfy the set's invariants. This is the most efficient way to
    /// build a set from a collection of arbitrary intervals.
    #[inline]
    pub fn from_vec(mut source_intervals: Vec<Interval<T>>) -> Self
    where
        T: Ord + Copy,
    {
        if !source_intervals.is_empty() {
            Self::coalesce_unsorted_in_place(&mut source_intervals);
        }
        Self {
            intervals: source_intervals,
        }
    }

    /// Returns the number of disjoint intervals in the set.
    #[inline]
    pub fn len(&self) -> usize {
        self.intervals.len()
    }

    /// Returns `true` if the set contains no intervals.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.intervals.is_empty()
    }

    /// Returns a slice containing all intervals in the set.
    ///
    /// The slice is guaranteed to be sorted and contain no overlapping intervals.
    #[inline]
    pub fn as_slice(&self) -> &[Interval<T>] {
        &self.intervals
    }

    pub fn into_intervals(self) -> Vec<Interval<T>> {
        self.intervals
    }

    /// Clears the set, removing all intervals.
    ///
    /// Note that this method has no effect on the allocated capacity of the
    /// underlying vector.
    #[inline]
    pub fn clear(&mut self) {
        self.intervals.clear();
    }

    /// Finds the index of the first interval `i` such that `intervals[i].start() >= point`.
    ///
    /// This is equivalent to a binary search for the lower bound on interval start points.
    #[inline]
    fn find_first_starting_at_or_after(&self, point: T) -> usize
    where
        T: Ord + Copy,
    {
        // `partition_point` finds the index of the first element that does *not* satisfy the predicate.
        // The predicate `iv.start() < point` defines the partition of elements whose start is less than `point`.
        // The returned index is therefore the first element whose start is >= `point`.
        self.intervals
            .partition_point(|interval| interval.start() < point)
    }

    /// Finds the index of the first interval `i` such that `intervals[i].end() > point`.
    ///
    /// This is used in queries to quickly find the first interval that could
    /// possibly overlap or contain a given point or interval, by skipping all
    /// intervals that end before the point.
    #[inline]
    fn find_first_ending_after(&self, point: T) -> usize
    where
        T: Ord + Copy,
    {
        // The predicate `iv.end() <= point` defines the partition of elements whose end is less than or equal to `point`.
        // The returned index is therefore the first element whose end is strictly greater than `point`.
        self.intervals
            .partition_point(|interval| interval.end() <= point)
    }

    /// Clears the set and fills it from an iterator of intervals.
    ///
    /// This method coalesces intervals on-the-fly without a full sort. For best
    /// performance, the iterator should yield items in a mostly-sorted order.
    #[inline]
    pub fn clear_and_fill_from_iter<I: IntoIterator<Item = Interval<T>>>(&mut self, iter: I)
    where
        T: Ord + Copy,
    {
        self.clear();
        for interval in iter {
            self.insert_and_coalesce(interval);
        }
        debug_assert!(Self::are_invariants_held(&self.intervals));
    }

    /// Inserts a single interval into the set, merging with existing intervals
    /// if they overlap or are adjacent.
    ///
    /// The set's invariants (sorted, disjoint) are maintained.
    #[inline]
    pub fn insert_and_coalesce(&mut self, new_interval: Interval<T>)
    where
        T: Ord + Copy,
    {
        if new_interval.is_empty() {
            return;
        }

        let start_key = new_interval.start();
        let mut insertion_index = self.find_first_starting_at_or_after(start_key);
        let intervals = &mut self.intervals;

        // The new interval's extent, which will expand as we merge with neighbors.
        let mut merged_start = new_interval.start();
        let mut merged_end = new_interval.end();

        // Merge with the interval to the left, if it overlaps or is adjacent.
        // `insertion_index` points to the first interval *after* our new one's start,
        // so we check the one at `insertion_index - 1`.
        if insertion_index > 0 && intervals[insertion_index - 1].end() >= merged_start {
            insertion_index -= 1; // Start merging from this earlier position.
            merged_start = intervals[insertion_index].start().min(merged_start);
            merged_end = intervals[insertion_index].end().max(merged_end);
        }

        // Merge with all subsequent intervals that are covered by or adjacent to the new merged extent.
        let mut coalesce_scan_index = insertion_index;
        while coalesce_scan_index < intervals.len()
            && intervals[coalesce_scan_index].start() <= merged_end
        {
            merged_end = merged_end.max(intervals[coalesce_scan_index].end());
            coalesce_scan_index += 1;
        }

        // Apply the changes to the underlying vector.
        let merged_interval = Interval::new(merged_start, merged_end);
        let num_merged_on_right = coalesce_scan_index - insertion_index;

        if insertion_index == intervals.len() {
            // Case 1: All merged intervals were at the end, or the vector was empty. Append.
            intervals.push(merged_interval);
        } else if num_merged_on_right == 0 {
            // Case 2: No merge on the right occurred. Insert.
            intervals.insert(insertion_index, merged_interval);
        } else {
            // Case 3: One or more intervals on the right were merged.
            // Replace the first merged interval and drain the rest.
            intervals[insertion_index] = merged_interval;
            if num_merged_on_right > 1 {
                intervals.drain(insertion_index + 1..coalesce_scan_index);
            }
        }
        debug_assert!(Self::are_invariants_held(&self.intervals));
    }

    /// Appends an interval to the end of the set, performing a fast merge
    /// with only the last existing interval.
    ///
    /// This method is an optimization for cases where intervals are added in
    /// mostly sorted order. For it to be a true fast path, the caller should
    /// ensure that `interval.start() >= self.last().unwrap().start()`.
    /// If the new interval is significantly out-of-order (`interval.end() <= last.start()`),
    /// this method transparently falls back to the safer (but slower) `insert_and_coalesce`
    /// to maintain correctness.
    #[inline]
    pub fn append_and_coalesce_tail(&mut self, interval: Interval<T>)
    where
        T: Ord + Copy + Debug,
    {
        if interval.is_empty() {
            return;
        }

        // Fallback condition: If the new interval is "way before" the last one,
        // a simple tail merge is incorrect. `insert_and_coalesce` handles this.
        if self.intervals.last().map_or(false, |last_interval| {
            interval.end() <= last_interval.start()
        }) {
            self.insert_and_coalesce(interval);
            return;
        }

        match self.intervals.last_mut() {
            // If the last interval overlaps or is adjacent to the new one, merge them.
            Some(last_interval) if last_interval.end() >= interval.start() => {
                let merged_end = last_interval.end().max(interval.end());
                *last_interval = Interval::new(last_interval.start(), merged_end);
            }
            // Otherwise, just push the new interval.
            _ => self.intervals.push(interval),
        }

        debug_assert!(Self::are_invariants_held(&self.intervals));
    }

    /// Extends the set with a slice of intervals that are already sorted and disjoint.
    ///
    /// This is a highly efficient way to merge another `IntervalSet` or a
    /// pre-processed slice into the current set, as it only needs to check for
    /// coalescence at the boundary between the two sets.
    #[inline]
    pub fn extend_from_sorted_disjoint(&mut self, other_intervals: &[Interval<T>])
    where
        T: Ord + Copy + Debug,
    {
        for &interval in other_intervals {
            self.append_and_coalesce_tail(interval);
        }
    }

    /// Retains only the intervals in the set that have a length greater than
    /// or equal to `min_length`.
    #[inline]
    pub fn retain_min_length<D>(&mut self, min_length: D)
    where
        T: Ord + Copy + Sub<Output = D>,
        D: Ord + Copy,
    {
        self.intervals
            .retain(|interval| interval.length() >= min_length);
    }

    /// Retains only the intervals in the set that satisfy the given `predicate`.
    ///
    /// This method allows for custom filtering logic beyond just length.
    pub fn retain<F>(&mut self, mut predicate: F)
    where
        F: FnMut(&Interval<T>) -> bool,
    {
        self.intervals.retain(|interval| predicate(interval));
    }

    /// Creates a new `IntervalSet` containing only the intervals from the
    /// original set that have a length greater than or equal to `min_length`.
    ///
    /// This is the consuming variant of [`retain_min_length`].
    ///
    /// ## Complexity
    /// O(N), where N is the number of intervals in the set.
    #[inline]
    pub fn filter_min_length<D>(mut self, min_length: D) -> Self
    where
        T: Ord + Copy + Sub<Output = D>,
        D: Ord + Copy,
    {
        self.retain_min_length(min_length);
        self
    }

    /// Returns `true` if any interval in the set overlaps with the `query_interval`.
    #[inline]
    pub fn overlaps(&self, query_interval: Interval<T>) -> bool
    where
        T: Ord + Copy,
    {
        if self.intervals.is_empty() || query_interval.is_empty() {
            return false;
        }
        // Find the first interval that *ends after* our query starts.
        // Any interval ending before or at our query's start cannot overlap.
        let candidate_index = self.find_first_ending_after(query_interval.start());

        // If such an interval exists, check if its start is before our query's end.
        // If both conditions are met, there is an overlap.
        candidate_index < self.intervals.len()
            && self.intervals[candidate_index].start() < query_interval.end()
    }

    /// Returns `true` if the `required_interval` is entirely covered by intervals
    /// within the set.
    ///
    /// An empty `required_interval` is always considered covered.
    #[inline]
    pub fn covers(&self, required_interval: Interval<T>) -> bool
    where
        T: Ord + Copy,
    {
        if required_interval.is_empty() {
            return true;
        }
        // Find the first interval potentially overlapping the start of our requirement.
        let mut interval_index = self.find_first_ending_after(required_interval.start());
        let mut cursor = required_interval.start();

        while interval_index < self.intervals.len() {
            let current_interval = self.intervals[interval_index];
            // If the next interval starts after our cursor, there's a gap.
            if current_interval.start() > cursor {
                return false;
            }
            // Move the cursor to the end of the current covering interval.
            cursor = cursor.max(current_interval.end());
            // If the cursor has reached or passed the end of the requirement, we're done.
            if cursor >= required_interval.end() {
                return true;
            }
            interval_index += 1;
        }
        // If we exit the loop, it means the cursor never reached the end.
        false
    }

    /// Returns `true` if the given point is contained within any interval in the set.
    ///
    /// Due to the half-open `[start, end)` semantics, a point is contained if
    /// `start <= point < end`.
    #[inline]
    pub fn contains_point(&self, point: T) -> bool
    where
        T: Ord + Copy,
    {
        // Find the first interval that ends after the point. This is our only candidate.
        let candidate_index = self.find_first_ending_after(point);
        // Check if this candidate exists and its start is also <= the point.
        candidate_index < self.len() && self.intervals[candidate_index].start() <= point
    }

    /// Computes the intersection of the set with a single `bounds` interval,
    /// storing the result in `output_set`.
    ///
    /// `output_set` is cleared before the operation.
    #[inline]
    pub fn clamped_into(&self, bounds: Interval<T>, output_set: &mut Self)
    where
        T: Ord + Copy,
    {
        output_set.clear();
        if self.is_empty() || bounds.is_empty() {
            return;
        }

        // Find the first interval that might overlap with the bounds.
        let mut interval_index = self.find_first_ending_after(bounds.start());
        while interval_index < self.intervals.len()
            && self.intervals[interval_index].start() < bounds.end()
        {
            let self_interval = self.intervals[interval_index];
            // Calculate the intersection of the current interval and the bounds.
            let intersect_start = self_interval.start().max(bounds.start());
            let intersect_end = self_interval.end().min(bounds.end());

            // Add the intersection to the output if it's a valid, non-empty interval.
            if intersect_start < intersect_end {
                output_set
                    .intervals
                    .push(Interval::new(intersect_start, intersect_end));
            }
            interval_index += 1;
        }
        debug_assert!(Self::are_invariants_held(&output_set.intervals));
    }

    /// Returns a new `IntervalSet` representing the intersection of the set with a
    /// single `bounds` interval.
    ///
    /// This is the convenient, non-in-place version of [`clamped_into`].
    #[inline]
    pub fn clamped(&self, bounds: Interval<T>) -> Self
    where
        T: Ord + Copy,
    {
        let mut output_set = Self::with_capacity(4.min(self.len()));
        self.clamped_into(bounds, &mut output_set);
        output_set
    }

    /// Computes the union of two sets (A ∪ B) and returns a new `IntervalSet`.
    ///
    /// The resulting set contains all intervals that are in `self`, in `other`,
    /// or in both.
    #[inline]
    pub fn union(&self, other: &Self) -> Self
    where
        T: Ord + Copy,
    {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }
        let mut output_set = Self::with_capacity(self.len() + other.len());
        self.union_into(other, &mut output_set);
        output_set
    }

    /// Computes the union of two sets (A ∪ B) and stores the result in `output_set`.
    ///
    /// `output_set` is cleared before the operation.
    #[inline]
    pub fn union_into(&self, other: &Self, output_set: &mut Self)
    where
        T: Ord + Copy,
    {
        output_set.intervals.clear();
        if self.is_empty() {
            output_set.intervals.extend_from_slice(&other.intervals);
            return;
        }
        if other.is_empty() {
            output_set.intervals.extend_from_slice(&self.intervals);
            return;
        }

        let self_intervals = &self.intervals;
        let other_intervals = &other.intervals;
        let (mut self_cursor, mut other_cursor) = (0usize, 0usize);
        output_set
            .intervals
            .reserve(self_intervals.len().saturating_add(other_intervals.len()));

        // Merge the two sorted lists of intervals.
        while self_cursor < self_intervals.len() && other_cursor < other_intervals.len() {
            let next_interval =
                if self_intervals[self_cursor].start() <= other_intervals[other_cursor].start() {
                    let interval = self_intervals[self_cursor];
                    self_cursor += 1;
                    interval
                } else {
                    let interval = other_intervals[other_cursor];
                    other_cursor += 1;
                    interval
                };
            Self::append_and_merge_sorted(&mut output_set.intervals, next_interval);
        }

        // Append any remaining intervals from `self`.
        while self_cursor < self_intervals.len() {
            Self::append_and_merge_sorted(&mut output_set.intervals, self_intervals[self_cursor]);
            self_cursor += 1;
        }

        // Append any remaining intervals from `other`.
        while other_cursor < other_intervals.len() {
            Self::append_and_merge_sorted(&mut output_set.intervals, other_intervals[other_cursor]);
            other_cursor += 1;
        }
        debug_assert!(Self::are_invariants_held(&output_set.intervals));
    }

    /// Computes the set subtraction (A \ B) and returns a new `IntervalSet`.
    ///
    /// The resulting set contains all parts of intervals in `self` that are not
    /// covered by any interval in `other`.
    #[inline]
    pub fn subtract(&self, other: &Self) -> Self
    where
        T: Ord + Copy,
    {
        if self.is_empty() || other.is_empty() {
            return self.clone();
        }
        let mut output_set = Self::with_capacity(self.len());
        self.subtract_into(other, &mut output_set);
        output_set
    }

    /// Computes the set subtraction (A \ B) and stores the result in `output_set`.
    ///
    /// `output_set` is cleared before the operation.
    #[inline]
    pub fn subtract_into(&self, other: &Self, output_set: &mut Self)
    where
        T: Ord + Copy,
    {
        output_set.intervals.clear();
        if self.is_empty() {
            return;
        }
        if other.is_empty() {
            output_set.intervals.extend_from_slice(&self.intervals);
            return;
        }

        let minuend_intervals = &self.intervals; // The set to subtract from.
        let subtrahend_intervals = &other.intervals; // The set of intervals to remove.
        let (mut minuend_cursor, mut subtrahend_cursor) = (0usize, 0usize);

        while minuend_cursor < minuend_intervals.len() {
            let mut current_minuend = minuend_intervals[minuend_cursor];

            // Advance subtrahend cursor past any intervals that are entirely before the current minuend.
            while subtrahend_cursor < subtrahend_intervals.len()
                && subtrahend_intervals[subtrahend_cursor].end() <= current_minuend.start()
            {
                subtrahend_cursor += 1;
            }

            let mut subtrahend_lookahead_cursor = subtrahend_cursor;
            let mut is_minuend_consumed = false;

            // Iterate through all subtrahends that overlap with the current minuend.
            while subtrahend_lookahead_cursor < subtrahend_intervals.len()
                && subtrahend_intervals[subtrahend_lookahead_cursor].start() < current_minuend.end()
            {
                let current_subtrahend = subtrahend_intervals[subtrahend_lookahead_cursor];

                // If there's a part of the minuend *before* the subtrahend, add it.
                if current_subtrahend.start() > current_minuend.start() {
                    output_set.intervals.push(Interval::new(
                        current_minuend.start(),
                        current_subtrahend.start(),
                    ));
                }

                // If the subtrahend covers the rest of the minuend, we are done with it.
                if current_subtrahend.end() >= current_minuend.end() {
                    is_minuend_consumed = true;
                    break;
                }

                // Otherwise, the minuend continues after the subtrahend ends.
                // We update its start point and continue checking against the next subtrahend.
                current_minuend = Interval::new(current_subtrahend.end(), current_minuend.end());
                subtrahend_lookahead_cursor += 1;
            }

            // If the minuend was not fully consumed by the subtrahends, add the remaining part.
            if !is_minuend_consumed {
                output_set.intervals.push(current_minuend);
            }

            subtrahend_cursor = subtrahend_lookahead_cursor;
            minuend_cursor += 1;
        }
        debug_assert!(Self::are_invariants_held(&output_set.intervals));
    }

    /// Computes the intersection of two sets (A ∩ B) and stores the result in `output_set`.
    ///
    /// `output_set` is cleared before the operation. The resulting set contains
    /// all intervals that are present in *both* `self` and `other`.
    #[inline]
    pub fn intersection_into(&self, other: &Self, output_set: &mut Self)
    where
        T: Ord + Copy,
    {
        output_set.intervals.clear();
        if self.is_empty() || other.is_empty() {
            return;
        }

        let self_intervals = &self.intervals;
        let other_intervals = &other.intervals;
        let (mut self_cursor, mut other_cursor) = (0usize, 0usize);
        output_set
            .intervals
            .reserve(self_intervals.len().min(other_intervals.len()));

        while self_cursor < self_intervals.len() && other_cursor < other_intervals.len() {
            let self_iv = self_intervals[self_cursor];
            let other_iv = other_intervals[other_cursor];

            // Calculate the overlapping portion.
            let overlap_start = self_iv.start().max(other_iv.start());
            let overlap_end = self_iv.end().min(other_iv.end());

            if overlap_start < overlap_end {
                output_set
                    .intervals
                    .push(Interval::new(overlap_start, overlap_end));
            }

            // Advance the cursor of the interval that finishes first.
            if self_iv.end() < other_iv.end() {
                self_cursor += 1;
            } else {
                other_cursor += 1;
            }
        }
        debug_assert!(Self::are_invariants_held(&output_set.intervals));
    }

    /// Subtracts a single interval from the set, storing the result in `output_set`.
    ///
    /// This is an optimized hot-path for subtraction when the subtrahend is a
    /// single interval instead of a full `IntervalSet`.
    pub fn subtract_interval_into(&self, subtrahend_interval: Interval<T>, output_set: &mut Self)
    where
        T: Ord + Copy,
    {
        output_set.intervals.clear();
        if self.is_empty() || subtrahend_interval.is_empty() {
            output_set.intervals.extend_from_slice(&self.intervals);
            return;
        }
        for &minuend_interval in &self.intervals {
            // Case 1: The intervals do not overlap. Keep the original minuend.
            if minuend_interval.end() <= subtrahend_interval.start()
                || subtrahend_interval.end() <= minuend_interval.start()
            {
                output_set.intervals.push(minuend_interval);
            } else {
                // Case 2: They overlap. Calculate the remaining parts.
                // Part 1: The portion of the minuend *before* the subtrahend starts.
                if minuend_interval.start() < subtrahend_interval.start() {
                    output_set.intervals.push(Interval::new(
                        minuend_interval.start(),
                        subtrahend_interval.start(),
                    ));
                }
                // Part 2: The portion of the minuend *after* the subtrahend ends.
                if subtrahend_interval.end() < minuend_interval.end() {
                    output_set.intervals.push(Interval::new(
                        subtrahend_interval.end(),
                        minuend_interval.end(),
                    ));
                }
            }
        }
        debug_assert!(Self::are_invariants_held(&output_set.intervals));
    }

    pub fn subtract_interval(&mut self, interval: Interval<T>)
    where
        T: Ord + Copy,
    {
        if self.is_empty() || interval.is_empty() {
            return;
        }
        let mut result = Self::with_capacity(self.len() + 1); // +1 in case of a split
        self.subtract_interval_into(interval, &mut result);
        *self = result;
    }

    /// Returns the complement of the set within a given `bounds`.
    ///
    /// This method finds all the "gaps" in the `IntervalSet` that fall inside
    /// the `bounds` interval.
    #[inline]
    pub fn gaps_within(&self, bounds: Interval<T>) -> Self
    where
        T: Ord + Copy,
    {
        if bounds.is_empty() {
            return Self::new();
        }
        if self.is_empty() {
            // If the set is empty, the entire bounds is a gap.
            return Self::from_vec(vec![bounds]);
        }

        let mut output_set = Self::new();
        // A cursor that tracks the start of the next potential gap.
        let mut cursor = bounds.start();

        // Find the first interval that could possibly be within our bounds.
        let mut interval_index = self.find_first_ending_after(bounds.start());

        while interval_index < self.intervals.len()
            && self.intervals[interval_index].start() < bounds.end()
        {
            let current_interval = self.intervals[interval_index];
            let clamped_start = current_interval.start().max(bounds.start());

            // If the cursor is before the start of the current interval, we have found a gap.
            if cursor < clamped_start {
                output_set
                    .intervals
                    .push(Interval::new(cursor, clamped_start));
            }

            // Move the cursor past the current interval.
            cursor = cursor.max(current_interval.end().min(bounds.end()));
            interval_index += 1;
        }

        // If the cursor hasn't reached the end of the bounds, there's a final gap.
        if cursor < bounds.end() {
            output_set
                .intervals
                .push(Interval::new(cursor, bounds.end()));
        }
        output_set
    }

    /// Sorts and merges a vector of arbitrary intervals in-place.
    ///
    /// After this operation, the vector will satisfy the `IntervalSet` invariants:
    /// sorted by start time and containing no overlapping or adjacent intervals.
    #[inline]
    pub fn coalesce_unsorted_in_place(intervals: &mut Vec<Interval<T>>)
    where
        T: Ord + Copy,
    {
        if intervals.len() < 2 {
            return;
        }
        // Sort by start point, which is the primary invariant.
        intervals.sort_unstable_by_key(|iv| iv.start());

        let mut write_index = 0;
        for read_index in 1..intervals.len() {
            // If the current interval overlaps or is adjacent to the last written one...
            if intervals[write_index].end() >= intervals[read_index].start() {
                // ...merge them by extending the end of the last written interval.
                let merged_end = intervals[write_index]
                    .end()
                    .max(intervals[read_index].end());
                intervals[write_index] = Interval::new(intervals[write_index].start(), merged_end);
            } else {
                // Otherwise, the current interval is disjoint. Move it to the next write position.
                write_index += 1;
                intervals[write_index] = intervals[read_index];
            }
        }
        // The merged intervals are now in `0..=write_index`.
        intervals.truncate(write_index + 1);
        debug_assert!(Self::are_invariants_held(intervals));
    }

    /// Helper for `union_into`. Appends an interval to a sorted, coalesced vector,
    /// merging with the last element if necessary.
    /// Assumes `next_interval` starts at or after the last interval in `destination_vec`.
    #[inline]
    fn append_and_merge_sorted(destination_vec: &mut Vec<Interval<T>>, next_interval: Interval<T>)
    where
        T: Ord + Copy,
    {
        if let Some(last_interval) = destination_vec.last_mut() {
            if last_interval.end() >= next_interval.start() {
                // Merge with the last interval if they overlap or are adjacent.
                let merged_end = last_interval.end().max(next_interval.end());
                *last_interval = Interval::new(last_interval.start(), merged_end);
                return;
            }
        }
        // Otherwise, just append.
        destination_vec.push(next_interval);
    }

    /// A debug-only check to ensure the set's invariants (sorted, non-overlapping) hold.
    ///
    /// In release builds, this function is a no-op and compiles away.
    #[inline]
    #[cfg(debug_assertions)]
    fn are_invariants_held(intervals: &[Interval<T>]) -> bool
    where
        T: Ord + Copy,
    {
        intervals.windows(2).all(|window| {
            window[0].start() < window[1].start() && window[0].end() < window[1].start()
        })
    }

    /// A release-build stub for `are_invariants_held`. Always returns `true`.
    #[inline]
    #[cfg(not(debug_assertions))]
    fn are_invariants_held(_intervals: &[Interval<T>]) -> bool {
        true
    }
}

/// Allows creating an `IntervalSet` from a `Vec<Interval<T>>`.
/// This is equivalent to calling [`IntervalSet::from_vec`].
impl<T> From<Vec<Interval<T>>> for IntervalSet<T>
where
    T: Ord + Copy,
{
    #[inline]
    fn from(vector: Vec<Interval<T>>) -> Self {
        Self::from_vec(vector)
    }
}

/// Allows collecting an iterator of `Interval<T>` into an `IntervalSet`.
///
/// The collected intervals will be sorted and coalesced.
impl<T> FromIterator<Interval<T>> for IntervalSet<T>
where
    T: Ord + Copy,
{
    #[inline]
    fn from_iter<I: IntoIterator<Item = Interval<T>>>(iter: I) -> Self {
        let mut collected_intervals: Vec<Interval<T>> = iter.into_iter().collect();
        if !collected_intervals.is_empty() {
            Self::coalesce_unsorted_in_place(&mut collected_intervals);
        }
        Self {
            intervals: collected_intervals,
        }
    }
}

/// Allows an `IntervalSet` to be treated as a slice `&[Interval<T>]`.
impl<T> Deref for IntervalSet<T> {
    type Target = [Interval<T>];
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.intervals
    }
}

/// Enables iteration over the intervals in the set via `for interval in &my_set`.
impl<'a, T> IntoIterator for &'a IntervalSet<T> {
    type Item = &'a Interval<T>;
    type IntoIter = core::slice::Iter<'a, Interval<T>>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.intervals.iter()
    }
}

/// Enables mutable iteration over the intervals in the set via `for interval in &mut my_set`.
impl<'a, T> IntoIterator for &'a mut IntervalSet<T> {
    type Item = &'a mut Interval<T>;
    type IntoIter = core::slice::IterMut<'a, Interval<T>>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.intervals.iter_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dock_alloc_core::primitives::Interval;

    type SetI = IntervalSet<i32>;

    #[inline]
    fn iv(a: i32, b: i32) -> Interval<i32> {
        Interval::new(a, b)
    }

    #[inline]
    fn assert_invariants(set: &SetI) {
        let v = set.as_slice();
        for w in v.windows(2) {
            assert!(
                w[0].end() <= w[1].start(),
                "violates non-overlap: {:?} then {:?}",
                w[0],
                w[1]
            );
        }
        for (i, iv) in v.iter().enumerate() {
            assert!(
                iv.start() <= iv.end(),
                "bad interval order at {}: {:?}",
                i,
                iv
            );
            // no empties kept by builder ops
            if i < v.len() {
                assert!(
                    iv.start() < iv.end(),
                    "empty interval retained at index {}: {:?}",
                    i,
                    iv
                );
            }
        }
    }

    #[test]
    fn new_and_empty() {
        let s = SetI::new();
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);
        assert_eq!(s.as_slice(), &[]);
    }

    #[test]
    fn from_vec_coalesces_and_sorts() {
        let s = SetI::from_vec(vec![iv(5, 7), iv(1, 3), iv(3, 5), iv(10, 12), iv(11, 13)]);
        assert_eq!(s.as_slice(), &[iv(1, 7), iv(10, 13)]);
        assert_invariants(&s);
    }

    #[test]
    fn from_iterator_coalesces() {
        let s: SetI = vec![iv(8, 9), iv(1, 4), iv(3, 6)].into_iter().collect();
        assert_eq!(s.as_slice(), &[iv(1, 6), iv(8, 9)]);
        assert_invariants(&s);
    }

    #[test]
    fn deref_and_iter() {
        let s = SetI::from_vec(vec![iv(1, 2), iv(4, 6)]);
        // Deref to slice
        let slice: &[Interval<i32>] = &s;
        assert_eq!(slice.len(), 2);
        // Iter over &Set
        let collected: Vec<_> = (&s).into_iter().copied().collect();
        assert_eq!(collected, vec![iv(1, 2), iv(4, 6)]);
        // Iter over &mut Set
        let mut s2 = s.clone();
        for seg in (&mut s2).into_iter() {
            // nop mutation; just ensure iterator type compiles
            let _ = seg.start();
        }
    }

    #[test]
    fn push_coalesced_basic_and_adjacency() {
        let mut s = SetI::new();
        s.insert_and_coalesce(iv(5, 7));
        s.insert_and_coalesce(iv(1, 3));
        // adjacency must coalesce (half-open semantics)
        s.insert_and_coalesce(iv(3, 5));
        assert_eq!(s.as_slice(), &[iv(1, 7)]);
        assert_invariants(&s);
    }

    #[test]
    fn push_coalesced_ignores_empty() {
        let mut s = SetI::new();
        s.insert_and_coalesce(iv(2, 2)); // empty
        assert!(s.is_empty());
        s.insert_and_coalesce(iv(2, 3));
        s.insert_and_coalesce(iv(3, 3)); // empty adjacency should not affect
        assert_eq!(s.as_slice(), &[iv(2, 3)]);
        assert_invariants(&s);
    }

    #[test]
    fn push_disjoint_tail_fast_path() {
        let mut s = SetI::new();
        s.append_and_coalesce_tail(iv(1, 3));
        s.append_and_coalesce_tail(iv(3, 5)); // merges -> [1,5)
        s.append_and_coalesce_tail(iv(10, 12));
        s.append_and_coalesce_tail(iv(8, 9)); // out-of-order: falls back to insert_and_coalesce
        assert_eq!(s.as_slice(), &[iv(1, 5), iv(8, 9), iv(10, 12)]);
    }

    #[test]
    fn extend_from_sorted_disjoint() {
        let mut s = SetI::from_vec(vec![iv(1, 2)]);
        let tail = [iv(2, 3), iv(5, 7), iv(7, 8)];
        s.extend_from_sorted_disjoint(&tail);
        assert_eq!(s.as_slice(), &[iv(1, 3), iv(5, 8)]);
        assert_invariants(&s);
    }

    #[test]
    fn clear_and_fill_from_iter() {
        let mut s = SetI::from_vec(vec![iv(1, 10)]);
        s.clear_and_fill_from_iter([iv(1, 3), iv(9, 10), iv(3, 5), iv(5, 7)]);
        assert_eq!(s.as_slice(), &[iv(1, 7), iv(9, 10)]);
        assert_invariants(&s);
    }

    #[test]
    fn retain_and_filter_min_length() {
        let mut s = SetI::from_vec(vec![iv(1, 2), iv(4, 8), iv(9, 11)]);
        s.retain_min_length(2); // keep len >= 2
        assert_eq!(s.as_slice(), &[iv(4, 8), iv(9, 11)]);

        let s2 = SetI::from_vec(vec![iv(1, 2), iv(4, 8), iv(9, 11)]).filter_min_length(3);
        assert_eq!(s2.as_slice(), &[iv(4, 8)]);
        assert_invariants(&s);
        assert_invariants(&s2);
    }

    #[test]
    fn overlaps_query() {
        let s = SetI::from_vec(vec![iv(1, 3), iv(5, 6), iv(8, 10)]);
        assert!(s.overlaps(iv(2, 4))); // overlaps [1,3)
        assert!(s.overlaps(iv(9, 12))); // overlaps [8,10)
        assert!(!s.overlaps(iv(3, 5))); // touches only (half-open)
        assert!(!s.overlaps(iv(6, 8))); // gap
        assert!(!s.overlaps(iv(12, 15)));
    }

    #[test]
    fn contains_point_query() {
        let s = SetI::from_vec(vec![iv(1, 3), iv(5, 6), iv(8, 10)]);
        assert!(s.contains_point(1));
        assert!(s.contains_point(9));
        assert!(!s.contains_point(3)); // exclusive end
        assert!(!s.contains_point(7));
        assert!(!s.contains_point(10));
    }

    #[test]
    fn covers_query() {
        let s = SetI::from_vec(vec![iv(1, 5), iv(7, 10)]);
        assert!(s.covers(iv(2, 4))); // inside first run
        assert!(s.covers(iv(7, 9))); // inside second run
        assert!(!s.covers(iv(4, 8))); // straddles a gap
        assert!(s.covers(iv(7, 7))); // empty requirement
        assert!(!s.covers(iv(0, 2))); // left edge not covered
        assert!(!s.covers(iv(9, 11))); // right edge not fully covered
    }

    #[test]
    fn clamped_into_and_clamped() {
        let s = SetI::from_vec(vec![iv(1, 5), iv(8, 12)]);
        let bounds = iv(3, 10);
        let cl = s.clamped(bounds);
        assert_eq!(cl.as_slice(), &[iv(3, 5), iv(8, 10)]);

        let mut out = SetI::new();
        s.clamped_into(bounds, &mut out);
        assert_eq!(out.as_slice(), cl.as_slice());
        assert_invariants(&out);
    }

    #[test]
    fn clamped_with_no_overlap_yields_empty() {
        let s = SetI::from_vec(vec![iv(1, 2), iv(5, 6)]);
        assert!(s.clamped(iv(2, 5)).is_empty());
    }

    #[test]
    fn union_basic_and_adjacency() {
        let a = SetI::from_vec(vec![iv(1, 3), iv(7, 9)]);
        let b = SetI::from_vec(vec![iv(2, 5), iv(9, 12)]);
        let u = a.union(&b);
        assert_eq!(u.as_slice(), &[iv(1, 5), iv(7, 12)]);

        let mut out = SetI::new();
        a.union_into(&b, &mut out);
        assert_eq!(out.as_slice(), u.as_slice());
        assert_invariants(&out);
    }

    #[test]
    fn union_with_empty_identity() {
        let a = SetI::from_vec(vec![iv(1, 3)]);
        let e = SetI::new();
        assert_eq!(a.union(&e).as_slice(), a.as_slice());
        assert_eq!(e.union(&a).as_slice(), a.as_slice());
    }

    #[test]
    fn intersection_basic() {
        let a = SetI::from_vec(vec![iv(1, 5), iv(7, 10)]);
        let b = SetI::from_vec(vec![iv(3, 8)]);
        let mut out = SetI::new();
        a.intersection_into(&b, &mut out);
        assert_eq!(out.as_slice(), &[iv(3, 5), iv(7, 8)]);
        assert_invariants(&out);
    }

    #[test]
    fn intersection_disjoint_or_touching_empty() {
        let a = SetI::from_vec(vec![iv(1, 3), iv(5, 7)]);
        let b = SetI::from_vec(vec![iv(3, 5), iv(7, 9)]); // only touching
        let mut out = SetI::new();
        a.intersection_into(&b, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn subtract_basic_cases() {
        let a = SetI::from_vec(vec![iv(1, 5), iv(8, 12)]);
        let b = SetI::from_vec(vec![iv(3, 10)]);

        // Expect: [1,3) from the first, and [10,12) from the second
        let sub = a.subtract(&b);
        assert_eq!(sub.as_slice(), &[iv(1, 3), iv(10, 12)]);
        assert_invariants(&sub);

        let mut out = SetI::new();
        a.subtract_into(&b, &mut out);
        assert_eq!(out.as_slice(), sub.as_slice());
    }

    #[test]
    fn subtract_disjoint_no_change() {
        let a = SetI::from_vec(vec![iv(1, 3), iv(5, 7)]);
        let b = SetI::from_vec(vec![iv(8, 9)]);
        assert_eq!(a.subtract(&b).as_slice(), a.as_slice());
    }

    #[test]
    fn subtract_full_cover_yields_empty() {
        let a = SetI::from_vec(vec![iv(1, 3), iv(5, 7)]);
        let b = SetI::from_vec(vec![iv(0, 10)]);
        assert!(a.subtract(&b).is_empty());
    }

    #[test]
    fn subtract_interval_variants() {
        let base = SetI::from_vec(vec![iv(2, 10)]);

        // Cut middle -> splits into two
        let mut out = SetI::new();
        base.subtract_interval_into(iv(4, 6), &mut out);
        assert_eq!(out.as_slice(), &[iv(2, 4), iv(6, 10)]);
        assert_invariants(&out);
    }

    #[test]
    fn gaps_within_basic() {
        let s = SetI::from_vec(vec![iv(2, 4), iv(6, 7), iv(9, 12)]);
        let gaps = s.gaps_within(iv(1, 13));
        assert_eq!(gaps.as_slice(), &[iv(1, 2), iv(4, 6), iv(7, 9), iv(12, 13)]);
        assert_invariants(&gaps);
    }

    #[test]
    fn gaps_within_empty_set_returns_bounds() {
        let s = SetI::new();
        let g = s.gaps_within(iv(5, 9));
        assert_eq!(g.as_slice(), &[iv(5, 9)]);
    }

    #[test]
    fn gaps_within_partial_cover() {
        let s = SetI::from_vec(vec![iv(0, 2), iv(4, 5), iv(8, 10)]);
        let g = s.gaps_within(iv(1, 9));
        assert_eq!(g.as_slice(), &[iv(2, 4), iv(5, 8)]);
    }

    #[test]
    fn clamped_edge_touching_is_empty() {
        let s = SetI::from_vec(vec![iv(1, 3), iv(5, 7)]);
        assert!(s.clamped(iv(3, 5)).is_empty());
    }

    #[test]
    fn coalesce_in_place_merges_and_sorts() {
        let mut v = vec![
            iv(5, 7),
            iv(1, 2),
            iv(2, 3),
            iv(7, 8),
            iv(9, 11),
            iv(10, 12),
        ];
        SetI::coalesce_unsorted_in_place(&mut v);
        assert_eq!(v, vec![iv(1, 3), iv(5, 8), iv(9, 12)]);
        // double run should be idempotent
        SetI::coalesce_unsorted_in_place(&mut v);
        assert_eq!(v, vec![iv(1, 3), iv(5, 8), iv(9, 12)]);
    }

    #[test]
    fn invariants_after_ops() {
        let s = SetI::from_vec(vec![iv(5, 9), iv(1, 3), iv(3, 5), iv(12, 15)]);
        assert_invariants(&s);

        let t = SetI::from_vec(vec![iv(2, 6), iv(10, 11), iv(14, 18)]);
        let mut u = SetI::new();
        s.union_into(&t, &mut u);
        assert_invariants(&u);

        let mut inter = SetI::new();
        s.intersection_into(&t, &mut inter);
        assert_invariants(&inter);

        let mut sub = SetI::new();
        s.subtract_into(&t, &mut sub);
        assert_invariants(&sub);

        let cl = s.clamped(iv(0, 20));
        assert_invariants(&cl);
    }
}
