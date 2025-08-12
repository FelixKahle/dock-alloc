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

use crate::igt::{FreeIntervalIter, IntervalGapTree};
use num_traits::{Bounded, One, ToPrimitive, Unsigned, Zero};
use std::collections::BTreeSet;
use std::ops::{Add, Bound, Range, RangeBounds};

/// A trait for data structures that manage a collection of "free" and "occupied"
/// integer segments over a fixed-size total range `[0, len)`.
///
/// This abstraction allows for different underlying implementations (e.g., a segment tree,
/// a B-Tree set of intervals) to be used interchangeably for tracking resource
/// allocation, scheduling, or any similar problem domain.
pub trait Quay {
    /// The iterator type that yields free intervals.
    ///
    /// This iterator should yield ranges of free segments that are at least `required_len` long.
    /// The lifetime `'a` indicates that the iterator can borrow from the `Quay`
    /// implementation, allowing it to access the internal state without needing to own it.
    ///
    /// # Lifetime
    /// `'a` is the lifetime of the `Quay` implementation, ensuring that the iterator
    /// does not outlive the `Quay` instance it is iterating over.
    type FreeIter<'a>: Iterator<Item=std::ops::Range<usize>> + 'a
    where
        Self: 'a;

    /// Marks all segments within the given range as `Occupied`.
    ///
    /// # Arguments
    /// * `range` - A `RangeBounds<usize>` specifying the segments to occupy.
    fn occupy<R: RangeBounds<usize>>(&mut self, range: R);

    /// Checks if all segments within the given range are `Occupied`.
    ///
    /// # Arguments
    /// * `range` - A `RangeBounds<usize>` specifying the segments to check.
    ///
    /// # Returns
    /// `true` if the entire range is occupied, `false` otherwise.
    fn check_occupied<R: RangeBounds<usize>>(&mut self, range: R) -> bool;

    /// Marks all segments within the given range as `Free`.
    ///
    /// # Arguments
    /// * `range` - A `RangeBounds<usize>` specifying the segments to free.
    fn free<R: RangeBounds<usize>>(&mut self, range: R);

    /// Checks if all segments within the given range are `Free`.
    ///
    /// # Arguments
    /// * `range` - A `RangeBounds<usize>` specifying the segments to check.
    ///
    /// # Returns
    /// `true` if the entire range is free, `false` otherwise.
    fn check_free<R: RangeBounds<usize>>(&mut self, range: R) -> bool;

    /// Returns an iterator over all free intervals of at least `required_len`
    /// that are contained within the given `range`.
    ///
    /// # Arguments
    /// * `required_len` - The minimum size of a free interval to be reported.
    /// * `range` - The `RangeBounds` to search within.
    ///
    /// # Returns
    /// An iterator yielding `Range<usize>` for each qualifying free interval.
    fn iter_free_intervals<R>(&mut self, required_len: usize, range: R) -> Self::FreeIter<'_>
    where
        R: RangeBounds<usize>;
}

/// An implementation of the `Quay` trait backed by an `IntervalGapTree`.
///
/// This struct acts as a wrapper, providing a `Quay` interface to the high-performance
/// segment tree implementation. It is ideal for scenarios with a very large number of
/// segments where the performance of range updates and queries is critical.
pub struct IntervalGapTreeQuay<T>
where
    T: Unsigned + Copy + Zero + One + Ord + Add<Output=T> + Bounded + ToPrimitive,
{
    tree: IntervalGapTree<T>,
}

impl<T> IntervalGapTreeQuay<T>
where
    T: Unsigned + Copy + Zero + One + Ord + Add<Output=T> + Bounded + ToPrimitive,
{
    /// Creates a new `IntervalGapTreeQuay`.
    ///
    /// # Arguments
    /// * `length` - The total number of segments to manage.
    /// * `initially_free` - If `true`, all segments start as `Free`; otherwise, `Occupied`.
    ///
    /// # Returns
    /// A new instance of `IntervalGapTreeQuay`.
    ///
    /// # Example
    /// ```
    /// # use crate::solver::quay::{IntervalGapTreeQuay, Quay};
    /// let mut quay = IntervalGapTreeQuay::<u32>::new(100, true);
    /// assert!(quay.check_free(..));
    /// ```
    pub fn new(len: usize, initially_free: bool) -> Self {
        Self {
            tree: IntervalGapTree::new(len, initially_free),
        }
    }

    /// Returns the total number of segments managed by the quay.
    ///
    /// # Returns
    /// The total number of segments as `usize`.
    pub fn len(&self) -> usize {
        self.tree.segment_count()
    }

    /// Returns `true` if the quay manages zero segments.
    ///
    /// # Returns
    /// `true` if the quay is empty, `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.tree.segment_count() == 0
    }
}

impl<T> Quay for IntervalGapTreeQuay<T>
where
    T: Unsigned + Copy + Zero + One + Ord + Add<Output=T> + Bounded + ToPrimitive,
{
    type FreeIter<'a> = FreeIntervalIter<'a, T>
    where
        Self: 'a;
    #[inline]
    fn occupy<R: RangeBounds<usize>>(&mut self, range: R) {
        self.tree.occupy(range);
    }

    #[inline]
    fn check_occupied<R: RangeBounds<usize>>(&mut self, range: R) -> bool {
        self.tree.check_occupied(range)
    }

    #[inline]
    fn free<R: RangeBounds<usize>>(&mut self, range: R) {
        self.tree.free(range);
    }

    #[inline]
    fn check_free<R: RangeBounds<usize>>(&mut self, range: R) -> bool {
        self.tree.check_free(range)
    }

    #[inline]
    fn iter_free_intervals<R>(&mut self, required_len: usize, range: R) -> Self::FreeIter<'_>
    where
        R: RangeBounds<usize>,
    {
        self.tree.iter_free_intervals(required_len, range)
    }
}

/// Represents a single, contiguous, half-open interval `[start, end)`.
///
/// This internal struct is used by `BTreeSetQuay` to store the set of free intervals.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Segment {
    /// The starting index of the segment (inclusive).
    start: usize,
    /// The ending index of the segment (exclusive).
    end: usize,
}

impl Segment {
    /// Checks if the segment has a length of zero.
    ///
    /// A segment is considered empty if `start` is greater than or equal to `end`.
    ///
    /// # Returns
    /// `true` if the segment is empty, `false` otherwise.
    #[inline]
    fn is_empty(&self) -> bool {
        self.start >= self.end
    }

    /// Checks if a given point is contained within the segment.
    ///
    /// A point is contained in the segment if it is greater than or equal to `start`
    /// and less than `end`.
    ///
    /// # Arguments
    /// * `position` - The position to check for containment within the segment.
    ///
    /// # Returns
    /// `true` if the position is within the segment, `false` otherwise.
    #[inline]
    fn contains(&self, position: usize) -> bool {
        self.start <= position && position < self.end
    }
}

impl Ord for Segment {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.start.cmp(&other.start) {
            std::cmp::Ordering::Equal => self.end.cmp(&other.end),
            order => order,
        }
    }
}
impl PartialOrd for Segment {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// An implementation of the `Quay` trait backed by a `BTreeSet` of free intervals.
///
/// This implementation maintains a sorted set of non-overlapping `Segment`s
/// that represent the currently free portions of the total range.
///
/// # Invariants
/// - The `free_segments` set contains disjoint, maximally-merged `[start, end)` segments.
/// - All segments lie within the total range `[0, len)`.
///
/// This approach is generally simpler than a segment tree but may be slower for
/// workloads with many small, fragmented updates.
pub struct BTreeSetQuay {
    /// The total number of segments this Quay manages.
    length: usize,
    /// The sorted set of disjoint, free intervals.
    free_segments: BTreeSet<Segment>,
}

impl BTreeSetQuay {
    /// Creates a new `BTreeSetQuay`.
    ///
    /// # Arguments
    /// * `length` - The total number of segments to manage.
    /// * `initially_free` - If `true`, the entire range `[0, length)` starts as `Free`.
    ///
    /// # Returns
    /// A new instance of `BTreeSetQuay`.
    ///
    /// # Example
    /// ```
    /// # use crate::solver::quay::{BTreeSetQuay, Quay};
    /// let mut quay = BTreeSetQuay::new(100, false);
    /// quay.free(10..20);
    /// assert!(quay.check_free(10..20));
    /// assert!(quay.check_occupied(0..10));
    /// ```
    pub fn new(len: usize, initially_free: bool) -> Self {
        let mut free = BTreeSet::new();
        if initially_free && len > 0 {
            free.insert(Segment { start: 0, end: len });
        }
        Self {
            length: len,
            free_segments: free,
        }
    }

    /// Returns the total number of segments managed by the quay.
    ///
    /// # Returns
    /// The total number of segments as `usize`.
    #[inline]
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns `true` if the quay manages zero segments.
    ///
    /// # Returns
    /// `true` if the quay is empty, `false` otherwise.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Finds the last free segment that starts at or before a given position.
    ///
    /// This method is used internally to efficiently find the segment that
    /// contains or precedes a specific index `x`.
    ///
    /// # Arguments
    /// * `x` - The position to probe for a segment.
    ///
    /// # Returns
    /// An `Option<Segment>` that is the last segment starting at or before `x`, or `None`
    /// if no such segment exists.
    #[inline]
    fn segment_before_or_at(&self, x: usize) -> Option<Segment> {
        let probe = Segment {
            start: x,
            end: usize::MAX,
        };
        self.free_segments.range(..=probe).next_back().copied()
    }

    /// Normalizes a `RangeBounds` into a concrete, half-open `Range<usize>`,
    /// clamping it to the valid range `[0, self.length)`.
    ///
    /// This method ensures that the start and end bounds are within the valid range.
    ///
    /// # Arguments
    /// * `range` - A `RangeBounds<usize>` that specifies the range to normalize.
    ///
    /// # Returns
    /// A `Range<usize>` that is guaranteed to be within `[0, self.length)`.
    ///
    #[inline(always)]
    fn normalize(&self, range: impl RangeBounds<usize>) -> Range<usize> {
        let start = match range.start_bound() {
            Bound::Included(&s) => s,
            Bound::Excluded(&s) => s.saturating_add(1),
            Bound::Unbounded => 0,
        };
        let mut end = match range.end_bound() {
            Bound::Included(&e) => e.saturating_add(1),
            Bound::Excluded(&e) => e,
            Bound::Unbounded => self.length,
        };
        let start = start.min(self.length);
        end = end.min(self.length);
        start..end
    }

    /// Internal helper to add a free interval, merging with any adjacent or
    /// overlapping free segments to maintain the invariant of maximally merged blocks.
    ///
    /// # Arguments
    /// * `r` - A `Range<usize>` representing the segment to add as free.
    fn add_free(&mut self, r: Range<usize>) {
        let mut new_start = r.start;
        let mut new_end = r.end;
        if new_start >= new_end {
            return;
        }

        if let Some(seg) = self.segment_before_or_at(new_start) && seg.end >= new_start {
            new_start = seg.start.min(new_start);
            new_end = new_end.max(seg.end);
            self.free_segments.remove(&seg);
        }

        while let Some(&seg) = self
            .free_segments
            .range(Segment { start: new_start, end: 0 }..)
            .next()
        {
            if seg.start > new_end {
                break;
            }
            new_end = new_end.max(seg.end);
            self.free_segments.remove(&seg);
        }

        self.free_segments.insert(Segment { start: new_start, end: new_end });
    }

    /// Internal helper to remove (occupy) an interval from the free-set. This may
    /// involve splitting an existing free segment into two smaller ones.
    ///
    /// This method ensures that the free segments are updated correctly, removing
    /// the occupied portion and potentially splitting existing segments
    /// into smaller segments if necessary.
    ///
    /// # Arguments
    /// * `r` - A `Range<usize>` representing the segment to remove from free segments.
    fn remove_free(&mut self, r: Range<usize>) {
        let start = r.start;
        let end = r.end;
        if start >= end {
            return;
        }

        let mut overlaps: Vec<Segment> = Vec::new();

        if let Some(seg) = self.segment_before_or_at(start) && seg.end > start {
            overlaps.push(seg);
        }

        for &segment in self.free_segments
            .range(Segment { start, end: 0 }..)
            .take_while(|seg| seg.start < end)
        {
            overlaps.push(segment);
        }

        for seg in overlaps {
            self.free_segments.remove(&seg);
            if seg.start < start {
                self.free_segments.insert(Segment { start: seg.start, end: start });
            }
            if seg.end > end {
                self.free_segments.insert(Segment { start: end, end: seg.end });
            }
        }
    }
}

/// An iterator that yields free intervals from a `BTreeSetQuay`.
///
/// This iterator is designed to return ranges of free segments that are at least
/// `required_len` long, and it respects a search limit defined by `search_end`.
///
/// # Lifetime
/// `'a` is the lifetime of the `BTreeSetQuay` instance, ensuring that the iterator
/// does not outlive the data it is iterating over.
pub struct BTreeSetQuayFreeIter<'a> {
    range_iter: std::collections::btree_set::Range<'a, Segment>,
    pending_range: Option<Range<usize>>,
    search_end: usize,
    required_len: usize,
}

impl<'a> Iterator for BTreeSetQuayFreeIter<'a> {
    type Item = Range<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(mut range) = self.pending_range.take() {
            range.end = range.end.min(self.search_end);
            if range.end > range.start && (range.end - range.start) >= self.required_len {
                return Some(range);
            }
        }

        for segment in self.range_iter.by_ref() {
            if segment.start >= self.search_end {
                return None;
            }
            let start = segment.start;
            let end = segment.end.min(self.search_end);
            if end > start && (end - start) >= self.required_len {
                return Some(start..end);
            }
        }
        None
    }
}

impl Quay for BTreeSetQuay {
    type FreeIter<'a> = BTreeSetQuayFreeIter<'a>
    where
        Self: 'a;

    #[inline]
    fn occupy<R: RangeBounds<usize>>(&mut self, range: R) {
        let normalized_range = self.normalize(range);
        self.remove_free(normalized_range);
    }

    #[inline]
    fn check_occupied<R: RangeBounds<usize>>(&mut self, range: R) -> bool {
        if self.length == 0 {
            return false;
        }
        let query_range = self.normalize(range);
        if query_range.is_empty() {
            return false; // empty range is never "occupied"
        }

        if let Some(segment) = self.segment_before_or_at(query_range.start)
            && segment.end > query_range.start
        {
            return false;
        }

        if self
            .free_segments
            .range(Segment { start: query_range.start, end: 0 }..)
            .take_while(|segment| segment.start < query_range.end)
            .next()
            .is_some()
        {
            return false;
        }
        true
    }

    #[inline]
    fn free<R: RangeBounds<usize>>(&mut self, range: R) {
        let normalized_range = self.normalize(range);
        self.add_free(normalized_range);
    }

    #[inline]
    fn check_free<R: RangeBounds<usize>>(&mut self, range: R) -> bool {
        if self.length == 0 {
            return true;
        }
        let query_range = self.normalize(range);
        if query_range.is_empty() {
            return true;
        }

        let mut current_position = query_range.start;
        let end_bound = query_range.end;

        while current_position < end_bound {
            if let Some(segment) = self.segment_before_or_at(current_position)
                && segment.end > current_position
            {
                current_position = segment.end.min(end_bound);
                continue;
            }
            return false;
        }
        true
    }

    fn iter_free_intervals<R>(&mut self, required_len: usize, range: R) -> BTreeSetQuayFreeIter<'_>
    where
        R: RangeBounds<usize>,
    {
        let search_range = self.normalize(range);
        let pending = self
            .segment_before_or_at(search_range.start)
            .and_then(|segment| {
                (segment.start < search_range.start && segment.end > search_range.start)
                    .then_some(search_range.start..segment.end.min(search_range.end))
            });

        let range_iter = self.free_segments.range(Segment { start: search_range.start, end: 0 }..);
        BTreeSetQuayFreeIter {
            range_iter,
            pending_range: pending,
            search_end: search_range.end,
            required_len,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{BTreeSetQuay, IntervalGapTreeQuay, Quay};
    use std::ops::RangeBounds;

    fn mk_pair(len: usize, initially_free: bool) -> (BTreeSetQuay, IntervalGapTreeQuay<u32>) {
        (BTreeSetQuay::new(len, initially_free), IntervalGapTreeQuay::new(len, initially_free))
    }

    fn collect<Q, R>(q: &mut Q, k: usize, range: R) -> Vec<std::ops::Range<usize>>
    where
        Q: Quay,
        R: RangeBounds<usize>,
    {
        q.iter_free_intervals(k, range).collect()
    }

    fn assert_same_state<R>(a: &mut BTreeSetQuay, b: &mut IntervalGapTreeQuay<u32>, range: R)
    where
        R: RangeBounds<usize> + Clone,
    {
        assert_eq!(a.check_free(range.clone()), b.check_free(range.clone()));
        assert_eq!(a.check_occupied(range.clone()), b.check_occupied(range.clone()));
    }

    fn assert_same_iter<R>(a: &mut BTreeSetQuay, b: &mut IntervalGapTreeQuay<u32>, k: usize, range: R)
    where
        R: RangeBounds<usize> + Clone,
    {
        let ia = collect(a, k, range.clone());
        let ib = collect(b, k, range.clone());
        assert_eq!(ia, ib);
    }

    #[test]
    fn new_zero_len_free() {
        let (mut bt, mut ig) = mk_pair(0, true);
        assert!(bt.is_empty());
        assert!(ig.is_empty());
        assert!(bt.check_free(..));
        assert!(ig.check_free(..));
        assert!(!bt.check_occupied(..));
        assert!(!ig.check_occupied(..));
        assert!(collect(&mut bt, 1, ..).is_empty());
        assert!(collect(&mut ig, 1, ..).is_empty());
    }

    #[test]
    fn new_all_free_len_n() {
        let n = 8;
        let (mut bt, mut ig) = mk_pair(n, true);
        assert!(bt.check_free(..));
        assert!(ig.check_free(..));
        assert_eq!(collect(&mut bt, 1, ..), vec![0..n]);
        assert_eq!(collect(&mut ig, 1, ..), vec![0..n]);
    }

    #[test]
    fn new_all_occupied_len_n() {
        let n = 8;
        let (mut bt, mut ig) = mk_pair(n, false);
        assert!(bt.check_occupied(..));
        assert!(ig.check_occupied(..));
        assert!(collect(&mut bt, 1, ..).is_empty());
        assert!(collect(&mut ig, 1, ..).is_empty());
    }

    #[test]
    fn empty_range_is_free_not_occupied() {
        let (mut bt, mut ig) = mk_pair(10, false);
        assert!(bt.check_free(3..3));
        assert!(ig.check_free(3..3));
        assert!(!bt.check_occupied(3..3));
        assert!(!ig.check_occupied(3..3));
    }

    #[test]
    fn range_clamps_past_end_free() {
        let n = 10;
        let (mut bt, mut ig) = mk_pair(n, false);
        bt.free(8..20);
        ig.free(8..20);
        assert_same_state(&mut bt, &mut ig, 0..n);
        assert_same_iter(&mut bt, &mut ig, 1, ..);
        assert_eq!(collect(&mut bt, 1, ..), vec![8..10]);
    }

    #[test]
    fn start_beyond_len_noop() {
        let n = 10;
        let (mut bt, mut ig) = mk_pair(n, false);
        bt.free(11..30);
        ig.free(11..30);
        assert!(collect(&mut bt, 1, ..).is_empty());
        assert_same_state(&mut bt, &mut ig, ..);
    }

    #[test]
    fn inclusive_end_is_honored() {
        let (mut bt, mut ig) = mk_pair(12, false);
        bt.free(4..=8); // => [4,9)
        ig.free(4..=8);
        assert_eq!(collect(&mut bt, 1, ..), vec![4..9]);
        assert_same_iter(&mut bt, &mut ig, 1, ..);
    }

    #[test]
    fn inclusive_open_mix() {
        let (mut bt, mut ig) = mk_pair(12, true);
        bt.occupy(..=3); // [0,4)
        ig.occupy(..=3);
        bt.occupy(10..); // [10,12)
        ig.occupy(10..);
        assert_eq!(collect(&mut bt, 1, ..), vec![4..10]);
        assert_same_iter(&mut bt, &mut ig, 1, ..);
    }

    #[test]
    fn free_adjacency_merges() {
        let (mut bt, mut ig) = mk_pair(10, false);
        bt.free(2..4);
        ig.free(2..4);
        bt.free(4..6);
        ig.free(4..6);
        assert_eq!(collect(&mut bt, 1, ..), vec![2..6]);
        assert_same_iter(&mut bt, &mut ig, 1, ..);
    }

    #[test]
    fn free_bridge_merges_two_runs() {
        let (mut bt, mut ig) = mk_pair(12, false);
        bt.free(1..3);
        bt.free(7..9);
        ig.free(1..3);
        ig.free(7..9);
        bt.free(3..7); // bridge
        ig.free(3..7);
        assert_eq!(collect(&mut bt, 1, ..), vec![1..9]);
        assert_same_iter(&mut bt, &mut ig, 1, ..);
    }

    #[test]
    fn occupy_splits_a_free_run() {
        let n = 10;
        let (mut bt, mut ig) = mk_pair(n, true);
        bt.occupy(3..7);
        ig.occupy(3..7);
        assert_eq!(collect(&mut bt, 1, ..), vec![0..3, 7..10]);
        assert_same_iter(&mut bt, &mut ig, 1, ..);
    }

    #[test]
    fn occupy_inclusive_right_splits() {
        let n = 10;
        let (mut bt, mut ig) = mk_pair(n, true);
        bt.occupy(3..=5); // [3,6)
        ig.occupy(3..=5);
        assert_eq!(collect(&mut bt, 1, ..), vec![0..3, 6..10]);
        assert_same_iter(&mut bt, &mut ig, 1, ..);
    }

    #[test]
    fn free_twice_is_idempotent() {
        let (mut bt, mut ig) = mk_pair(10, false);
        bt.free(2..5);
        ig.free(2..5);
        bt.free(2..5);
        ig.free(2..5);
        assert_eq!(collect(&mut bt, 1, ..), vec![2..5]);
        assert_same_iter(&mut bt, &mut ig, 1, ..);
    }

    #[test]
    fn occupy_twice_is_idempotent() {
        let (mut bt, mut ig) = mk_pair(10, true);
        bt.occupy(4..8);
        ig.occupy(4..8);
        bt.occupy(4..8);
        ig.occupy(4..8);
        assert_eq!(collect(&mut bt, 1, ..), vec![0..4, 8..10]);
        assert_same_iter(&mut bt, &mut ig, 1, ..);
    }

    #[test]
    fn window_clips_left_and_uses_pending_predecessor() {
        let (mut bt, mut ig) = mk_pair(12, false);
        bt.free(2..8);
        ig.free(2..8);
        assert_eq!(collect(&mut bt, 1, 4..11), vec![4..8]);
        assert_same_iter(&mut bt, &mut ig, 1, 4..11);
    }

    #[test]
    fn window_clips_right() {
        let (mut bt, mut ig) = mk_pair(20, false);
        bt.free(5..15);
        ig.free(5..15);
        assert_eq!(collect(&mut bt, 1, 10..12), vec![10..12]);
        assert_same_iter(&mut bt, &mut ig, 1, 10..12);
    }

    #[test]
    fn required_len_filters_short_runs() {
        let (mut bt, mut ig) = mk_pair(20, false);
        bt.free(5..10); // len 5
        ig.free(5..10);
        assert!(collect(&mut bt, 6, ..).is_empty());
        assert_same_iter(&mut bt, &mut ig, 6, ..);
    }

    #[test]
    fn required_len_with_window_after_clip() {
        let (mut bt, mut ig) = mk_pair(20, false);
        bt.free(0..5); // len 5
        ig.free(0..5);
        assert!(collect(&mut bt, 3, 3..5).is_empty());
        assert_same_iter(&mut bt, &mut ig, 3, 3..5);
    }

    #[test]
    fn required_len_exact_match() {
        let (mut bt, mut ig) = mk_pair(20, false);
        bt.free(10..13); // len 3
        ig.free(10..13);
        assert_eq!(collect(&mut bt, 3, ..), vec![10..13]);
        assert_same_iter(&mut bt, &mut ig, 3, ..);
    }

    #[test]
    fn equivalence_after_mixed_updates_small() {
        let (mut bt, mut ig) = mk_pair(32, false);
        bt.free(5..15);
        ig.free(5..15);
        bt.free(20..27);
        ig.free(20..27);
        bt.occupy(22..=23);
        ig.occupy(22..=23); // removes [22,24)
        bt.free(12..18);
        ig.free(12..18);
        bt.occupy(..3);
        ig.occupy(..3);
        bt.free(0..1);
        ig.free(0..1);

        assert_same_iter(&mut bt, &mut ig, 1, ..);
        assert_same_iter(&mut bt, &mut ig, 3, 0..20);
        assert_same_iter(&mut bt, &mut ig, 4, 10..30);
        assert_same_state(&mut bt, &mut ig, 12..18);
        assert_same_state(&mut bt, &mut ig, 22..25);
    }

    #[test]
    fn free_then_occupy_exact_edges() {
        let (mut bt, mut ig) = mk_pair(10, false);
        bt.free(2..8);
        ig.free(2..8);
        bt.occupy(2..8);
        ig.occupy(2..8);
        assert!(collect(&mut bt, 1, ..).is_empty());
        assert_same_iter(&mut bt, &mut ig, 1, ..);
    }

    #[test]
    fn occupy_then_free_superset() {
        let (mut bt, mut ig) = mk_pair(12, true);
        bt.occupy(4..8);
        ig.occupy(4..8);
        bt.free(2..10);
        ig.free(2..10);
        assert_eq!(collect(&mut bt, 1, ..), vec![0..12]);
        assert_same_iter(&mut bt, &mut ig, 1, ..);
    }

    #[test]
    fn required_len_bigger_than_total() {
        let (mut bt, mut ig) = mk_pair(16, true);
        assert!(collect(&mut bt, 17, ..).is_empty());
        assert_same_iter(&mut bt, &mut ig, 17, ..);
    }

    #[test]
    fn checks_match_iter_presence() {
        let (mut bt, mut ig) = mk_pair(16, false);
        bt.free(4..6);
        ig.free(4..6);
        assert!(bt.check_free(4..6));
        assert!(ig.check_free(4..6));
        assert!(!bt.check_occupied(4..6));
        assert!(!ig.check_occupied(4..6));
        assert!(bt.check_occupied(..4));
        assert!(ig.check_occupied(..4));
    }

    #[test]
    fn no_duplicate_when_window_starts_at_segment_start() {
        let mut q = super::BTreeSetQuay::new(8, true);
        let v: Vec<_> = q.iter_free_intervals(1, 0..8).collect();
        assert_eq!(v, vec![0..8]);
    }
}
