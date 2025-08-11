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

use num_traits::{Bounded, One, ToPrimitive, Unsigned, Zero};
use std::cmp::max;
use std::ops::{Add, Bound, RangeBounds};

/// Represents the state of a pending lazy-propagation update.
///
/// This enum is used internally to mark nodes for deferred updates,
/// which is key to the efficiency of range-based operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LazyState {
    /// No pending update needs to be propagated.
    None,
    /// A pending update to mark the range as `Free`.
    Free,
    /// A pending update to mark the range as `Occupied`.
    Occupied,
}

impl std::fmt::Display for LazyState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LazyState::None => write!(f, "None"),
            LazyState::Free => write!(f, "Free"),
            LazyState::Occupied => write!(f, "Occupied"),
        }
    }
}

/// An internal node of the `IntervalGapTree`.
///
/// Each node stores aggregate information about the range of segments it represents,
/// allowing for efficient queries and updates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Node<T>
where
    T: Unsigned,
{
    length_of_longest_free_prefix: T,
    length_of_longest_free_suffix: T,
    length_of_maximum_free_gap: T,
    segment_length: T,
    lazy_propagation_state: LazyState,
}

impl<T> Node<T>
where
    T: Unsigned,
{
    /// Creates a new `Node`.
    ///
    /// # Arguments
    ///
    /// * `length_of_longest_free_prefix` - The prefix value.
    /// * `length_of_longest_free_suffix` - The suffix value.
    /// * `length_of_maximum_free_gap` - The max gap value.
    /// * `segment_length` - The total length of the segment.
    /// * `lazy_propagation_state` - The initial lazy state.
    ///
    /// # Returns
    ///
    /// A new `Node` instance.
    pub fn new(
        length_of_longest_free_prefix: T,
        length_of_longest_free_suffix: T,
        length_of_maximum_free_gap: T,
        segment_length: T,
        lazy_propagation_state: LazyState,
    ) -> Self {
        Self {
            length_of_longest_free_prefix,
            length_of_longest_free_suffix,
            length_of_maximum_free_gap,
            segment_length,
            lazy_propagation_state,
        }
    }
}

impl<T> Default for Node<T>
where
    T: Unsigned,
{
    /// Creates a default, zeroed-out `Node`.
    ///
    /// # Returns
    ///
    /// A `Node` with all numeric fields set to zero and state set to `None`.
    fn default() -> Self {
        Self {
            length_of_longest_free_prefix: T::zero(),
            length_of_longest_free_suffix: T::zero(),
            length_of_maximum_free_gap: T::zero(),
            segment_length: T::zero(),
            lazy_propagation_state: LazyState::None,
        }
    }
}

impl<T> std::fmt::Display for Node<T>
where
    T: Unsigned + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Node(length_of_longest_free_prefix: {}, \
            length_of_longest_free_suffix: {}, \
            length_of_maximum_free_gap: {}, \
            segment_length: {}, \
            lazy_propagation_state: {})",
            self.length_of_longest_free_prefix,
            self.length_of_longest_free_suffix,
            self.length_of_maximum_free_gap,
            self.segment_length,
            self.lazy_propagation_state
        )
    }
}

/// A segment tree with lazy propagation, optimized for querying and updating
/// the status of contiguous intervals.
///
/// This data structure is particularly useful for problems involving resource
/// allocation, scheduling, or any domain where you need to efficiently find
/// and manage "free" or "occupied" blocks within a larger range. For example, it can
/// quickly answer questions like "what is the largest block of free memory?" or
/// "is the time slot from 10:00 to 11:30 completely available?".
///
/// It uses an iterative, non-recursive algorithm for updates and queries,
/// making it robust against stack overflow for very large numbers of segments.
///
/// # Example
///
/// ```
/// # use crate::solver::igt::IntervalGapTree;
/// let mut tree = IntervalGapTree::<u32>::new(100, true);
/// tree.occupy(10..20);
/// assert!(tree.check_occupied(10..20));
/// assert!(!tree.check_free(..));
/// ```
#[derive(Debug)]
pub struct IntervalGapTree<T>
where
    T: Unsigned + Copy + Zero + One + Ord + Add<Output=T>,
{
    total_segment_count: usize,
    leaf_node_count: usize,
    segment_tree_height: usize,
    nodes: Vec<Node<T>>,
}

impl<T> Default for IntervalGapTree<T>
where
    T: Unsigned + Copy + Zero + One + Ord + Add<Output=T>,
{
    /// Creates a new, empty `IntervalGapTree`.
    ///
    /// # Returns
    ///
    /// An empty tree with a segment count of 0.
    ///
    /// # Example
    ///
    /// ```
    /// # use crate::solver::igt::IntervalGapTree;
    /// let tree: IntervalGapTree<u32> = IntervalGapTree::default();
    /// assert_eq!(tree.segment_count(), 0);
    /// ```
    fn default() -> Self {
        Self {
            total_segment_count: 0,
            leaf_node_count: 0,
            segment_tree_height: 0,
            nodes: Vec::new(),
        }
    }
}

/// Computes the integer bit width, equivalent to `floor(log2(x)) + 1`.
///
/// This function returns the number of bits required to represent a
/// unsigned integer `x` in binary, which is useful for determining the
/// height of the segment tree based on the number of leaf nodes.
///
/// # Arguments
/// * `x` - The unsigned integer whose bit width is to be calculated.
///
/// # Returns
/// The bit width as a `usize`, which is the number of bits needed to represent `x`.
#[inline]
fn bit_width(x: usize) -> usize {
    usize::BITS as usize - x.leading_zeros() as usize
}

/// Normalizes a `RangeBounds` into a concrete, half-open `(start, end)` tuple,
/// clamping it to the valid range `[0, total_count)`.
///
/// # Arguments
/// * `total_count` - The upper bound of the valid range.
/// * `range` - The `RangeBounds` to normalize.
///
/// # Returns
/// A `(start, end)` tuple representing the normalized, half-open range.
#[inline(always)]
fn normalize_bounds(total_count: usize, range: impl RangeBounds<usize>) -> (usize, usize) {
    let start = match range.start_bound() {
        Bound::Included(&s) => s,
        Bound::Excluded(&s) => s.saturating_add(1),
        Bound::Unbounded => 0,
    };
    let mut end = match range.end_bound() {
        Bound::Included(&e) => e.saturating_add(1),
        Bound::Excluded(&e) => e,
        Bound::Unbounded => total_count,
    };
    let start = start.min(total_count);
    end = end.min(total_count);
    (start, end)
}

/// Merges two child nodes into a new parent node.
///
/// This function is the core of the segment tree's aggregation logic.
///
/// # Arguments
/// * `left` - A reference to the left child node.
/// * `right` - A reference to the right child node.
///
/// # Returns
/// A new `Node` instance representing the merged parent.
fn merge<T>(left: &Node<T>, right: &Node<T>) -> Node<T>
where
    T: Unsigned + Copy + Zero + One + Ord + Add<Output=T>,
{
    debug_assert!(left.length_of_maximum_free_gap <= left.segment_length);
    debug_assert!(right.length_of_maximum_free_gap <= right.segment_length);

    let segment_length = left.segment_length + right.segment_length;

    let length_of_longest_free_prefix = if left.length_of_longest_free_prefix == left.segment_length
    {
        left.segment_length + right.length_of_longest_free_prefix
    } else {
        left.length_of_longest_free_prefix
    };

    let length_of_longest_free_suffix = if right.length_of_longest_free_suffix == right.segment_length
    {
        right.segment_length + left.length_of_longest_free_suffix
    } else {
        right.length_of_longest_free_suffix
    };

    let cross = left.length_of_longest_free_suffix + right.length_of_longest_free_prefix;
    let length_of_maximum_free_gap = max(
        left.length_of_maximum_free_gap,
        max(right.length_of_maximum_free_gap, cross),
    );

    debug_assert!(length_of_maximum_free_gap <= segment_length);

    Node::new(
        length_of_longest_free_prefix,
        length_of_longest_free_suffix,
        length_of_maximum_free_gap,
        segment_length,
        LazyState::None,
    )
}

impl<T> IntervalGapTree<T>
where
    T: Unsigned + Copy + Zero + One + Ord + Add<Output=T> + Bounded + ToPrimitive,
{
    /// Creates a new `IntervalGapTree` with a specified number of segments.
    ///
    /// # Arguments
    /// * `initial_number_of_segments` - The total number of segments to manage.
    /// * `initially_free` - If `true`, all segments are initialized as `Free`.
    ///   If `false`, they are initialized as `Occupied`.
    ///
    /// # Returns
    /// A new `IntervalGapTree` instance.
    ///
    /// # Example
    /// ```
    /// # use crate::solver::igt::IntervalGapTree;
    /// // Create a tree with 10 segments, all initially occupied.
    /// let mut tree: IntervalGapTree<u32> = IntervalGapTree::new(10, false);
    /// assert_eq!(tree.segment_count(), 10);
    /// assert!(tree.check_occupied(..));
    ///
    /// // Create a tree with 8 segments, all initially free.
    /// let mut tree2: IntervalGapTree<u64> = IntervalGapTree::new(8, true);
    /// assert_eq!(tree2.segment_count(), 8);
    /// assert!(tree2.check_free(..));
    /// ```
    pub fn new(initial_number_of_segments: usize, initially_free: bool) -> Self {
        if initial_number_of_segments == 0 {
            return Self::default();
        }

        let total_segment_count = initial_number_of_segments;
        let leaf_node_count = initial_number_of_segments.next_power_of_two();
        let max_t = T::max_value().to_usize().unwrap_or(usize::MAX);
        assert!(leaf_node_count <= max_t, "T too small for leaf count");
        let segment_tree_height = bit_width(leaf_node_count);

        let mut nodes = vec![Node::<T>::default(); 2 * leaf_node_count];

        let one = T::one();
        let zero = T::zero();

        let leaf_start = leaf_node_count;
        let user_leaves_end = leaf_start + total_segment_count;
        let padded_leaves_end = 2 * leaf_node_count;

        for node in nodes.iter_mut().take(user_leaves_end).skip(leaf_start) {
            node.segment_length = one;
            if initially_free {
                node.length_of_longest_free_prefix = one;
                node.length_of_longest_free_suffix = one;
                node.length_of_maximum_free_gap = one;
            } else {
                node.length_of_longest_free_prefix = zero;
                node.length_of_longest_free_suffix = zero;
                node.length_of_maximum_free_gap = zero;
            }
            node.lazy_propagation_state = LazyState::None;
        }

        for node in nodes.iter_mut().take(padded_leaves_end).skip(user_leaves_end) {
            node.segment_length = one;
            node.length_of_longest_free_prefix = zero;
            node.length_of_longest_free_suffix = zero;
            node.length_of_maximum_free_gap = zero;
            node.lazy_propagation_state = LazyState::None;
        }

        for parent in (1..leaf_node_count).rev() {
            let left_child = parent << 1;
            let right_child = left_child | 1;
            nodes[parent] = merge(&nodes[left_child], &nodes[right_child]);
        }

        Self {
            total_segment_count,
            leaf_node_count,
            segment_tree_height,
            nodes,
        }
    }

    /// Returns the total number of segments the tree was initialized with.
    ///
    /// # Returns
    /// The number of segments as a `usize`.
    ///
    /// # Example
    /// ```
    /// # use crate::solver::igt::IntervalGapTree;
    /// let tree: IntervalGapTree<u32> = IntervalGapTree::new(42, true);
    /// assert_eq!(tree.segment_count(), 42);
    /// ```
    #[inline]
    pub fn segment_count(&self) -> usize {
        self.total_segment_count
    }

    /// Returns the number of leaf nodes in the internal tree structure.
    ///
    /// This will be the smallest power of two that is greater than or equal to
    /// the `segment_count`.
    ///
    /// # Returns
    /// The number of leaf nodes as a `usize`.
    ///
    /// # Example
    /// ```
    /// # use crate::solver::igt::IntervalGapTree;
    /// let tree: IntervalGapTree<u32> = IntervalGapTree::new(10, true);
    /// // 10 is not a power of two, so it's padded to 16.
    /// assert_eq!(tree.leaf_count(), 16);
    /// ```
    #[inline]
    pub fn leaf_count(&self) -> usize {
        self.leaf_node_count
    }

    /// Returns the height of the internal tree structure.
    ///
    /// # Returns
    /// The height of the tree as a `usize`.
    ///
    /// # Example
    /// ```
    /// # use crate::solver::igt::IntervalGapTree;
    /// // A tree with 8 leaves (a power of two) has a height of 4.
    /// let tree: IntervalGapTree<u32> = IntervalGapTree::new(8, true);
    /// assert_eq!(tree.height(), 4);
    /// ```
    #[inline]
    pub fn height(&self) -> usize {
        self.segment_tree_height
    }

    /// Returns the total number of nodes allocated for the tree.
    /// This is `2 * leaf_count`.
    ///
    /// # Returns
    /// The total number of nodes as a `usize`.
    ///
    /// # Example
    /// ```
    /// # use crate::solver::igt::IntervalGapTree;
    /// let tree: IntervalGapTree<u32> = IntervalGapTree::new(8, true);
    /// assert_eq!(tree.leaf_count(), 8);
    /// assert_eq!(tree.node_count(), 16);
    /// ```
    #[inline]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Marks all segments within the given range as `Occupied`.
    ///
    /// # Arguments
    /// * `range` - A `RangeBounds<usize>` specifying the segments to occupy.
    ///
    /// # Example
    /// ```
    /// # use crate::solver::igt::IntervalGapTree;
    /// let mut tree: IntervalGapTree<u32> = IntervalGapTree::new(10, true);
    /// assert!(tree.check_free(..));
    ///
    /// tree.occupy(3..7);
    ///
    /// assert!(tree.check_free(0..3));
    /// assert!(tree.check_occupied(3..7));
    /// assert!(tree.check_free(7..10));
    /// ```
    pub fn occupy<R: RangeBounds<usize>>(&mut self, range: R) {
        self.range_update(range, LazyState::Occupied);
    }

    /// Marks all segments within the given range as `Free`.
    ///
    /// # Arguments
    /// * `range` - A `RangeBounds<usize>` specifying the segments to free.
    ///
    /// # Example
    /// ```
    /// # use crate::solver::igt::IntervalGapTree;
    /// let mut tree: IntervalGapTree<u32> = IntervalGapTree::new(10, false);
    /// assert!(tree.check_occupied(..));
    ///
    /// tree.free(4..=8);
    ///
    /// assert!(tree.check_occupied(0..4));
    /// assert!(tree.check_free(4..=8));
    /// assert!(tree.check_occupied(9..10));
    /// ```
    pub fn free<R: RangeBounds<usize>>(&mut self, range: R) {
        self.range_update(range, LazyState::Free);
    }

    /// Checks if all segments within the given range are `Free`.
    ///
    /// # Arguments
    /// * `range` - A `RangeBounds<usize>` specifying the segments to check.
    ///
    /// # Returns
    /// `true` if the entire range is free, `false` otherwise. An empty range
    /// is considered `Free`.
    ///
    /// # Example
    /// ```
    /// # use crate::solver::igt::IntervalGapTree;
    /// let mut tree: IntervalGapTree<u32> = IntervalGapTree::new(10, true);
    /// tree.occupy(5..7);
    ///
    /// assert!(tree.check_free(0..5));
    /// assert!(!tree.check_free(4..6)); // Overlaps with the occupied part
    /// assert!(tree.check_free(2..2)); // Empty range is always free
    /// ```
    pub fn check_free<R: RangeBounds<usize>>(&mut self, range: R) -> bool {
        if self.total_segment_count == 0 {
            return true;
        }
        let (start, end) = normalize_bounds(self.total_segment_count, range);
        if start >= end {
            return true;
        }
        let node = self.range_query(start..end);
        node.length_of_maximum_free_gap == node.segment_length
    }

    /// Checks if all segments within the given range are `Occupied`.
    ///
    /// # Arguments
    /// * `range` - A `RangeBounds<usize>` specifying the segments to check.
    ///
    /// # Returns
    /// `true` if the entire range is occupied, `false` otherwise. An empty
    /// range is considered not `Occupied`.
    ///
    /// # Example
    /// ```
    /// # use crate::solver::igt::IntervalGapTree;
    /// let mut tree: IntervalGapTree<u32> = IntervalGapTree::new(10, false);
    /// tree.free(5..7);
    ///
    /// assert!(tree.check_occupied(0..5));
    /// assert!(!tree.check_occupied(4..6)); // Overlaps with the free part
    /// assert!(!tree.check_occupied(2..2)); // Empty range is never occupied
    /// ```
    pub fn check_occupied<R: RangeBounds<usize>>(&mut self, range: R) -> bool {
        if self.total_segment_count == 0 {
            return false;
        }
        let (start, end) = normalize_bounds(self.total_segment_count, range);
        if start >= end {
            return false;
        }
        let node = self.range_query(start..end);
        node.length_of_maximum_free_gap == T::zero()
    }

    /// Applies a lazy state to a single node and updates its aggregate values.
    ///
    /// This method is used to mark a node as `Free`, `Occupied`, or to clear its state.
    /// It updates the node's segment length and free/occupied metrics accordingly.
    ///
    /// # Arguments
    /// * `idx` - The index of the node to update.
    /// * `state` - The `LazyState` to apply, which can be `Free`, `Occupied`, or `None`.
    fn apply(&mut self, idx: usize, state: LazyState) {
        if self.nodes[idx].lazy_propagation_state == state
        {
            return;
        }
        let node = &mut self.nodes[idx];
        node.lazy_propagation_state = state;
        match state {
            LazyState::Free => {
                let len = node.segment_length;
                node.length_of_longest_free_prefix = len;
                node.length_of_longest_free_suffix = len;
                node.length_of_maximum_free_gap = len;
            }
            LazyState::Occupied => {
                node.length_of_longest_free_prefix = T::zero();
                node.length_of_longest_free_suffix = T::zero();
                node.length_of_maximum_free_gap = T::zero();
            }
            LazyState::None => {}
        }
    }

    /// Pushes a pending lazy update from a parent node to its direct children.
    ///
    /// This method is used to propagate updates down the tree, ensuring that
    /// child nodes reflect the parent's lazy state.
    ///
    /// # Arguments
    /// * `parent` - The index of the parent node whose state should be pushed to its children.
    fn push(&mut self, parent: usize) {
        if parent >= self.leaf_node_count {
            self.nodes[parent].lazy_propagation_state = LazyState::None;
            return;
        }
        let state = self.nodes[parent].lazy_propagation_state;
        if matches!(state, LazyState::None) {
            return;
        }
        let left_child = parent << 1;
        let right_child = left_child | 1;
        self.apply(left_child, state);
        self.apply(right_child, state);
        self.nodes[parent].lazy_propagation_state = LazyState::None;
    }

    /// Pulls updated values from children and merges them to update a parent node.
    /// This is only done if the parent has no pending lazy update.
    ///
    /// This method is used to recompute the parent's aggregate values based on its children,
    /// ensuring that the segment tree remains consistent after updates.
    ///
    /// # Arguments
    /// * `parent` - The index of the parent node to update.
    fn pull(&mut self, parent: usize) {
        if !matches!(self.nodes[parent].lazy_propagation_state, LazyState::None) {
            return;
        }
        let left_child = parent << 1;
        let right_child = left_child | 1;
        self.nodes[parent] = merge(&self.nodes[left_child], &self.nodes[right_child]);
    }

    /// The internal implementation for range updates.
    ///
    /// This method applies a lazy state to all nodes within the specified range,
    /// updating their aggregate values accordingly.
    ///
    /// # Arguments
    /// * `range` - A `RangeBounds<usize>` specifying the segments to update.
    /// * `state` - The `LazyState` to apply, which can be `Free`, `Occupied`, or `None`.
    fn range_update<R: RangeBounds<usize>>(&mut self, range: R, state: LazyState) {
        if self.total_segment_count == 0
        {
            return;
        }
        let (mut start, mut end) = normalize_bounds(self.total_segment_count, range);
        if start >= end
        {
            return;
        }

        start += self.leaf_node_count;
        end += self.leaf_node_count;

        let orig_start = start;
        let orig_end = end;

        self.push_boundary_paths(start, end);

        while start < end {
            if (start & 1) != 0 {
                self.apply(start, state);
                start += 1;
            }
            if (end & 1) != 0 {
                end -= 1;
                self.apply(end, state);
            }
            start >>= 1;
            end >>= 1;
        }

        self.pull_boundary_paths(orig_start, orig_end);
    }

    /// The internal implementation for range queries.
    ///
    /// This method retrieves the aggregate values for all segments within the specified range,
    /// allowing for efficient queries about the state of the segments.
    ///
    /// # Arguments
    /// * `range` - A `RangeBounds<usize>` specifying the segments to query.
    ///
    /// # Returns
    /// A `Node<T>` containing the aggregate values for the specified range.
    fn range_query<R: RangeBounds<usize>>(&mut self, range: R) -> Node<T> {
        if self.total_segment_count == 0 { return Node::<T>::default(); }
        let (mut start, mut end) = normalize_bounds(self.total_segment_count, range);
        if start >= end { return Node::<T>::default(); }

        start += self.leaf_node_count;
        end += self.leaf_node_count;

        self.push_boundary_paths(start, end);

        let mut left_acc = Node::<T>::default();
        let mut right_acc = Node::<T>::default();

        while start < end {
            if (start & 1) != 0 {
                left_acc = merge(&left_acc, &self.nodes[start]);
                start += 1;
            }
            if (end & 1) != 0 {
                end -= 1;
                right_acc = merge(&self.nodes[end], &right_acc);
            }
            start >>= 1;
            end >>= 1;
        }
        merge(&left_acc, &right_acc)
    }

    /// Traverses from the root down to the range boundaries, pushing any lazy updates.
    ///
    /// This method ensures that any pending updates are applied to the ancestors of the
    /// specified range, allowing for efficient updates without needing to traverse the entire tree.
    ///
    /// # Arguments
    /// * `start` - The starting index of the range.
    /// * `end` - The ending index of the range (exclusive).
    #[inline]
    fn push_boundary_paths(&mut self, start: usize, end: usize) {
        for level in (1..=self.segment_tree_height).rev() {
            let left_ancestor = start >> level;
            let right_ancestor = (end - 1) >> level;
            if left_ancestor > 0 {
                self.push(left_ancestor);
            }
            if right_ancestor > 0 && right_ancestor != left_ancestor {
                self.push(right_ancestor);
            }
        }
    }

    /// Traverses from the range boundaries up to the root, pulling new aggregate values.
    ///
    /// This method ensures that the parent nodes are updated with the latest values
    /// from their children, allowing for consistent state after updates.
    ///
    /// # Arguments
    /// * `start` - The starting index of the range.
    /// * `end` - The ending index of the range (exclusive).
    #[inline]
    fn pull_boundary_paths(&mut self, start: usize, end: usize) {
        for level in 1..=self.segment_tree_height {
            let left_ancestor = start >> level;
            let right_ancestor = (end - 1) >> level;
            if left_ancestor > 0 {
                self.pull(left_ancestor);
            }
            if right_ancestor > 0 && right_ancestor != left_ancestor {
                self.pull(right_ancestor);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{merge, IntervalGapTree, LazyState, Node};

    #[test]
    fn test_private_merge_logic_directly() {
        let left = Node::<u32> {
            segment_length: 4,
            length_of_longest_free_prefix: 1,
            length_of_longest_free_suffix: 3,
            length_of_maximum_free_gap: 2,
            lazy_propagation_state: LazyState::None,
        };
        let right = Node::<u32> {
            segment_length: 5,
            length_of_longest_free_prefix: 4,
            length_of_longest_free_suffix: 2,
            length_of_maximum_free_gap: 5,
            lazy_propagation_state: LazyState::None,
        };
        let merged_node = merge(&left, &right);
        assert_eq!(merged_node.length_of_maximum_free_gap, 7);
        assert_eq!(merged_node.length_of_longest_free_prefix, 1);
        assert_eq!(merged_node.length_of_longest_free_suffix, 2);
        assert_eq!(merged_node.segment_length, 9);
    }

    #[test]
    fn test_lazy_state_display() {
        assert_eq!(format!("{}", LazyState::None), "None");
        assert_eq!(format!("{}", LazyState::Free), "Free");
        assert_eq!(format!("{}", LazyState::Occupied), "Occupied");
    }

    #[test]
    fn test_node_default() {
        let node: Node<u32> = Node::default();
        assert_eq!(node.length_of_longest_free_prefix, 0);
        assert_eq!(node.length_of_longest_free_suffix, 0);
        assert_eq!(node.length_of_maximum_free_gap, 0);
        assert_eq!(node.segment_length, 0);
        assert_eq!(node.lazy_propagation_state, LazyState::None);
    }

    #[test]
    fn test_node_display() {
        let node: Node<u32> = Node::new(5, 10, 15, 20, LazyState::Occupied);
        assert_eq!(
            format!("{}", node),
            "Node(length_of_longest_free_prefix: 5, \
            length_of_longest_free_suffix: 10, \
            length_of_maximum_free_gap: 15, \
            segment_length: 20, \
            lazy_propagation_state: Occupied)"
        );
    }

    #[test]
    fn bit_width_matches_expectations() {
        assert_eq!(super::bit_width(1), 1);
        assert_eq!(super::bit_width(2), 2);
        assert_eq!(super::bit_width(3), 2);
        assert_eq!(super::bit_width(4), 3);
        assert_eq!(super::bit_width(7), 3);
        assert_eq!(super::bit_width(8), 4);
        assert_eq!(super::bit_width(9), 4);
        assert_eq!(super::bit_width(16), 5);
    }

    #[test]
    fn tree_empty_default() {
        let t: IntervalGapTree<u32> = IntervalGapTree::new(0, true);
        assert_eq!(t.segment_count(), 0);
        assert_eq!(t.leaf_count(), 0);
        assert_eq!(t.node_count(), 0);
        assert_eq!(t.height(), 0);
    }

    #[test]
    fn construction_with_padding_initially_free() {
        let t: IntervalGapTree<u32> = IntervalGapTree::new(5, true);
        assert_eq!(t.segment_count(), 5);
        assert_eq!(t.leaf_count(), 8);
        assert_eq!(t.node_count(), 16);
        assert_eq!(t.height(), super::bit_width(8));

        let root = t.nodes[1];
        assert_eq!(root.segment_length, 8);
        assert_eq!(root.length_of_maximum_free_gap, 5);
        assert_eq!(root.length_of_longest_free_prefix, 5);
        assert_eq!(root.length_of_longest_free_suffix, 0);
        assert!(matches!(root.lazy_propagation_state, LazyState::None));
    }

    #[test]
    fn construction_initially_occupied() {
        let t: IntervalGapTree<u32> = IntervalGapTree::new(5, false);
        let root = t.nodes[1];
        assert_eq!(root.segment_length, 8);
        assert_eq!(root.length_of_maximum_free_gap, 0);
        assert_eq!(root.length_of_longest_free_prefix, 0);
        assert_eq!(root.length_of_longest_free_suffix, 0);
    }

    #[test]
    fn exact_power_of_two_all_free() {
        let t: IntervalGapTree<u32> = IntervalGapTree::new(8, true);
        let root = t.nodes[1];
        assert_eq!(root.segment_length, 8);
        assert_eq!(root.length_of_maximum_free_gap, 8);
        assert_eq!(root.length_of_longest_free_prefix, 8);
        assert_eq!(root.length_of_longest_free_suffix, 8);
    }

    #[test]
    fn single_leaf_cases() {
        let t: IntervalGapTree<u32> = IntervalGapTree::new(1, true);
        assert_eq!(t.leaf_count(), 1);
        assert_eq!(t.node_count(), 2);
        assert_eq!(t.height(), super::bit_width(1));
        let root = t.nodes[1];
        assert_eq!(root.segment_length, 1);
        assert_eq!(root.length_of_maximum_free_gap, 1);

        let t2: IntervalGapTree<u32> = IntervalGapTree::new(1, false);
        let root2 = t2.nodes[1];
        assert_eq!(root2.segment_length, 1);
        assert_eq!(root2.length_of_maximum_free_gap, 0);
    }

    #[test]
    fn index_zero_is_unused_default() {
        let t: IntervalGapTree<u32> = IntervalGapTree::new(5, true);
        let n0 = t.nodes[0];
        assert_eq!(n0.segment_length, 0);
        assert_eq!(n0.length_of_maximum_free_gap, 0);
        assert_eq!(n0.length_of_longest_free_prefix, 0);
        assert_eq!(n0.length_of_longest_free_suffix, 0);
        assert!(matches!(n0.lazy_propagation_state, LazyState::None));
    }

    #[test]
    fn merge_accumulates_when_child_fully_free() {
        let left = Node::<u32> {
            segment_length: 4,
            length_of_longest_free_prefix: 4,
            length_of_longest_free_suffix: 4,
            length_of_maximum_free_gap: 4,
            lazy_propagation_state: LazyState::None,
        };
        let right = Node::<u32> {
            segment_length: 5,
            length_of_longest_free_prefix: 5,
            length_of_longest_free_suffix: 5,
            length_of_maximum_free_gap: 5,
            lazy_propagation_state: LazyState::None,
        };
        let m = merge(&left, &right);
        assert_eq!(m.segment_length, 9);
        assert_eq!(m.length_of_longest_free_prefix, 9);
        assert_eq!(m.length_of_longest_free_suffix, 9);
        assert_eq!(m.length_of_maximum_free_gap, 9);
    }

    fn mk_tree_4_occupied() -> IntervalGapTree<u32> {
        IntervalGapTree::new(4, false)
    }

    #[test]
    fn apply_sets_leaf_free_then_occupied() {
        let mut tree = mk_tree_4_occupied();
        let leaf = tree.leaf_count() + 1;

        tree.apply(leaf, LazyState::Free);
        let node_one = tree.nodes[leaf];
        assert_eq!(node_one.segment_length, 1);
        assert_eq!(node_one.length_of_longest_free_prefix, 1);
        assert_eq!(node_one.length_of_longest_free_suffix, 1);
        assert_eq!(node_one.length_of_maximum_free_gap, 1);
        assert!(matches!(node_one.lazy_propagation_state, LazyState::Free));

        tree.apply(leaf, LazyState::Occupied);
        let node_two = tree.nodes[leaf];
        assert_eq!(node_two.segment_length, 1);
        assert_eq!(node_two.length_of_longest_free_prefix, 0);
        assert_eq!(node_two.length_of_longest_free_suffix, 0);
        assert_eq!(node_two.length_of_maximum_free_gap, 0);
        assert!(matches!(
            node_two.lazy_propagation_state,
            LazyState::Occupied
        ));
    }

    #[test]
    fn push_propagates_to_children_and_clears_parent_flag() {
        let mut tree = mk_tree_4_occupied();

        tree.apply(1, LazyState::Free);
        assert_eq!(tree.nodes[2].length_of_maximum_free_gap, 0);
        assert_eq!(tree.nodes[3].length_of_maximum_free_gap, 0);

        tree.push(1);
        assert!(matches!(tree.nodes[1].lazy_propagation_state, LazyState::None));
        assert_eq!(tree.nodes[2].segment_length, 2);
        assert_eq!(tree.nodes[2].length_of_maximum_free_gap, 2);
        assert!(matches!(tree.nodes[2].lazy_propagation_state, LazyState::Free));
        assert_eq!(tree.nodes[3].segment_length, 2);
        assert_eq!(tree.nodes[3].length_of_maximum_free_gap, 2);
        assert!(matches!(tree.nodes[3].lazy_propagation_state, LazyState::Free));

        let leaf_start = tree.leaf_count();
        assert_eq!(tree.nodes[leaf_start].length_of_maximum_free_gap, 0);
        assert_eq!(tree.nodes[leaf_start + 1].length_of_maximum_free_gap, 0);
        assert_eq!(tree.nodes[leaf_start + 2].length_of_maximum_free_gap, 0);
        assert_eq!(tree.nodes[leaf_start + 3].length_of_maximum_free_gap, 0);
    }

    #[test]
    fn push_cascades_down_to_leaves() {
        let mut tree = mk_tree_4_occupied();

        tree.apply(1, LazyState::Free);
        tree.push(1);
        tree.push(2);
        tree.push(3);

        let leaf_start = tree.leaf_count();
        for i in leaf_start..(leaf_start + 4) {
            let leaf = tree.nodes[i];
            assert_eq!(leaf.segment_length, 1);
            assert_eq!(leaf.length_of_maximum_free_gap, 1);
            assert!(matches!(leaf.lazy_propagation_state, LazyState::Free));
        }
    }

    #[test]
    fn pull_recomputes_parent_from_children_when_no_lazy_flag() {
        let mut tree = mk_tree_4_occupied();
        let left_leaf = tree.leaf_count();
        let right_leaf = tree.leaf_count() + 1;
        tree.apply(left_leaf, LazyState::Free);
        tree.apply(right_leaf, LazyState::Occupied);

        assert!(matches!(tree.nodes[2].lazy_propagation_state, LazyState::None));
        tree.pull(2);

        let n2 = tree.nodes[2];
        assert_eq!(n2.segment_length, 2);
        assert_eq!(n2.length_of_longest_free_prefix, 1);
        assert_eq!(n2.length_of_longest_free_suffix, 0);
        assert_eq!(n2.length_of_maximum_free_gap, 1);
    }

    #[test]
    fn pull_is_noop_when_parent_has_lazy_flag() {
        let mut tree = mk_tree_4_occupied();
        tree.apply(2, LazyState::Free);
        let left_leaf = tree.leaf_count();
        let right_leaf = tree.leaf_count() + 1;
        tree.apply(left_leaf, LazyState::Occupied);
        tree.apply(right_leaf, LazyState::Occupied);
        tree.pull(2);

        let n2 = tree.nodes[2];
        assert!(matches!(n2.lazy_propagation_state, LazyState::Free));
        assert_eq!(n2.segment_length, 2);
        assert_eq!(n2.length_of_longest_free_prefix, 2);
        assert_eq!(n2.length_of_longest_free_suffix, 2);
        assert_eq!(n2.length_of_maximum_free_gap, 2);
    }

    fn apply_naive(v: &mut [bool], start: usize, end: usize, free: bool) {
        for i in start..end {
            v[i] = free;
        }
    }

    fn metrics_naive(v: &[bool], start: usize, end: usize) -> (u32, u32, u32, u32) {
        if start >= end {
            return (0, 0, 0, 0);
        }
        let mut prefix = 0u32;
        let mut i = start;
        while i < end && v[i] {
            prefix += 1;
            i += 1;
        }

        let mut suffix = 0u32;
        let mut j = end;
        while j > start && v[j - 1] {
            suffix += 1;
            j -= 1;
        }

        let mut best = 0u32;
        let mut cur = 0u32;
        for k in start..end {
            if v[k] {
                cur += 1;
            } else {
                best = best.max(cur);
                cur = 0;
            }
        }
        best = best.max(cur);

        let seg_len = (end - start) as u32;
        (prefix, suffix, best, seg_len)
    }

    #[test]
    fn range_query_empty_interval_returns_zero_node() {
        let mut t: IntervalGapTree<u32> = IntervalGapTree::new(8, false);
        let q = t.range_query(5..5);
        assert_eq!(q.segment_length, 0);
        assert_eq!(q.length_of_longest_free_prefix, 0);
        assert_eq!(q.length_of_longest_free_suffix, 0);
        assert_eq!(q.length_of_maximum_free_gap, 0);
    }

    #[test]
    fn range_update_free_then_query_whole_tree() {
        let mut t: IntervalGapTree<u32> = IntervalGapTree::new(8, false);
        t.range_update(2..6, LazyState::Free);
        let q = t.range_query(0..8);
        assert_eq!(q.segment_length, 8);
        assert_eq!(q.length_of_longest_free_prefix, 0);
        assert_eq!(q.length_of_longest_free_suffix, 0);
        assert_eq!(q.length_of_maximum_free_gap, 4);
    }

    #[test]
    fn range_update_multiple_overlaps_matches_naive_model() {
        let node = 16usize;
        let mut tree: IntervalGapTree<u32> = IntervalGapTree::new(node, false);
        let mut naive = vec![false; node];

        tree.range_update(2..10, LazyState::Free);
        apply_naive(&mut naive, 2, 10, true);

        tree.range_update(5..=12, LazyState::Occupied);
        apply_naive(&mut naive, 5, 13, false);

        tree.range_update(..4, LazyState::Free);
        apply_naive(&mut naive, 0, 4, true);

        tree.range_update(3..4, LazyState::Occupied);
        apply_naive(&mut naive, 3, 4, false);

        tree.range_update(12.., LazyState::Free);
        apply_naive(&mut naive, 12, 16, true);

        let ranges = [
            (0, 16),
            (0, 8),
            (8, 16),
            (2, 6),
            (4, 5),
            (12, 16),
            (3, 13),
        ];

        for (s, e) in ranges {
            let q = tree.range_query(s..e);
            let (p, sfx, mg, len) = metrics_naive(&naive, s, e);
            assert_eq!(q.segment_length, len, "seg_len mismatch for [{s},{e})");
            assert_eq!(
                q.length_of_longest_free_prefix, p,
                "prefix mismatch for [{s},{e})"
            );
            assert_eq!(
                q.length_of_longest_free_suffix, sfx,
                "suffix mismatch for [{s},{e})"
            );
            assert_eq!(
                q.length_of_maximum_free_gap, mg,
                "max_gap mismatch for [{s},{e})"
            );
        }

        let q_all = tree.range_query(0..node);
        let (_, _, mg_all, _) = metrics_naive(&naive, 0, node);
        assert_eq!(q_all.length_of_maximum_free_gap, mg_all);
    }

    #[test]
    fn range_update_noops_on_empty_or_out_of_order() {
        let mut t: IntervalGapTree<u32> = IntervalGapTree::new(8, false);
        let before = t.nodes[1];
        t.range_update(3..3, LazyState::Free);
        t.range_update(6..5, LazyState::Free);
        let after = t.nodes[1];

        assert_eq!(
            before.length_of_maximum_free_gap,
            after.length_of_maximum_free_gap
        );
        assert_eq!(
            before.length_of_longest_free_prefix,
            after.length_of_longest_free_prefix
        );
        assert_eq!(
            before.length_of_longest_free_suffix,
            after.length_of_longest_free_suffix
        );
        assert_eq!(before.segment_length, after.segment_length);
    }

    #[test]
    fn range_query_pushes_pending_lazy_on_paths() {
        let mut t: IntervalGapTree<u32> = IntervalGapTree::new(8, false);
        t.range_update(.., LazyState::Free);
        t.range_update(3..5, LazyState::Occupied);

        let q_all = t.range_query(..);
        assert_eq!(q_all.length_of_maximum_free_gap, 3);
        assert_eq!(q_all.length_of_longest_free_prefix, 3);
        assert_eq!(q_all.length_of_longest_free_suffix, 3);

        let q_mid = t.range_query(2..6);
        assert_eq!(q_mid.segment_length, 4);
        assert_eq!(q_mid.length_of_maximum_free_gap, 1);
        assert_eq!(q_mid.length_of_longest_free_prefix, 1);
        assert_eq!(q_mid.length_of_longest_free_suffix, 1);
    }

    #[test]
    fn occupy_and_free_basic_partitions() {
        let mut t: IntervalGapTree<u32> = IntervalGapTree::new(8, true);
        assert!(t.check_free(..));
        assert!(!t.check_occupied(..));

        t.occupy(2..6);

        assert!(t.check_free(0..2));
        assert!(t.check_occupied(2..6));
        assert!(t.check_free(6..8));

        assert!(!t.check_free(..));
        assert!(!t.check_occupied(..));

        t.free(2..6);
        assert!(t.check_free(..));
        assert!(!t.check_occupied(..));
    }

    #[test]
    fn wrappers_equivalence_with_mixed_updates() {
        let mut t: IntervalGapTree<u32> = IntervalGapTree::new(12, false);
        assert!(t.check_occupied(..));

        t.free(3..9);
        assert!(t.check_free(3..9));
        assert!(t.check_occupied(..3));
        assert!(t.check_occupied(9..));
        assert!(!t.check_free(..));
        assert!(!t.check_occupied(..));

        t.occupy(5..=7);
        assert!(t.check_free(3..5));
        assert!(t.check_occupied(5..8));
        assert!(t.check_free(8..9));
        assert!(!t.check_free(3..9));
        assert!(!t.check_occupied(3..9));
    }

    #[test]
    fn idempotence_and_empty_range_semantics() {
        let mut t: IntervalGapTree<u32> = IntervalGapTree::new(10, false);

        let before = t.nodes[1];
        t.free(4..4);
        t.occupy(6..6);
        let after = t.nodes[1];
        assert_eq!(before.segment_length, after.segment_length);
        assert_eq!(
            before.length_of_maximum_free_gap,
            after.length_of_maximum_free_gap
        );

        assert!(t.check_free(2..2));
        assert!(!t.check_occupied(2..2));

        t.occupy(1..5);
        assert!(t.check_occupied(1..5));
        t.occupy(1..5);
        assert!(t.check_occupied(1..5));

        t.free(2..4);
        assert!(t.check_free(2..4));
        t.free(2..4);
        assert!(t.check_free(2..4));
    }

    #[test]
    fn boundaries_and_non_power_of_two_n() {
        let mut t: IntervalGapTree<u32> = IntervalGapTree::new(5, true);
        assert!(t.check_free(..));
        assert!(!t.check_occupied(..));

        t.occupy(..1);
        t.occupy(4..);

        assert!(t.check_occupied(..1));
        assert!(t.check_free(1..4));
        assert!(t.check_occupied(4..));

        assert!(!t.check_free(..));
        assert!(!t.check_occupied(..));
    }

    #[test]
    fn whole_tree_toggle_free_then_occupied() {
        let mut t: IntervalGapTree<u32> = IntervalGapTree::new(6, false);
        assert!(t.check_occupied(..));

        t.free(..);
        assert!(t.check_free(..));
        assert!(!t.check_occupied(..));

        t.occupy(..);
        assert!(t.check_occupied(..));
        assert!(!t.check_free(..));
    }
}
