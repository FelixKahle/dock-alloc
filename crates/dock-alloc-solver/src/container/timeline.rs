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

use std::collections::BTreeMap;
use std::ops::Bound::{self, Excluded, Included, Unbounded};
use std::ops::RangeBounds;

/// A data structure representing a series of states that change at discrete points in time.
///
/// A `Timeline` models a value that is **piecewise constant**—it holds a specific state
/// over an interval and changes instantaneously at points called "keyframes". For any given
/// time `t`, the value of the timeline is determined by the keyframe with the largest key
/// that is less than or equal to `t`.
///
/// This is conceptually similar to a [step function](https://en.wikipedia.org/wiki/Step_function).
/// It's useful for modeling properties like animations, configuration changes, or any
/// stateful value that evolves over time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Timeline<K, V> {
    map: BTreeMap<K, V>,
}

impl<K, V> Timeline<K, V>
where
    K: Ord + Copy,
{
    /// Creates a new `Timeline` with an initial value at a specified origin time.
    #[inline]
    pub fn new(origin: K, v0: V) -> Self {
        let mut map = BTreeMap::new();
        map.insert(origin, v0);
        Self { map }
    }

    /// Returns the number of keyframes in the timeline.
    #[inline]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the timeline has no keyframes.
    ///
    /// Note: A `Timeline` created with [`new()`](Timeline::new) will never be empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns the value that is active at a specific time `t`.
    ///
    /// Returns `None` if `t` is before the timeline's origin.
    /// See also [`floor()`](Timeline::floor) to get the key as well.
    #[inline]
    pub fn at(&self, t: K) -> Option<&V> {
        self.map.range(..=t).next_back().map(|(_, v)| v)
    }

    /// Finds the keyframe (key and value) active at time `t`.
    ///
    /// Returns `None` if `t` is before the timeline's origin.
    /// See also [`at()`](Timeline::at) if you only need the value.
    #[inline]
    pub fn floor(&self, t: K) -> Option<(K, &V)> {
        self.map.range(..=t).next_back().map(|(k, v)| (*k, v))
    }

    /// Ensures an exact key exists at time `t`, returning a mutable reference to its value.
    ///
    /// If no key exists at `t`, it clones the value from the preceding keyframe.
    /// Returns `None` if `t` is before the origin.
    #[inline]
    fn ensure_key(&mut self, t: K) -> Option<&mut V>
    where
        V: Clone,
    {
        if !self.map.contains_key(&t) {
            let v = self.map.range(..=t).next_back()?.1.clone();
            self.map.insert(t, v);
        }
        self.map.get_mut(&t)
    }

    #[inline]
    pub fn first_key(&self) -> K {
        *self.map.keys().next().expect("timeline has origin")
    }

    #[inline]
    pub fn last_key(&self) -> K {
        *self.map.keys().next_back().expect("timeline has origin")
    }

    /// Returns the key of the keyframe active at time `t` (largest key <= `t`).
    #[inline]
    pub fn prev_key(&self, t: K) -> Option<K> {
        self.map.range(..=t).next_back().map(|(k, _)| *k)
    }

    /// Returns the largest key that is strictly less than `t`.
    #[inline]
    pub fn prev_strict_key(&self, t: K) -> Option<K> {
        self.map.range(..t).next_back().map(|(k, _)| *k)
    }

    /// Returns the smallest key that is strictly greater than `t`.
    #[inline]
    pub fn next_key(&self, t: K) -> Option<K> {
        self.map
            .range((Excluded(t), Unbounded))
            .next()
            .map(|(k, _)| *k)
    }

    /// Alias for [`next_key()`](Timeline::next_key).
    #[inline]
    pub fn next_strict_key(&self, t: K) -> Option<K> {
        self.next_key(t)
    }

    /// Returns an iterator over the keys within a specified range.
    #[inline]
    pub fn keys(&self, range: impl RangeBounds<K>) -> impl DoubleEndedIterator<Item = K> + '_ {
        let (lb, rb) = normalize_bounds(range.start_bound(), range.end_bound());
        self.map.range((lb, rb)).map(|(k, _)| *k)
    }

    #[inline]
    pub fn entries<R>(&self, range: R) -> impl DoubleEndedIterator<Item = (K, &V)> + '_
    where
        R: RangeBounds<K>,
    {
        let (lb, rb) = normalize_bounds(range.start_bound(), range.end_bound());
        self.map.range((lb, rb)).map(|(k, v)| (*k, v))
    }

    /// Iterate (key, &mut value) over a range.
    #[inline]
    pub fn entries_mut<R>(&mut self, range: R) -> impl DoubleEndedIterator<Item = (K, &mut V)> + '_
    where
        R: RangeBounds<K>,
    {
        let (lb, rb) = normalize_bounds(range.start_bound(), range.end_bound());
        self.map.range_mut((lb, rb)).map(|(k, v)| (*k, v))
    }

    /// Inserts or replaces a keyframe and automatically coalesces redundant keyframes around it.
    ///
    /// This is the preferred method for adding keyframes, as it ensures the timeline
    /// remains in an optimized state. After insertion, it checks if the new key or its
    /// immediate neighbors have become redundant and removes them if so.
    #[inline]
    pub fn insert_key(&mut self, t: K, v: V)
    where
        V: PartialEq,
    {
        self.map.insert(t, v);
        let left = self.prev_strict_key(t).unwrap_or(t);
        let right = self.next_key(t).unwrap_or(t);
        self.coalesce_in(left..=right);
    }

    #[inline]
    fn coalesce_anchors(&self, lb: std::ops::Bound<K>, rb: std::ops::Bound<K>) -> (K, K) {
        let left_anchor = match lb {
            Included(s) | Excluded(s) => self.prev_strict_key(s).unwrap_or(s),
            Unbounded => *self.map.keys().next().expect("timeline has origin"),
        };
        let right_anchor = match rb {
            Included(e) | Excluded(e) => self.next_key(e).unwrap_or(e),
            Unbounded => *self.map.keys().next_back().expect("timeline has origin"),
        };
        (left_anchor, right_anchor)
    }

    /// Edits all keyframes within a range, ensuring clean boundaries and coalescing afterward.
    ///
    /// # Panics
    ///
    /// Panics if the timeline is empty (which should not happen if created via `new`).
    #[inline]
    pub fn edit_in<R>(&mut self, range: R, mut f: impl FnMut(&mut V))
    where
        R: RangeBounds<K>,
        V: Clone + PartialEq,
    {
        let (lb, rb) = self.ensure_cuts(range);

        for (_, v) in self.map.range_mut((lb, rb)) {
            f(v);
        }

        let (la, ra) = self.coalesce_anchors(lb, rb);
        self.coalesce_in(la..=ra);
    }

    /// Tries to edit all keyframes within a range, ensuring clean boundaries and coalescing afterward.
    ///
    /// If the closure returns an error for any keyframe, the editing stops and the error is returned.
    /// Keyframes that were successfully edited before the error occurred will retain their changes.
    pub fn try_edit_in<R, E, F>(&mut self, range: R, mut f: F) -> Result<(), E>
    where
        R: std::ops::RangeBounds<K>,
        F: FnMut(&mut V) -> Result<(), E>,
        V: Clone + PartialEq,
    {
        let (lb, rb) = self.ensure_cuts(range);
        let mut err: Option<E> = None;
        for (_, v) in self.map.range_mut((lb, rb)) {
            if err.is_some() {
                break;
            }
            if let Err(e) = f(v) {
                err = Some(e);
            }
        }

        let (la, ra) = self.coalesce_anchors(lb, rb);
        self.coalesce_in(la..=ra);

        match err {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    /// Private helper to ensure keyframes exist at the bounded endpoints of a range.
    /// This "cuts" the timeline to isolate a range before mutation.
    #[inline]
    fn ensure_cuts<R>(&mut self, range: R) -> (Bound<K>, Bound<K>)
    where
        R: RangeBounds<K>,
        V: Clone,
    {
        let (sb, eb) = (range.start_bound(), range.end_bound());

        if let Some(s) = boundary_key(sb) {
            let _ = self.ensure_key(s);
        }
        if let Some(e) = boundary_key(eb) {
            let _ = self.ensure_key(e);
        }

        normalize_bounds(sb, eb)
    }

    /// Removes redundant keyframes within a specified range.
    /// A keyframe is redundant if its value is identical to its immediate predecessor.
    fn coalesce_in<R>(&mut self, range: R)
    where
        R: RangeBounds<K>,
        V: PartialEq,
    {
        if self.map.len() < 2 {
            return;
        }
        let (lb, rb) = normalize_bounds(range.start_bound(), range.end_bound());
        let keys: Vec<K> = self.map.range((lb, rb)).map(|(k, _)| *k).collect();
        for k in keys {
            self.coalesce_at(k);
        }
    }

    /// Checks a single point for redundancy and removes it if necessary.
    fn coalesce_at(&mut self, tp: K)
    where
        V: PartialEq,
    {
        let Some(cur) = self.map.get(&tp) else { return };
        let redundant = self
            .map
            .range(..tp)
            .next_back()
            .is_some_and(|(_, prev)| prev == cur);

        if redundant {
            self.map.remove(&tp);
        }
    }
}

/// Helper to get the key from a `Bound` if it's `Included` or `Excluded`.
#[inline]
fn boundary_key<K: Copy>(bound: Bound<&K>) -> Option<K> {
    match bound {
        Included(k) | Excluded(k) => Some(*k),
        Unbounded => None,
    }
}

/// Normalizes range bounds to handle a `BTreeMap::range` edge case.
#[inline]
fn normalize_bounds<K>(start: Bound<&K>, end: Bound<&K>) -> (Bound<K>, Bound<K>)
where
    K: PartialEq + Copy,
{
    match (start, end) {
        (Excluded(a), Excluded(b)) if a == b => (Included(*a), Excluded(*b)),
        _ => (own(start), own(end)),
    }
}

/// Helper to convert a bound of references to a bound of owned values.
#[inline]
fn own<K: Copy>(b: Bound<&K>) -> Bound<K> {
    match b {
        Included(x) => Included(*x),
        Excluded(x) => Excluded(*x),
        Unbounded => Unbounded,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    /// Helper to assert the exact state of the timeline's keyframes using the public API.
    fn assert_timeline_state<K, V>(timeline: &Timeline<K, V>, expected_keyframes: &[(K, V)])
    where
        K: Ord + Copy + std::fmt::Debug,
        V: PartialEq + Clone + std::fmt::Debug,
    {
        let expected_map: BTreeMap<K, V> = expected_keyframes.iter().cloned().collect();

        // Reconstruct the map from the public API
        let actual_map: BTreeMap<K, V> = timeline
            .keys(..)
            .map(|k| (k, timeline.at(k).expect("key should have a value").clone()))
            .collect();

        assert_eq!(
            actual_map, expected_map,
            "Timeline's internal state does not match expected state."
        );
    }

    #[test]
    fn test_new() {
        let timeline = Timeline::new(0, "initial");
        assert_eq!(timeline.len(), 1);
        assert!(!timeline.is_empty());
        assert_eq!(timeline.at(0), Some(&"initial"));
    }

    #[test]
    fn test_insert_key() {
        // Case 1: Simple insert in the middle.
        let mut tl = Timeline::new(0, 'A');
        tl.insert_key(20, 'C');
        tl.insert_key(10, 'B');
        assert_timeline_state(&tl, &[(0, 'A'), (10, 'B'), (20, 'C')]);

        // Case 2: Insert a key that is immediately redundant.
        let mut tl = Timeline::new(0, 'A');
        tl.insert_key(20, 'C');
        tl.insert_key(10, 'A'); // Value 'A' is same as predecessor at 0
        assert_timeline_state(&tl, &[(0, 'A'), (20, 'C')]);

        // Case 3: Insert a key that makes the successor redundant.
        let mut tl = Timeline::new(0, 'A');
        tl.insert_key(20, 'C');
        tl.insert_key(10, 'C'); // This makes the key at 20 redundant
        assert_timeline_state(&tl, &[(0, 'A'), (10, 'C')]);

        // Case 4: Overwrite an existing key, causing it to become redundant.
        let mut tl = Timeline::new(0, 'A');
        tl.insert_key(10, 'B');
        tl.insert_key(10, 'A'); // Overwriting 10 with 'A' makes it redundant
        assert_timeline_state(&tl, &[(0, 'A')]);
    }

    #[test]
    fn test_private_ensure_cuts() {
        let mut timeline = Timeline::new(0, 'A');
        timeline.insert_key(20, 'C');

        // Case 1: Cuts are needed at both ends.
        let mut tl1 = timeline.clone();
        tl1.ensure_cuts(5..15);
        // Expects keys to be inserted at 5 and 15 with the preceding value 'A'.
        assert_timeline_state(&tl1, &[(0, 'A'), (5, 'A'), (15, 'A'), (20, 'C')]);

        // Case 2: Start bound is already a key.
        let mut tl2 = timeline.clone();
        tl2.ensure_cuts(0..15);
        // Expects only one key to be added at 15.
        assert_timeline_state(&tl2, &[(0, 'A'), (15, 'A'), (20, 'C')]);
    }

    #[test]
    fn test_edit_in() {
        // Case 1: Edit a middle segment, causing coalesce with predecessor.
        let mut tl = Timeline::new(0, 'A');
        tl.insert_key(10, 'B');
        tl.insert_key(20, 'C');
        tl.edit_in(10..20, |v| *v = 'A');
        assert_timeline_state(&tl, &[(0, 'A'), (20, 'C')]);

        // Case 2: Edit a middle segment, causing coalesce with successor.
        let mut tl = Timeline::new(0, 'A');
        tl.insert_key(10, 'B');
        tl.insert_key(20, 'C');
        tl.edit_in(10..20, |v| *v = 'C');
        assert_timeline_state(&tl, &[(0, 'A'), (10, 'C')]);

        // Case 3: Edit over multiple segments.
        let mut tl = Timeline::new(0, 'A');
        tl.insert_key(10, 'B');
        tl.insert_key(20, 'C');
        tl.insert_key(30, 'D');
        tl.edit_in(5..25, |v| *v = 'X');
        assert_timeline_state(&tl, &[(0, 'A'), (5, 'X'), (25, 'C'), (30, 'D')]);

        // Case 4: Edit with unbounded start.
        let mut tl = Timeline::new(0, 'A');
        tl.insert_key(10, 'B');
        tl.insert_key(20, 'C');
        tl.edit_in(..15, |v| *v = 'Z');
        assert_timeline_state(&tl, &[(0, 'Z'), (15, 'B'), (20, 'C')]);
    }
}
