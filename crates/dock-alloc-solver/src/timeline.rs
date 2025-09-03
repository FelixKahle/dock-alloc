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

use std::collections::BTreeMap;
use std::ops::Bound::{Excluded, Included, Unbounded};
use std::ops::RangeBounds;

/// A data structure representing a series of states that change at discrete points in time.
///
/// A `Timeline` can be thought of as a sequence of keyframes. For any given time `t`,
/// the value of the timeline is determined by the keyframe with the largest key
/// that is less than or equal to `t`. This is useful for modeling properties
/// that remain constant over intervals and change instantaneously.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Timeline<K, V> {
    map: BTreeMap<K, V>,
}

impl<K, V> Timeline<K, V>
where
    K: Ord + Copy,
{
    /// Creates a new `Timeline` with an initial value at a specified origin time.
    ///
    /// Every timeline must have at least one keyframe, which is established here.
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
    /// Note: A timeline created with `new()` will never be empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns the value that is active at a specific time `t`.
    ///
    /// This is determined by finding the keyframe with the largest key
    /// less than or equal to `t`. Returns `None` if `t` is before the
    /// first keyframe.
    #[inline]
    pub fn at(&self, t: K) -> Option<&V> {
        self.map.range(..=t).next_back().map(|(_, v)| v)
    }

    /// Finds the keyframe (key and value) active at time `t`.
    ///
    /// This is the key-value pair with the largest key less than or equal to `t`.
    /// Returns `None` if `t` is before the first keyframe.
    #[inline]
    pub fn floor(&self, t: K) -> Option<(K, &V)> {
        self.map.range(..=t).next_back().map(|(k, v)| (*k, v))
    }

    /// Ensures that an exact key exists at time `t`.
    ///
    /// - If a key already exists at `t`, it returns a mutable reference to its value.
    /// - If no key exists at `t`, it clones the value from the immediately preceding
    ///   keyframe, inserts it at `t`, and returns a mutable reference.
    ///
    /// Returns `None` if `t` is before the first keyframe in the timeline, as there would
    /// be no value to clone.
    #[inline]
    pub fn ensure_key(&mut self, t: K) -> Option<&mut V>
    where
        V: Clone,
    {
        if !self.map.contains_key(&t) {
            let v = self.map.range(..=t).next_back()?.1.clone();
            self.map.insert(t, v);
        }
        self.map.get_mut(&t)
    }

    /// Returns the key of the keyframe active at time `t`.
    ///
    /// This is the largest key that is less than or equal to `t`.
    #[inline]
    pub fn prev_key(&self, t: K) -> Option<K> {
        self.map.range(..=t).next_back().map(|(k, _)| *k)
    }

    /// Returns the first key that comes after time `t`.
    ///
    /// This is the smallest key that is strictly greater than `t`.
    #[inline]
    pub fn next_key(&self, t: K) -> Option<K> {
        self.map
            .range((Excluded(t), Unbounded))
            .next()
            .map(|(k, _)| *k)
    }

    /// Returns an iterator over the keys within a specified range.
    #[inline]
    pub fn keys(&self, range: impl RangeBounds<K>) -> impl Iterator<Item = K> + '_ {
        self.map.range(range).map(|(k, _)| *k)
    }

    /// Applies a function to all values associated with keyframes in a given range.
    #[inline]
    pub fn apply_in(&mut self, range: impl RangeBounds<K>, mut f: impl FnMut(&mut V)) {
        for (_, v) in self.map.range_mut(range) {
            f(v);
        }
    }

    /// Scans a region and removes redundant keyframes.
    ///
    /// A keyframe is considered redundant if its value is identical to the value of the
    /// preceding keyframe. This method checks all keyframes that "touch" the specified
    /// range (i.e., the key just before the range start, all keys within, and the key at the end)
    /// and removes any that are unnecessary.
    pub fn coalesce_in(&mut self, range: impl RangeBounds<K>)
    where
        V: PartialEq,
    {
        if self.map.is_empty() {
            return;
        }

        // strict predecessor of start
        let left = match range.start_bound() {
            Included(s) | Excluded(s) => self
                .map
                .range(..*s)
                .next_back()
                .map(|(k, _)| *k)
                .unwrap_or(*s),
            Unbounded => *self.map.keys().next().unwrap(),
        };

        // first key strictly after end
        let right = match range.end_bound() {
            Included(e) | Excluded(e) => self
                .map
                .range((Excluded(*e), Unbounded))
                .next()
                .map(|(k, _)| *k)
                .unwrap_or(*e),
            Unbounded => *self.map.keys().next_back().unwrap(),
        };

        // Collect to avoid borrow conflicts while mutating
        let keys: Vec<K> = self
            .map
            .range((Included(left), Included(right)))
            .map(|(k, _)| *k)
            .collect();

        for tp in keys {
            self.coalesce_at(tp);
        }
    }

    /// Checks a single point `tp` and removes it if its value is the same
    /// as its predecessor and successor.
    fn coalesce_at(&mut self, tp: K)
    where
        V: PartialEq,
    {
        let Some(cur) = self.map.get(&tp) else {
            return;
        };

        let pred_eq = self
            .map
            .range(..tp)
            .next_back()
            .is_some_and(|(_, p)| p == cur);
        let next_eq = match self.map.range((Excluded(tp), Unbounded)).next() {
            None => true,
            Some((_, n)) => n == cur,
        };

        if pred_eq && next_eq {
            self.map.remove(&tp);
        }
    }

    /// Returns a reference to the raw, underlying `BTreeMap`.
    #[inline]
    pub fn raw(&self) -> &BTreeMap<K, V> {
        &self.map
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Creates a sample timeline for testing purposes:
    /// 0 -> "a"
    /// 10 -> "b"
    /// 20 -> "c"
    fn sample_timeline() -> Timeline<i32, &'static str> {
        let mut timeline = Timeline::new(0, "a");
        timeline.map.insert(10, "b");
        timeline.map.insert(20, "c");
        timeline
    }

    #[test]
    fn test_new_and_len() {
        let timeline = Timeline::new(0, "hello");
        assert_eq!(timeline.len(), 1);
        assert!(!timeline.is_empty());
        assert_eq!(timeline.at(0), Some(&"hello"));
        assert_eq!(timeline.at(100), Some(&"hello"));
    }

    #[test]
    fn test_at_and_floor() {
        let timeline = sample_timeline();

        // Test `at`
        assert_eq!(timeline.at(-5), None); // Before first key
        assert_eq!(timeline.at(0), Some(&"a")); // Exact key
        assert_eq!(timeline.at(5), Some(&"a")); // Between keys
        assert_eq!(timeline.at(10), Some(&"b")); // Exact key
        assert_eq!(timeline.at(19), Some(&"b")); // Between keys
        assert_eq!(timeline.at(20), Some(&"c")); // Last key
        assert_eq!(timeline.at(100), Some(&"c")); // After last key

        // Test `floor`
        assert_eq!(timeline.floor(-5), None);
        assert_eq!(timeline.floor(0), Some((0, &"a")));
        assert_eq!(timeline.floor(5), Some((0, &"a")));
        assert_eq!(timeline.floor(10), Some((10, &"b")));
        assert_eq!(timeline.floor(100), Some((20, &"c")));
    }

    #[test]
    fn test_prev_and_next_key() {
        let timeline = sample_timeline();

        // Test prev_key
        assert_eq!(timeline.prev_key(-1), None);
        assert_eq!(timeline.prev_key(0), Some(0));
        assert_eq!(timeline.prev_key(9), Some(0));
        assert_eq!(timeline.prev_key(10), Some(10));
        assert_eq!(timeline.prev_key(50), Some(20));

        // Test next_key
        assert_eq!(timeline.next_key(-1), Some(0));
        assert_eq!(timeline.next_key(0), Some(10));
        assert_eq!(timeline.next_key(9), Some(10));
        assert_eq!(timeline.next_key(10), Some(20));
        assert_eq!(timeline.next_key(20), None);
        assert_eq!(timeline.next_key(50), None);
    }

    #[test]
    fn test_ensure_key() {
        let mut timeline = Timeline::new(0, 100);
        timeline.map.insert(10, 200);

        // Case 1: Key already exists. Should do nothing but return a mutable reference.
        assert_eq!(timeline.len(), 2);
        if let Some(val) = timeline.ensure_key(10) {
            *val = 250;
        }
        assert_eq!(timeline.len(), 2);
        assert_eq!(timeline.at(10), Some(&250));

        // Case 2: Key does not exist. Should clone the floor value.
        assert!(timeline.ensure_key(5).is_some());
        assert_eq!(timeline.len(), 3);
        assert_eq!(timeline.at(5), Some(&100)); // Cloned from key 0
        assert_eq!(timeline.at(9), Some(&100)); // Value at 5 persists
        assert_eq!(timeline.at(10), Some(&250)); // Unchanged
    }

    #[test]
    fn test_ensure_key_no_floor() {
        let mut timeline = Timeline::<i32, i32>::new(10, 100);

        // ensure_key before the first key should do nothing and return None
        assert_eq!(timeline.ensure_key(5), None);
        assert_eq!(timeline.len(), 1);
        assert_eq!(timeline.map.contains_key(&5), false);
    }

    #[test]
    fn test_keys_iterator() {
        let timeline = sample_timeline();

        let all_keys: Vec<_> = timeline.keys(..).collect();
        assert_eq!(all_keys, vec![0, 10, 20]);

        let from_10: Vec<_> = timeline.keys(10..).collect();
        assert_eq!(from_10, vec![10, 20]);

        let up_to_10_exclusive: Vec<_> = timeline.keys(..10).collect();
        assert_eq!(up_to_10_exclusive, vec![0]);

        let up_to_10_inclusive: Vec<_> = timeline.keys(..=10).collect();
        assert_eq!(up_to_10_inclusive, vec![0, 10]);

        let between_5_and_15: Vec<_> = timeline.keys(5..15).collect();
        assert_eq!(between_5_and_15, vec![10]);
    }

    #[test]
    fn test_apply_in() {
        let mut timeline = Timeline::new(0, 1);
        timeline.map.insert(10, 2);
        timeline.map.insert(20, 3);
        timeline.map.insert(30, 4);

        // Apply a function to a range of values
        timeline.apply_in(10..=20, |v| *v *= 10);

        assert_eq!(timeline.at(0), Some(&1));
        assert_eq!(timeline.at(10), Some(&20));
        assert_eq!(timeline.at(20), Some(&30));
        assert_eq!(timeline.at(30), Some(&4));
    }

    #[test]
    fn test_coalesce_simple_redundant_middle_point() {
        let mut timeline = Timeline::new(0, "a");
        timeline.map.insert(10, "a"); // Redundant point
        timeline.map.insert(20, "b");

        // This won't be removed because its `next` value ("b") is different.
        // The implementation only removes points surrounded by equal values.
        timeline.coalesce_in(0..);
        assert_eq!(timeline.len(), 3);

        // Now add another "a", so 10 is surrounded
        timeline.map.insert(15, "a");
        let mut timeline2 = timeline.clone();

        // `coalesce_at(10)` runs: pred=0("a"), next=15("a"). Both equal. Remove 10.
        // `coalesce_at(15)` runs: pred is now 0("a"), next is 20("b"). Not equal. Keep 15.
        timeline.coalesce_in(..20);
        assert_eq!(timeline.keys(..).collect::<Vec<_>>(), vec![0, 15, 20]);

        // `coalesce_at(15)` runs: pred=10("a"), next=20("b"). Not equal. Keep 15.
        // `coalesce_at(10)` runs: pred=0("a"), next=15("a"). Both equal. Remove 10.
        timeline2.coalesce_in(15..20); // Different range, same keys touched
        assert_eq!(timeline2.keys(..).collect::<Vec<_>>(), vec![0, 15, 20]);
    }

    #[test]
    fn test_coalesce_no_change() {
        let mut timeline = sample_timeline();
        let original_keys: Vec<_> = timeline.keys(..).collect();

        timeline.coalesce_in(..);
        assert_eq!(timeline.keys(..).collect::<Vec<_>>(), original_keys);
    }

    #[test]
    fn test_coalesce_contiguous_block() {
        let mut timeline = Timeline::new(0, "a");
        timeline.map.insert(10, "a");
        timeline.map.insert(20, "a");
        timeline.map.insert(30, "b");

        // Keys to check are 0, 10, 20, 30
        // 1. coalesce_at(0): keep (no pred)
        // 2. coalesce_at(10): remove (pred=0("a"), next=20("a")) -> map is {0:a, 20:a, 30:b}
        // 3. coalesce_at(20): keep (pred is now 0("a"), next is 30("b")) -> pred_eq is true, next_eq is false
        // 4. coalesce_at(30): keep (pred=20("a"), next=none) -> pred_eq is false
        timeline.coalesce_in(..);

        assert_eq!(timeline.keys(..).collect::<Vec<_>>(), vec![0, 20, 30]);
    }

    #[test]
    fn test_coalesce_full_block() {
        let mut timeline = Timeline::new(0, "a");
        timeline.map.insert(10, "a");
        timeline.map.insert(20, "a");

        // Keys to check: 0, 10, 20
        // 1. coalesce_at(0): keep
        // 2. coalesce_at(10): remove (pred=0("a"), next=20("a")) -> map is {0:a, 20:a}
        // 3. coalesce_at(20): remove (pred is now 0("a"), next=None) -> pred_eq & next_eq are true
        timeline.coalesce_in(..);

        assert_eq!(timeline.keys(..).collect::<Vec<_>>(), vec![0]);
    }

    #[test]
    fn test_raw_getter() {
        let timeline = sample_timeline();
        let raw_map = timeline.raw();

        assert_eq!(raw_map.len(), 3);
        assert_eq!(raw_map.get(&10), Some(&"b"));
    }
}
