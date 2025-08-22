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

//! # Core Primitives
//!
//! This module provides a collection of fundamental, reusable data structures
//! that serve as the basic building blocks for the rest of the crate.
//!
//! These primitives are designed to be generic and robust, offering common
//! functionality for mathematical and logical operations.

use num_traits::{FromPrimitive, Zero};
use std::cmp::Ordering;
use std::fmt;
use std::hash::Hash;
use std::iter::FusedIterator;
use std::ops::{Add, Div, Sub};

/// A half-open interval `[start, end)`.
///
/// This struct represents a half-open interval where the start is inclusive and the end is exclusive,
/// so that [start, end) includes all values `x` such that `start <= x < end`.
/// It provides methods to create intervals, check containment, intersection, and more.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::primitives::Interval;
/// let interval = Interval::new(1, 5);
/// assert!(interval.start() == 1);
/// assert!(interval.end() == 5);
/// assert!(interval.contains(3));
/// assert!(!interval.contains(5));
/// assert!(interval.is_empty() == false);
/// assert!(interval.length() == 4);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Interval<T> {
    start_inclusive: T,
    end_exclusive: T,
}

impl<T> Interval<T> {
    /// Creates a new half-open interval `[start, end)`.
    ///
    /// This function takes two values `a` and `b`, determines their order, and constructs an interval
    /// with `start_inclusive` as the smaller value and `end_exclusive` as the larger value.
    /// So any attempt to create an interval where `b < a` will automatically swap the bounds.
    ///
    /// # Panics
    ///
    /// If `a` and `b` are not comparable (e.g., if they are NaN), this function will panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(3, 5);
    /// assert_eq!(interval.start(), 3);
    /// assert_eq!(interval.end(), 5);
    ///
    /// let interval = Interval::new(5, 3);
    /// assert_eq!(interval.start(), 3);
    /// assert_eq!(interval.end(), 5);
    /// ```
    #[inline]
    pub fn new(a: T, b: T) -> Self
    where
        T: PartialOrd + Copy,
    {
        // This creates the invariant that `start_inclusive` is always less than or equal to `end_exclusive`.
        // If `a` is greater than `b`, it swaps them.
        // This is done to ensure that the interval is always well-defined, and we rely on this
        // invariant throughout the struct's methods.
        let ord = a
            .partial_cmp(&b)
            .expect("Interval::new: non-comparable bounds (NaN?)");
        let (s, e) = match ord {
            Ordering::Greater => (b, a),
            _ => (a, b),
        };

        Self {
            start_inclusive: s,
            end_exclusive: e,
        }
    }

    /// Returns the start of the interval, which is inclusive.
    ///
    /// This method returns the `start_inclusive` value of the interval.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(1, 5);
    /// assert_eq!(interval.start(), 1);
    /// ```
    #[inline]
    pub fn start(&self) -> T
    where
        T: Copy,
    {
        self.start_inclusive
    }

    /// Returns the end of the interval, which is exclusive.
    ///
    /// This method returns the `end_exclusive` value of the interval.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(1, 5);
    /// assert_eq!(interval.end(), 5);
    /// ```
    #[inline]
    pub fn end(&self) -> T
    where
        T: Copy,
    {
        self.end_exclusive
    }

    /// Checks if the interval is empty.
    ///
    /// Determines if the interval has no length, which occurs when the start and end are equal.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(5, 5);
    /// assert!(interval.is_empty());
    ///
    /// let interval = Interval::new(1, 5);
    /// assert!(!interval.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool
    where
        T: PartialEq,
    {
        self.start_inclusive == self.end_exclusive
    }

    /// Checks if the interval contains a value.
    ///
    /// This method checks if a given value `x` is within the interval,
    /// meaning it is greater than or equal to `start_inclusive` and less than `end_exclusive`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(1, 5);
    /// assert!(interval.contains(1)); // start is inclusive
    /// assert!(interval.contains(3)); // within the interval
    /// assert!(!interval.contains(5)); // end is exclusive
    /// assert!(!interval.contains(6)); // beyond the interval
    /// assert!(!interval.contains(0)); // below the interval
    /// ```
    #[inline]
    pub fn contains(&self, x: T) -> bool
    where
        T: PartialOrd,
    {
        x >= self.start_inclusive && x < self.end_exclusive
    }

    /// Checks if the interval contains another interval.
    ///
    /// This method checks if the current interval fully contains another interval `other`.
    /// The `other` interval is considered contained if its start is greater than or equal to
    /// the current interval's start and its end is less than or equal to the current interval's end.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let a = Interval::new(1, 5);
    /// let b = Interval::new(2, 4);
    /// assert!(a.contains_interval(&b)); // a contains b
    /// let c = Interval::new(0, 6);
    /// assert!(!a.contains_interval(&c)); // a does not contain c
    /// let d = Interval::new(1, 5);
    /// assert!(a.contains_interval(&d)); // a contains itself
    /// ```
    #[inline]
    pub fn contains_interval(&self, other: &Self) -> bool
    where
        T: PartialOrd,
    {
        other.start_inclusive >= self.start_inclusive && other.end_exclusive <= self.end_exclusive
    }

    /// Checks if this interval intersects with another interval.
    ///
    /// This method checks if there is any overlap between the
    /// current interval and another interval `other`.
    /// The intervals are considered to intersect if the maximum of their
    /// start points is less than the minimum of their end points.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let a = Interval::new(1, 5);
    /// let b = Interval::new(4, 6);
    /// assert!(a.intersects(&b)); // a and b intersect
    /// let c = Interval::new(5, 7);
    /// assert!(!a.intersects(&c)); // a and c do not intersect
    /// let d = Interval::new(0, 1);
    /// assert!(!a.intersects(&d)); // a and d do not intersect
    /// let e = Interval::new(1, 5);
    /// assert!(a.intersects(&e)); // a intersects with itself
    /// ```
    #[inline]
    pub fn intersects(&self, other: &Self) -> bool
    where
        T: PartialOrd + Copy,
    {
        let start = if self.start_inclusive > other.start_inclusive {
            self.start_inclusive
        } else {
            other.start_inclusive
        };
        let end = if self.end_exclusive < other.end_exclusive {
            self.end_exclusive
        } else {
            other.end_exclusive
        };
        start < end
    }

    /// Translates the interval by a given distance.
    ///
    /// This method creates a new interval by adding a distance `d`
    /// to both the start and end points of the current interval.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(1, 5);
    /// let translated = interval.translate(2);
    /// assert_eq!(translated.start(), 3); // start is now 1 + 2
    /// assert_eq!(translated.end(), 7);   // end is now 5 +
    /// ```
    #[inline]
    pub fn translate(&self, d: T) -> Self
    where
        T: Copy + PartialOrd + Add<Output = T>,
    {
        Self::new(self.start() + d, self.end() + d)
    }

    /// Inflates the interval by a given distance.
    ///
    /// This method creates a new interval by subtracting `d` from the start point
    /// and adding `d` to the end point of the current interval.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(1, 5);
    /// let inflated = interval.inflate(2);
    /// assert_eq!(inflated.start(), -1); // start is now 1 - 2
    /// assert_eq!(inflated.end(), 7);   // end is now 5 + 2
    /// ```
    #[inline]
    pub fn inflate(&self, d: T) -> Self
    where
        T: Copy + PartialOrd + Sub<Output = T> + Add<Output = T>,
    {
        Self::new(self.start() - d, self.end() + d)
    }

    /// Measures the length of the interval.
    ///
    /// This method calculates the length of the interval as the difference between
    /// `end_exclusive` and `start_inclusive`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(2, 5);
    /// assert_eq!(interval.measure(), 3); // length is 5 - 2
    /// let empty_interval = Interval::new(5, 5);
    /// assert_eq!(empty_interval.measure(), 0); // length is 0 for empty
    /// ```
    pub fn measure<D>(&self) -> D
    where
        T: Copy + Sub<Output = D>,
    {
        self.end() - self.start()
    }

    /// Returns the intersection of this interval with another interval.
    ///
    /// This method returns an `Option<Interval<T>>` that represents the
    /// intersection of the two intervals. If the intervals do not intersect, it returns `None`.
    /// The intersection is defined as the maximum of the start points and the minimum of the end points.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let a = Interval::new(1, 5);
    /// let b = Interval::new(3, 7);
    ///
    /// assert_eq!(a.intersection(&b), Some(Interval::new(3, 5))); // intersection exists
    /// let c = Interval::new(5, 8);
    /// assert_eq!(a.intersection(&c), None); // no intersection
    /// let d = Interval::new(1, 5);
    /// assert_eq!(a.intersection(&d), Some(Interval::new(1, 5))); // intersection with itself
    /// ```
    #[inline]
    pub fn intersection(&self, other: &Self) -> Option<Self>
    where
        T: PartialOrd + Copy,
    {
        self.clamp(other)
    }

    /// Clamps this interval to the bounds of another interval.
    ///
    /// This method returns an `Option<Interval<T>>` that represents the intersection of the two intervals.
    /// If the intervals do not overlap, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let a = Interval::new(1, 5);
    /// let b = Interval::new(3, 7);
    /// assert_eq!(a.clamp(&b), Some(Interval::new(3, 5))); // clamped to intersection
    /// let c = Interval::new(6, 8);
    /// assert_eq!(a.clamp(&c), None); // no overlap, returns None
    /// let d = Interval::new(1, 5);
    /// assert_eq!(a.clamp(&d), Some(Interval::new(1, 5))); // clamped to itself
    /// ```
    #[inline]
    pub fn clamp(&self, boundary: &Self) -> Option<Self>
    where
        T: PartialOrd + Copy,
    {
        let start = if self.start_inclusive > boundary.start_inclusive {
            self.start_inclusive
        } else {
            boundary.start_inclusive
        };
        let end = if self.end_exclusive < boundary.end_exclusive {
            self.end_exclusive
        } else {
            boundary.end_exclusive
        };
        (start < end).then_some(Self {
            start_inclusive: start,
            end_exclusive: end,
        })
    }

    /// Returns the length of the interval.
    ///
    /// This method calculates the length of the interval as the difference between
    /// `end_exclusive` and `start_inclusive`. It requires that the type `
    /// T` implements the `Sub` trait.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(2, 5);
    /// assert_eq!(interval.length(), 3); // length is 5 - 2
    /// let empty_interval = Interval::new(5, 5);
    /// assert_eq!(empty_interval.length(), 0); // length is 0 for empty
    /// ```
    #[inline]
    pub fn length(&self) -> T
    where
        T: Sub<Output = T> + Copy,
    {
        self.end_exclusive - self.start_inclusive
    }

    /// Returns the midpoint of the interval.
    ///
    /// This method calculates the midpoint of the interval as the average of
    /// `start_inclusive` and `end_exclusive`. It requires that the type `T`
    /// implements the `FromPrimitive`, `Copy`, `Sub`, `Div`, and `Add` traits.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(2, 6);
    /// assert_eq!(interval.midpoint(), 4); // midpoint is (2 + 6) / 2
    /// let empty_interval = Interval::new(5, 5);
    /// assert_eq!(empty_interval.midpoint(), 5); // midpoint is 5 for empty interval
    /// ```
    #[inline]
    pub fn midpoint(&self) -> T
    where
        T: FromPrimitive + Copy + Sub<Output = T> + Div<T, Output = T> + Add<T, Output = T>,
    {
        self.start_inclusive + (self.end_exclusive - self.start_inclusive) / T::from_u8(2).unwrap()
    }

    /// Converts the interval to a range.
    ///
    /// This method converts the half-open interval into a `std::ops::Range<T>`,
    /// which is a Rust standard library type representing a range of values.
    /// The range is defined as `start..end`, where `start` is inclusive and
    /// `end` is exclusive.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(2, 5);
    /// assert_eq!(interval.to_range(), 2..5); // converts to range
    /// let empty_interval = Interval::new(5, 5);
    /// assert_eq!(empty_interval.to_range(), 5..5); // empty range
    /// ```
    #[inline]
    pub fn to_range(&self) -> std::ops::Range<T>
    where
        T: Copy,
    {
        self.start()..self.end()
    }

    /// Returns an iterator over the interval with a specified step.
    ///
    /// This method creates an iterator that yields values from the interval,
    /// starting from `start_inclusive` and incrementing by `step`
    /// until it reaches or exceeds `end_exclusive`.
    ///
    /// # Panics
    ///
    /// This method will panic immediately if `step` is zero or negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(1, 5);
    /// let mut iter = interval.iter(1);
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), Some(4));
    /// assert_eq!(iter.next(), None); // end_exclusive reached
    /// ```
    #[inline]
    pub fn iter<'a>(&'a self, step: T) -> IntervalIter<'a, T>
    where
        T: Copy + PartialOrd + Add<T, Output = T> + Zero,
    {
        IntervalIter::new(self, step)
    }
}

impl<T: fmt::Display> fmt::Display for Interval<T> {
    /// Formats the interval as a string in the form `[start, end)`.
    ///
    /// This method implements the `Display` trait for the `Interval` struct,
    /// allowing it to be printed in a human-readable format.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(1, 5);
    /// assert_eq!(format!("{}", interval), "[1, 5)");
    /// let empty_interval = Interval::new(5, 5);
    /// assert_eq!(format!("{}", empty_interval), "[5, 5)");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {})", self.start_inclusive, self.end_exclusive)
    }
}

impl<T: Copy + PartialOrd> From<std::ops::Range<T>> for Interval<T> {
    /// Converts a `std::ops::Range<T>` into an `Interval<T>`.
    ///
    /// This method allows you to create an `Interval` from a standard Rust range,
    /// which is defined as `start..end`. The start of the range is inclusive,
    /// and the end is exclusive, matching the semantics of the `Interval` struct.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let range = 1..5;
    /// let interval: Interval<_> = Interval::from(range);
    /// assert_eq!(interval.start(), 1);
    /// assert_eq!(interval.end(), 5);
    /// let empty_range: std::ops::Range<_> = 5..5;
    ///
    /// // You can also use `into` directly:
    /// let empty_interval: Interval<_> = (1..5).into();
    /// assert_eq!(empty_interval.start(), 1);
    /// assert_eq!(empty_interval.end(), 5);
    /// ```
    #[inline]
    fn from(r: std::ops::Range<T>) -> Self {
        Interval::new(r.start, r.end)
    }
}

/// An iterator over the values in a half-open interval.
///
/// This iterator yields values starting from `start_inclusive` and increments by a specified `step`
/// until it reaches or exceeds `end_exclusive`.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::primitives::Interval;
///
/// let interval = Interval::new(1, 5);
/// let mut iter = interval.iter(1);
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), Some(3));
/// assert_eq!(iter.next(), Some(4));
/// assert_eq!(iter.next(), None); // end_exclusive reached
/// ```
pub struct IntervalIter<'a, T> {
    interval: &'a Interval<T>,
    current: T,
    step: T,
}

impl<'a, T: Copy + PartialOrd + Zero> IntervalIter<'a, T> {
    /// Creates a new iterator for the given interval with a specified step.
    ///
    /// This method initializes the iterator with the starting point as `start_inclusive`
    /// and sets the step size for each iteration.
    ///
    /// # Panics
    ///
    /// This method will panic immediately if `step` is zero or negative.
    fn new(interval: &'a Interval<T>, step: T) -> Self {
        assert!(step > T::zero(), "Interval::iter: step must be > 0");

        IntervalIter {
            interval,
            current: interval.start_inclusive,
            step,
        }
    }
}

impl<'a, T> Iterator for IntervalIter<'a, T>
where
    T: Copy + PartialOrd + Add<T, Output = T>,
{
    type Item = T;

    /// Returns the next value in the interval.
    ///
    /// This method returns the next value in the interval, incrementing by `step` each time.
    /// If the current value exceeds `end_exclusive`, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::primitives::Interval;
    ///
    /// let interval = Interval::new(1, 5);
    /// let mut iter = interval.iter(1);
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), Some(4));
    /// assert_eq!(iter.next(), None); // end_exclusive reached
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.interval.end_exclusive {
            let value = self.current;
            self.current = self.current + self.step;
            Some(value)
        } else {
            None
        }
    }
}

impl<'a, T> FusedIterator for IntervalIter<'a, T> where T: Copy + PartialOrd + Add<T, Output = T> {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn new_normalizes_order_integers() {
        let i = Interval::new(5i32, 3i32);
        assert_eq!(i.start(), 3);
        assert_eq!(i.end(), 5);
    }

    #[test]
    fn new_keeps_order_when_sorted() {
        let i = Interval::new(-4i64, 9i64);
        assert_eq!(i.start(), -4);
        assert_eq!(i.end(), 9);
    }

    #[test]
    #[should_panic]
    fn new_panics_on_nan_left() {
        let _ = Interval::new(f64::NAN, 1.0f64);
    }

    #[test]
    #[should_panic]
    fn new_panics_on_nan_right() {
        let _ = Interval::new(1.0f64, f64::NAN);
    }

    #[test]
    fn is_empty_true_when_bounds_equal() {
        let i = Interval::new(5u32, 5u32);
        assert!(i.is_empty());
    }

    #[test]
    fn is_empty_false_when_bounds_different() {
        let i = Interval::new(1u32, 2u32);
        assert!(!i.is_empty());
    }

    #[test]
    fn contains_inclusive_start_and_exclusive_end() {
        let i = Interval::new(10i32, 20i32);
        assert!(i.contains(10));
        assert!(i.contains(19));
        assert!(!i.contains(20));
        assert!(!i.contains(9));
    }

    #[test]
    fn contains_on_empty_interval_is_always_false() {
        let i = Interval::new(3i32, 3i32);
        assert!(!i.contains(3));
        assert!(!i.contains(2));
        assert!(!i.contains(4));
    }

    #[test]
    fn contains_interval_true_for_nested_and_equal() {
        let a = Interval::new(1i32, 5i32);
        let b = Interval::new(2i32, 4i32);
        let c = Interval::new(1i32, 5i32);
        assert!(a.contains_interval(&b));
        assert!(a.contains_interval(&c));
    }

    #[test]
    fn contains_interval_false_when_other_extends_outside() {
        let a = Interval::new(1i32, 5i32);
        let bigger = Interval::new(0i32, 6i32);
        assert!(!a.contains_interval(&bigger));
    }

    #[test]
    fn contains_interval_true_for_empty_other_if_anchor_inside() {
        let a = Interval::new(1i32, 5i32);
        let empty_inside = Interval::new(3i32, 3i32);
        assert!(a.contains_interval(&empty_inside));
    }

    #[test]
    fn intersects_true_on_overlap() {
        let a = Interval::new(0i32, 10i32);
        let b = Interval::new(5i32, 15i32);
        assert!(a.intersects(&b));
        assert!(b.intersects(&a));
    }

    #[test]
    fn intersects_false_when_touching_at_endpoint() {
        let a = Interval::new(0i32, 10i32);
        let b = Interval::new(10i32, 20i32);
        assert!(!a.intersects(&b));
        assert!(!b.intersects(&a));
    }

    #[test]
    fn intersects_false_when_disjoint() {
        let a = Interval::new(0i32, 5i32);
        let b = Interval::new(6i32, 10i32);
        assert!(!a.intersects(&b));
    }

    #[test]
    fn intersects_false_when_one_is_empty() {
        let a = Interval::new(1i32, 5i32);
        let empty = Interval::new(3i32, 3i32);
        assert!(!a.intersects(&empty));
        assert!(!empty.intersects(&a));
        assert!(!empty.intersects(&empty));
    }

    #[test]
    fn intersects_true_with_itself_if_non_empty() {
        let a = Interval::new(1i32, 5i32);
        assert!(a.intersects(&a));
    }

    #[test]
    fn intersection_returns_overlap_interval() {
        let a = Interval::new(0i32, 10i32);
        let b = Interval::new(5i32, 15i32);
        assert_eq!(a.intersection(&b), Some(Interval::new(5, 10)));
    }

    #[test]
    fn intersection_is_none_when_touching_at_endpoint() {
        let a = Interval::new(0i32, 10i32);
        let b = Interval::new(10i32, 20i32);
        assert_eq!(a.intersection(&b), None);
    }

    #[test]
    fn intersection_with_empty_is_none() {
        let a = Interval::new(1i32, 5i32);
        let empty = Interval::new(3i32, 3i32);
        assert_eq!(a.intersection(&empty), None);
        assert_eq!(empty.intersection(&a), None);
    }

    #[test]
    fn intersection_with_itself_yields_self() {
        let a = Interval::new(2i32, 7i32);
        assert_eq!(a.intersection(&a), Some(a));
    }

    #[test]
    fn clamp_to_inner_boundary_returns_inner() {
        let a = Interval::new(0i32, 10i32);
        let boundary = Interval::new(2i32, 8i32);
        assert_eq!(a.clamp(&boundary), Some(boundary));
    }

    #[test]
    fn clamp_disjoint_returns_none() {
        let a = Interval::new(0i32, 3i32);
        let boundary = Interval::new(5i32, 7i32);
        assert_eq!(a.clamp(&boundary), None);
    }

    #[test]
    fn clamp_to_equal_returns_self() {
        let a = Interval::new(2i32, 6i32);
        assert_eq!(a.clamp(&a), Some(a));
    }

    #[test]
    fn length_on_signed_integers() {
        let i = Interval::new(-3i32, 2i32);
        assert_eq!(i.length(), 5);
    }

    #[test]
    fn length_on_unsigned_integers() {
        let i = Interval::new(3u32, 9u32);
        assert_eq!(i.length(), 6);
    }

    #[test]
    fn midpoint_on_even_integer_span() {
        let i = Interval::new(2i32, 6i32);
        assert_eq!(i.midpoint(), 4);
    }

    #[test]
    fn midpoint_on_odd_integer_span_floor_behavior() {
        let i = Interval::new(0i32, 3i32);
        assert_eq!(i.midpoint(), 1);
    }

    #[test]
    fn midpoint_integer_avoids_overflow_where_a_plus_b_would() {
        let a = i64::MAX - 2;
        let b = i64::MAX;
        let i = Interval::new(a, b);
        assert_eq!(i.midpoint(), i64::MAX - 1);
    }

    #[test]
    fn midpoint_on_floats_basic() {
        let i = Interval::new(1.0f64, 3.0f64);
        assert_eq!(i.midpoint(), 2.0);
        let j = Interval::new(-10.0f32, 6.0f32);
        assert_eq!(j.midpoint(), -2.0);
    }

    #[test]
    fn to_range_roundtrip() {
        let i = Interval::new(-2i32, 5i32);
        let r = i.to_range();
        assert_eq!(r, -2..5);
    }

    #[test]
    fn from_range_normalizes_order() {
        let i: Interval<i32> = (5..2).into();
        assert_eq!(i.start(), 2);
        assert_eq!(i.end(), 5);
    }

    #[test]
    fn display_formats_as_half_open() {
        let i = Interval::new(1i32, 5i32);
        assert_eq!(format!("{}", i), "[1, 5)");
    }

    #[test]
    fn display_formats_empty() {
        let i = Interval::new(5i32, 5i32);
        assert_eq!(format!("{}", i), "[5, 5)");
    }

    #[test]
    fn hash_and_eq_allow_dedup_in_set() {
        let mut set = HashSet::new();
        set.insert(Interval::new(5i32, 3i32));
        set.insert(Interval::new(3i32, 5i32));
        assert_eq!(set.len(), 1);
        assert!(set.contains(&Interval::new(3, 5)));
    }

    #[test]
    fn contains_interval_with_empty_self_is_true_only_if_other_is_also_empty_and_equal() {
        let empty = Interval::new(4i32, 4i32);
        let empty_same = Interval::new(4i32, 4i32);
        let non_empty = Interval::new(3i32, 5i32);
        assert!(empty.contains_interval(&empty_same));
        assert!(!empty.contains_interval(&non_empty));
    }

    #[test]
    fn floats_infinite_bounds_midpoint_is_nan() {
        let i = Interval::new(f64::NEG_INFINITY, f64::INFINITY);
        assert!(i.midpoint().is_nan());
    }

    #[test]
    fn contains_interval_with_empty_other_at_edges() {
        let a = Interval::new(1i32, 5i32);
        assert!(a.contains_interval(&Interval::new(1, 1)));
        assert!(a.contains_interval(&Interval::new(5, 5)));
    }

    #[test]
    fn from_range_via_into_needs_parens() {
        let i: Interval<_> = (1..5).into();
        assert_eq!((i.start(), i.end()), (1, 5));
    }

    #[test]
    #[should_panic(expected = "step must be > 0")]
    fn iter_panics_on_zero_step_int() {
        let i = Interval::new(1i32, 5i32);
        let _ = i.iter(0).next();
    }

    #[test]
    #[should_panic(expected = "step must be > 0")]
    fn iter_panics_on_negative_step_int() {
        let i = Interval::new(1i32, 5i32);
        let _ = i.iter(-1).next();
    }

    #[test]
    fn iter_basic_progression() {
        let i = Interval::new(1i32, 5i32);
        let v: Vec<_> = i.iter(1).collect();
        assert_eq!(v, vec![1, 2, 3, 4]); // half-open
    }

    #[test]
    fn iter_step_larger_than_span_emits_once_if_non_empty() {
        let i = Interval::new(1i32, 5i32);
        let v: Vec<_> = i.iter(10).collect();
        assert_eq!(v, vec![1]);
    }

    #[test]
    fn iter_over_empty_is_empty() {
        let i = Interval::new(3i32, 3i32);
        assert_eq!(i.iter(1).next(), None);
    }
}
