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
//
// //! Core data types for the Berth Allocation Problem (BAP).

#[allow(dead_code)]
use crate::primitives::Interval;
use num_traits::{PrimInt, Signed};
use std::{
    fmt::Display,
    ops::{Add, AddAssign, Neg, Sub, SubAssign},
};

/// Represents a point in time.
///
/// A `TimePoint` is a wrapper around a primitive integer type that
/// represents a specific point in time.
/// It is designed to be used in time intervals and comparisons,
/// providing a clear and type-safe way to handle time-related data.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::TimePoint;
///
/// let tp = TimePoint::new(42);
/// assert_eq!(tp.value(), 42);
/// assert_eq!(format!("{}", tp), "TimePoint(42)");
/// ```
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TimePoint<T: PrimInt>(T);

impl<T: PrimInt> TimePoint<T> {
    /// Creates a new `TimePoint` with the given value.
    ///
    /// Creates a new `TimePoint` instance wrapping the provided value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimePoint;
    ///
    /// let tp = TimePoint::new(42);
    /// assert_eq!(tp.value(), 42);
    /// ```
    pub fn new(value: T) -> Self {
        TimePoint(value)
    }

    /// Returns the value of the `TimePoint`.
    ///
    /// Returns the inner value of the `TimePoint` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimePoint;
    ///
    /// let tp = TimePoint::new(42);
    /// assert_eq!(tp.value(), 42);
    /// ```
    pub fn value(&self) -> T {
        self.0
    }
}

impl<T: PrimInt + Display> Display for TimePoint<T> {
    /// Formats the `TimePoint` as `TimePoint(value)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimePoint;
    ///
    /// let tp = TimePoint::new(42);
    /// assert_eq!(format!("{}", tp), "TimePoint(42)");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TimePoint({})", self.value())
    }
}

impl<T: PrimInt> From<T> for TimePoint<T> {
    /// Converts a primitive integer type into a `TimePoint`.
    ///
    /// This implementation allows for easy conversion from a primitive integer type
    /// to a `TimePoint`, enabling the use of `TimePoint`
    /// in contexts where a primitive integer is available.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimePoint;
    ///
    /// let value: i32 = 42;
    /// let tp: TimePoint<i32> = TimePoint::from(value);
    /// assert_eq!(tp.value(), 42);
    ///
    /// // You can also use the `into()` method for conversion:
    /// let tp: TimePoint<i32> = value.into();
    /// assert_eq!(tp.value(), 42);
    /// ```
    #[inline]
    fn from(v: T) -> Self {
        TimePoint(v)
    }
}

/// Represents a time interval with start and end points.
///
/// Represents a time interval defined by a start and end `TimePoint`.
/// The start time is inclusive, while the end time is exclusive.
/// This defines the interval as `[start, end)`.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::{TimePoint, TimeInterval};
///
/// let interval: TimeInterval<i32> = TimeInterval::new(TimePoint::new(10), TimePoint::new(20));
/// assert_eq!(interval.start().value(), 10);
/// assert_eq!(interval.end().value(), 20);
/// ```
pub type TimeInterval<T> = Interval<TimePoint<T>>;

/// Represents a time delta, which is the difference between two `TimePoint`s.
///
/// A `TimeDelta` is a wrapper around a primitive integer type that represents
/// the difference between two `TimePoint`s. It can be positive, negative, or zero
/// and is used to represent durations or intervals of time.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::{TimePoint, TimeDelta};
///
/// let start = TimePoint::new(10);
/// let end = TimePoint::new(20);
/// let delta: TimeDelta<i32> = end - start;
/// assert_eq!(delta.value(), 10);
/// ```
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TimeDelta<T: PrimInt + Signed>(T);

impl<T: PrimInt + Signed> TimeDelta<T> {
    /// Creates a new `TimeDelta` with the given value.
    ///
    /// Creates a new `TimeDelta` instance wrapping the provided value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(42);
    /// assert_eq!(delta.value(), 42);
    /// ```
    #[inline(always)]
    pub const fn new(value: T) -> Self {
        Self(value)
    }

    /// Creates a new `TimeDelta` with the value zero.
    ///
    /// Creates a new `TimeDelta` instance with a value of zero.
    /// This is useful for representing a zero duration or no change in time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta: TimeDelta<i32> = TimeDelta::zero();
    /// assert!(delta.is_zero());
    /// ```
    #[inline(always)]
    pub fn zero() -> Self {
        Self(T::zero())
    }

    /// Returns the value of the `TimeDelta`.
    ///
    /// Returns the inner value of the `TimeDelta` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(42);
    /// assert_eq!(delta.value(), 42);
    /// ```
    #[inline(always)]
    pub const fn value(self) -> T {
        self.0
    }

    /// Returns the absolute value of the `TimeDelta`.
    ///
    /// Returns a new `TimeDelta` instance with the absolute value of the inner value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(-42);
    /// assert_eq!(delta.abs().value(), 42);
    /// ```
    #[inline(always)]
    pub fn abs(self) -> Self {
        Self(self.0.abs())
    }

    /// Checks if the `TimeDelta` is negative.
    ///
    /// Returns `true` if the inner value is negative, otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let positive_delta = TimeDelta::new(42);
    /// let negative_delta = TimeDelta::new(-42);
    /// assert!(!positive_delta.is_negative());
    /// assert!(negative_delta.is_negative());
    /// ```
    #[inline(always)]
    pub fn is_negative(self) -> bool {
        self.0.is_negative()
    }

    /// Checks if the `TimeDelta` is positive.
    ///
    /// Returns `true` if the inner value is positive, otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let positive_delta = TimeDelta::new(42);
    /// let negative_delta = TimeDelta::new(-42);
    ///
    /// assert!(positive_delta.is_positive());
    /// assert!(!negative_delta.is_positive());
    /// ```
    #[inline(always)]
    pub fn is_positive(self) -> bool {
        self.0.is_positive()
    }

    /// Checks if the `TimeDelta` is zero.
    ///
    /// Returns `true` if the inner value is zero, otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let zero_delta: TimeDelta<i32> = TimeDelta::zero();
    /// assert!(zero_delta.is_zero());
    /// let non_zero_delta: TimeDelta<i32> = TimeDelta::new(42);
    /// assert!(!non_zero_delta.is_zero());
    /// ```
    #[inline(always)]
    pub fn is_zero(self) -> bool {
        self.0.is_zero()
    }
}

impl<T: PrimInt + Signed> TimePoint<T> {
    /// Adds a `TimeDelta` to the `TimePoint`, returning a new `TimePoint`.
    ///
    /// This method takes a `TimeDelta` and adds it to the current `TimePoint`,
    /// returning a new `TimePoint` with the updated value. However,
    /// if the addition would overflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let tp = TimePoint::new(10);
    /// let delta = TimeDelta::new(5);
    /// let new_tp = tp.checked_add(delta);
    /// assert_eq!(new_tp.unwrap().value(), 15);
    /// ```
    #[inline]
    pub fn checked_add(self, rhs: TimeDelta<T>) -> Option<Self> {
        self.0.checked_add(&rhs.0).map(TimePoint)
    }

    /// Subtracts a `TimeDelta` from the `TimePoint`, returning a new `TimePoint`.
    ///
    /// This method takes a `TimeDelta` and subtracts it from the current `TimePoint`,
    /// returning a new `TimePoint` with the updated value. However,
    /// if the subtraction would overflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let tp = TimePoint::new(20);
    /// let delta = TimeDelta::new(5);
    /// let new_tp = tp.checked_sub(delta);
    /// assert_eq!(new_tp.unwrap().value(), 15);
    /// ```
    #[inline]
    pub fn checked_sub(self, rhs: TimeDelta<T>) -> Option<Self> {
        self.0.checked_sub(&rhs.0).map(TimePoint)
    }

    /// Adds a `TimeDelta` to the `TimePoint`, returning a new `TimePoint`.
    ///
    /// This method takes a `TimeDelta` and adds it to the current `TimePoint`,
    /// returning a new `TimePoint` with the updated value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let tp = TimePoint::new(10);
    /// let delta = TimeDelta::new(5);
    /// let new_tp = tp.saturating_add(delta);
    /// assert_eq!(new_tp.value(), 15);
    /// ```
    #[inline]
    pub fn saturating_add(self, rhs: TimeDelta<T>) -> Self {
        TimePoint(self.0.saturating_add(rhs.0))
    }

    /// Subtracts a `TimeDelta` from the `TimePoint`, returning a new `TimePoint`.
    ///
    /// This method takes a `TimeDelta` and subtracts it from the current `TimePoint`,
    /// returning a new `TimePoint` with the updated value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let tp = TimePoint::new(20);
    /// let delta = TimeDelta::new(5);
    /// let new_tp = tp.saturating_sub(delta);
    /// assert_eq!(new_tp.value(), 15);
    /// ```
    #[inline]
    pub fn saturating_sub(self, rhs: TimeDelta<T>) -> Self {
        TimePoint(self.0.saturating_sub(rhs.0))
    }
}

impl<T: PrimInt + Display + Signed> Display for TimeDelta<T> {
    /// Formats the `TimeDelta` as `TimeDelta(value)`.
    ///
    /// Formats the `TimeDelta` instance as a string in the format `TimeDelta(value)`,
    /// where `value` is the inner value of the `TimeDelta`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(42);
    /// assert_eq!(format!("{}", delta), "TimeDelta(42)");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TimeDelta({})", self.0)
    }
}

impl<T: PrimInt + Signed> Add<TimeDelta<T>> for TimePoint<T> {
    type Output = TimePoint<T>;

    /// Adds a `TimeDelta` to a `TimePoint`, returning a new `TimePoint`.
    ///
    /// This method takes a `TimeDelta` and adds it to the current `TimePoint`,
    /// returning a new `TimePoint` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if a overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let tp = TimePoint::new(10);
    /// let delta = TimeDelta::new(5);
    /// let new_tp = tp + delta;
    /// assert_eq!(new_tp.value(), 15);
    /// ```
    #[inline]
    fn add(self, rhs: TimeDelta<T>) -> Self::Output {
        TimePoint(
            self.0
                .checked_add(&rhs.0)
                .expect("overflow in TimePoint + TimeDelta"),
        )
    }
}

impl<T: PrimInt + Signed> Add<TimePoint<T>> for TimeDelta<T> {
    type Output = TimePoint<T>;

    /// Adds a `TimePoint` to a `TimeDelta`, returning a new `TimePoint`.
    ///
    /// This method takes a `TimePoint` and adds it to the current `TimeDelta`,
    /// returning a new `TimePoint` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if a overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let delta = TimeDelta::new(5);
    /// let tp = TimePoint::new(10);
    ///
    /// let new_tp = delta + tp;
    /// assert_eq!(new_tp.value(), 15);
    /// ```
    #[inline]
    fn add(self, rhs: TimePoint<T>) -> Self::Output {
        TimePoint(
            rhs.0
                .checked_add(&self.0)
                .expect("overflow in TimeDelta + TimePoint"),
        )
    }
}

impl<T: PrimInt + Signed> AddAssign<TimeDelta<T>> for TimePoint<T> {
    /// Adds a `TimeDelta` to the current `TimePoint`, modifying it in place.
    ///
    /// This method takes a `TimeDelta` and adds it to the current `TimePoint`,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if a overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let mut tp = TimePoint::new(10);
    /// let delta = TimeDelta::new(5);
    /// tp += delta;
    /// assert_eq!(tp.value(), 15);
    /// ```
    fn add_assign(&mut self, rhs: TimeDelta<T>) {
        self.0 = self
            .0
            .checked_add(&rhs.0)
            .expect("overflow in TimePoint += TimeDelta");
    }
}

impl<T: PrimInt + Signed> Sub<TimeDelta<T>> for TimePoint<T> {
    type Output = TimePoint<T>;

    /// Subtracts a `TimeDelta` from a `TimePoint`, returning a new `TimePoint`.
    ///
    /// This method takes a `TimeDelta` and subtracts it from the current `TimePoint`,
    /// returning a new `TimePoint` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if a overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let tp = TimePoint::new(20);
    /// let delta = TimeDelta::new(5);
    /// let new_tp = tp - delta;
    /// assert_eq!(new_tp.value(), 15);
    /// ```
    fn sub(self, rhs: TimeDelta<T>) -> Self::Output {
        TimePoint(
            self.0
                .checked_sub(&rhs.0)
                .expect("overflow in TimePoint - TimeDelta"),
        )
    }
}
impl<T: PrimInt + Signed> SubAssign<TimeDelta<T>> for TimePoint<T> {
    /// Subtracts a `TimeDelta` from the current `TimePoint`, modifying it in place.
    ///
    /// This method takes a `TimeDelta` and subtracts it from the current `TimePoint`,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if a overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let mut tp = TimePoint::new(20);
    /// let delta = TimeDelta::new(5);
    /// tp -= delta;
    /// assert_eq!(tp.value(), 15);
    /// ```
    fn sub_assign(&mut self, rhs: TimeDelta<T>) {
        self.0 = self
            .0
            .checked_sub(&rhs.0)
            .expect("overflow in TimePoint -= TimeDelta");
    }
}

impl<T: PrimInt + Signed> Sub<TimePoint<T>> for TimePoint<T> {
    type Output = TimeDelta<T>;

    /// Subtracts one `TimePoint` from another, returning a `TimeDelta`.
    ///
    /// This method takes another `TimePoint` and subtracts it from the current instance,
    /// returning a new `TimeDelta` that represents the difference between the two points in time.
    ///
    /// # Panics
    ///
    /// This method will panic if a overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let tp1 = TimePoint::new(20);
    /// let tp2 = TimePoint::new(10);
    ///
    /// let delta = tp1 - tp2;
    /// assert_eq!(delta.value(), 10);
    /// ```
    fn sub(self, rhs: TimePoint<T>) -> Self::Output {
        TimeDelta::new(
            self.0
                .checked_sub(&rhs.0)
                .expect("overflow in TimePoint - TimePoint"),
        )
    }
}

impl<T: PrimInt + Signed> Add for TimeDelta<T> {
    type Output = TimeDelta<T>;

    /// Adds two `TimeDelta`s, returning a new `TimeDelta`.
    ///
    /// This method takes another `TimeDelta` and adds it to the current instance,
    /// returning a new `TimeDelta` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if a overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta1 = TimeDelta::new(10);
    /// let delta2 = TimeDelta::new(5);
    /// let result = delta1 + delta2;
    /// assert_eq!(result.value(), 15);
    /// ```
    fn add(self, rhs: Self) -> Self::Output {
        TimeDelta::new(
            self.0
                .checked_add(&rhs.0)
                .expect("overflow in TimeDelta + TimeDelta"),
        )
    }
}

impl<T: PrimInt + Signed> Sub for TimeDelta<T> {
    type Output = TimeDelta<T>;

    /// Subtracts one `TimeDelta` from another, returning a new `TimeDelta`.
    ///
    /// This method takes another `TimeDelta` and subtracts it from the current instance,
    /// returning a new `TimeDelta` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if a overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta1 = TimeDelta::new(10);
    /// let delta2 = TimeDelta::new(5);
    /// let result = delta1 - delta2;
    /// assert_eq!(result.value(), 5);
    /// ```
    fn sub(self, rhs: Self) -> Self::Output {
        TimeDelta(
            self.0
                .checked_sub(&rhs.0)
                .expect("overflow in TimeDelta - TimeDelta"),
        )
    }
}

impl<T: PrimInt + Signed> AddAssign for TimeDelta<T> {
    /// Adds another `TimeDelta` to the current instance, modifying it in place.
    ///
    /// This method takes another `TimeDelta` and adds it to the current instance,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if a overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    /// let mut delta1 = TimeDelta::new(10);
    /// let delta2 = TimeDelta::new(5);
    /// delta1 += delta2;
    /// assert_eq!(delta1.value(), 15);
    /// ```
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_add(&rhs.0)
            .expect("overflow in TimeDelta += TimeDelta");
    }
}

impl<T: PrimInt + Signed> SubAssign for TimeDelta<T> {
    /// Subtracts another `TimeDelta` from the current instance, modifying it in place.
    ///
    /// This method takes another `TimeDelta` and subtracts it from the current instance,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if a overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let mut delta1 = TimeDelta::new(10);
    /// let delta2 = TimeDelta::new(5);
    /// delta1 -= delta2;
    /// assert_eq!(delta1.value(), 5);
    /// ```
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_sub(&rhs.0)
            .expect("overflow in TimeDelta -= TimeDelta");
    }
}

impl<T: PrimInt + Signed> Neg for TimeDelta<T> {
    type Output = TimeDelta<T>;

    /// Negates the `TimeDelta`, returning a new `TimeDelta` with the negated value.
    ///
    /// This method takes the current `TimeDelta` and returns a new instance
    /// with the value negated.
    ///
    /// # Panics
    ///
    /// This method will panic if a overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(42);
    /// let negated_delta = -delta;
    /// assert_eq!(negated_delta.value(), -42);
    /// ```
    fn neg(self) -> Self::Output {
        TimeDelta::new(
            T::zero()
                .checked_sub(&self.0)
                .expect("overflow in -TimeDelta"),
        )
    }
}

impl<T: PrimInt + Signed> num_traits::Zero for TimeDelta<T> {
    /// Returns a `TimeDelta` with a value of zero.
    ///
    /// This implementation provides a `TimeDelta` with a value of zero,
    /// which is useful when you need to initialize a `TimeDelta`
    /// without a specific value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta: TimeDelta<i32> = TimeDelta::zero();
    /// assert!(delta.is_zero());
    /// ```
    #[inline]
    fn zero() -> Self {
        TimeDelta(T::zero())
    }

    /// Checks if the `TimeDelta` is zero.
    ///
    /// This implementation checks if the inner value of the `TimeDelta` is zero,
    /// which is useful for determining if a `TimeDelta` represents no change in time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta: TimeDelta<i32> = TimeDelta::zero();
    /// assert!(delta.is_zero());
    /// let non_zero_delta: TimeDelta<i32> = TimeDelta::new(42);
    /// assert!(!non_zero_delta.is_zero());
    /// ```
    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<T: PrimInt + Signed> From<T> for TimeDelta<T> {
    /// Converts a primitive integer type into a `TimeDelta`.
    ///
    /// This implementation allows for easy conversion from a primitive integer type
    /// to a `TimeDelta`, enabling the use of `TimeDelta`
    /// in contexts where a primitive integer is available.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let value: i32 = 42;
    /// let delta: TimeDelta<i32> = TimeDelta::from(value);
    /// assert_eq!(delta.value(), 42);
    ///
    /// // You can also use the `into()` method for conversion:
    /// let delta: TimeDelta<i32> = value.into();
    /// assert_eq!(delta.value(), 42);
    /// ```
    #[inline]
    fn from(v: T) -> Self {
        TimeDelta(v)
    }
}

impl<T: PrimInt + Signed> Default for TimeDelta<T> {
    /// Returns a `TimeDelta` with a value of zero.
    ///
    /// This implementation provides a default value for `TimeDelta`,
    /// which is useful when you need to initialize a `TimeDelta`
    /// without a specific value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta: TimeDelta<i32> = TimeDelta::default();
    /// assert!(delta.is_zero());
    /// ```
    #[inline]
    fn default() -> Self {
        TimeDelta::zero()
    }
}

/// Represents a segment index along the quay.
///
/// A `SegmentIndex` is a wrapper around a primitive unsigned integer type
/// that represents a specific segment along the quay.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::SegmentIndex;
///
/// let seg_idx = SegmentIndex::new(5);
/// assert_eq!(seg_idx.value(), 5);
/// assert_eq!(format!("{}", seg_idx), "SegmentIndex(5)");
/// ```
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct SegmentIndex(usize);

/// Represents a segment index along the quay with a length.
///
/// A `SegmentInterval` is a half-open interval defined by a start and end `SegmentIndex`.
/// It represents a contiguous section of the quay, where the start index is inclusive
/// and the end index is exclusive.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::{SegmentIndex, SegmentInterval, SegmentLength};
///
/// let start = SegmentIndex::new(5);
/// let length = SegmentLength::new(10);
///
/// let span: SegmentInterval = start.span_of(length);
/// assert_eq!(span.start().value(), 5);
/// assert_eq!(span.end().value(), 15);
/// ```
pub type SegmentInterval = Interval<SegmentIndex>;

impl Display for SegmentIndex {
    /// Formats the `SegmentIndex` as `SegmentIndex(value)`.
    ///
    /// Formats the `SegmentIndex` instance as a string in the format `SegmentIndex(value)`,
    /// where `value` is the inner value of the `SegmentIndex`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentIndex;
    ///
    /// let seg_idx = SegmentIndex::new(5);
    /// assert_eq!(format!("{}", seg_idx), "SegmentIndex(5)");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SegmentIndex({})", self.0)
    }
}

impl From<usize> for SegmentIndex {
    /// Converts a primitive unsigned integer type into a `SegmentIndex`.
    ///
    /// This implementation allows for easy conversion from a primitive unsigned integer type
    /// to a `SegmentIndex`, enabling the use of `SegmentIndex`
    /// in contexts where a primitive unsigned integer is available.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentIndex;
    ///
    /// let value: usize = 5;
    /// let seg_idx: SegmentIndex = SegmentIndex::from(value);
    /// assert_eq!(seg_idx.value(), 5);
    /// ```
    #[inline]
    fn from(v: usize) -> Self {
        SegmentIndex(v)
    }
}

impl SegmentIndex {
    /// Creates a new `SegmentIndex` with the given value.
    ///
    /// Creates a new `SegmentIndex` instance wrapping the provided value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentIndex;
    ///
    /// let seg_idx = SegmentIndex::new(5);
    /// assert_eq!(seg_idx.value(), 5);
    /// ```
    #[inline]
    pub const fn new(v: usize) -> Self {
        SegmentIndex(v)
    }

    /// Creates a new `SegmentIndex` with a value of zero.
    ///
    /// Creates a new `SegmentIndex` instance with a value of zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentIndex;
    ///
    /// let seg_idx = SegmentIndex::zero();
    /// assert_eq!(seg_idx.value(), 0);
    /// ```
    #[inline]
    pub const fn zero() -> Self {
        SegmentIndex::new(0)
    }

    /// Returns the value of the `SegmentIndex`.
    ///
    /// Returns the inner value of the `SegmentIndex` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentIndex;
    ///
    /// let seg_idx = SegmentIndex::new(5);
    /// assert_eq!(seg_idx.value(), 5);
    /// ```
    #[inline]
    pub const fn value(self) -> usize {
        self.0
    }

    /// Checks if the `SegmentIndex` is zero.
    ///
    /// Returns `true` if the inner value is zero, otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentIndex;
    ///
    /// let seg_idx = SegmentIndex::new(0);
    /// assert!(seg_idx.is_zero());
    /// let non_zero_seg_idx = SegmentIndex::new(5);
    /// assert!(!non_zero_seg_idx.is_zero());
    /// ```
    pub fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Adds a `SegmentLength` to the `SegmentIndex`, returning a new `SegmentIndex`.
    ///
    /// Adds a `SegmentLength` to the current `SegmentIndex`, returning a new `SegmentIndex`.
    /// If the addition would overflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SegmentIndex, SegmentLength};
    ///
    /// let seg_idx = SegmentIndex::new(5);
    /// let length = SegmentLength::new(3);
    /// let new_seg_idx = seg_idx.checked_add_len(length);
    /// assert_eq!(new_seg_idx.unwrap().value(), 8);
    /// ```
    #[inline]
    pub fn checked_add_len(self, d: SegmentLength) -> Option<Self> {
        self.0.checked_add(d.0).map(SegmentIndex)
    }

    /// Subtracts a `SegmentLength` from the `SegmentIndex`, returning a new `SegmentIndex`.
    ///
    /// Subtracts a `SegmentLength` from the current `SegmentIndex`,
    /// returning a new `SegmentIndex`.
    /// If the subtraction would underflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SegmentIndex, SegmentLength};
    ///
    /// let seg_idx = SegmentIndex::new(5);
    /// let length = SegmentLength::new(3);
    /// let new_seg_idx = seg_idx.checked_sub_len(length);
    /// assert_eq!(new_seg_idx.unwrap().value(), 2);
    /// ```
    #[inline]
    pub fn checked_sub_len(self, d: SegmentLength) -> Option<Self> {
        self.0.checked_sub(d.0).map(SegmentIndex)
    }

    /// Adds a `SegmentLength` to the `SegmentIndex`, returning a new `SegmentIndex`.
    ///
    /// Adds a `SegmentLength` to the current `SegmentIndex`, returning a new `SegmentIndex`.
    /// If the addition would overflow, it returns a `SegmentIndex` with the maximum value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SegmentIndex, SegmentLength};
    ///
    /// let seg_idx = SegmentIndex::new(5);
    /// let length = SegmentLength::new(3);
    /// let new_seg_idx = seg_idx.saturating_add_len(length);
    /// assert_eq!(new_seg_idx.value(), 8);
    /// ```
    #[inline]
    pub fn saturating_add_len(self, d: SegmentLength) -> Self {
        SegmentIndex(self.0.saturating_add(d.0))
    }

    /// Subtracts a `SegmentLength` from the `SegmentIndex`, returning a new `SegmentIndex`.
    ///
    /// Subtracts a `SegmentLength` from the current `SegmentIndex`, returning a new `SegmentIndex`.
    /// If the subtraction would underflow, it returns a `SegmentIndex` with a value of zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SegmentIndex, SegmentLength};
    ///
    /// let seg_idx = SegmentIndex::new(5);
    /// let length = SegmentLength::new(3);
    /// let new_seg_idx = seg_idx.saturating_sub_len(length);
    /// assert_eq!(new_seg_idx.value(), 2);
    /// ```
    #[inline]
    pub fn saturating_sub_len(self, d: SegmentLength) -> Self {
        SegmentIndex(self.0.saturating_sub(d.0))
    }

    /// Creates a `SegmentInterval` starting from the current `SegmentIndex` with the specified length.
    ///
    /// Creates a `SegmentInterval` that represents a half-open interval starting from the current `SegmentIndex`
    /// and extending by the specified `SegmentLength`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SegmentIndex, SegmentInterval, SegmentLength}; // Add SegmentLength here
    ///
    /// let start = SegmentIndex::new(5);
    /// let length = SegmentLength::new(10);
    /// let span: SegmentInterval = start.span_of(length);
    /// assert_eq!(span.start().value(), 5);
    /// assert_eq!(span.end().value(), 15);
    /// ```
    #[inline]
    pub fn span_of(self, len: SegmentLength) -> SegmentInterval {
        Interval::new(self, self + len)
    }
}

impl Add<SegmentLength> for SegmentIndex {
    type Output = SegmentIndex;

    /// Adds a `SegmentLength` to a `SegmentIndex`, returning a new `SegmentIndex`.
    ///
    /// This method takes a `SegmentLength` and adds it to the current `SegmentIndex`,
    /// returning a new `SegmentIndex` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SegmentIndex, SegmentLength};
    ///
    /// let seg_idx = SegmentIndex::new(5);
    /// let length = SegmentLength::new(3);
    /// let new_seg_idx = seg_idx + length;
    /// assert_eq!(new_seg_idx.value(), 8);
    /// ```
    #[inline]
    fn add(self, rhs: SegmentLength) -> Self::Output {
        SegmentIndex(
            self.0
                .checked_add(rhs.0)
                .expect("overflow in SegmentIndex + SegmentLength"),
        )
    }
}

impl Sub<SegmentLength> for SegmentIndex {
    type Output = SegmentIndex;

    /// Subtracts a `SegmentLength` from a `SegmentIndex`, returning a new `SegmentIndex`.
    ///
    /// This method takes a `SegmentLength` and subtracts it from the current `SegmentIndex`,
    /// returning a new `SegmentIndex` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SegmentIndex, SegmentLength};
    ///
    /// let seg_idx = SegmentIndex::new(5);
    /// let length = SegmentLength::new(3);
    /// let new_seg_idx = seg_idx - length;
    /// assert_eq!(new_seg_idx.value(), 2);
    /// ```
    #[inline]
    fn sub(self, rhs: SegmentLength) -> Self::Output {
        SegmentIndex(
            self.0
                .checked_sub(rhs.0)
                .expect("underflow in SegmentIndex - SegmentLength"),
        )
    }
}

impl Sub<SegmentIndex> for SegmentIndex {
    type Output = SegmentLength;

    /// Subtracts one `SegmentIndex` from another, returning a `SegmentLength`.
    ///
    /// This method takes another `SegmentIndex` and subtracts it from the current instance,
    /// returning a new `SegmentLength` that represents the difference between the two indices.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SegmentIndex, SegmentLength};
    ///
    /// let seg_idx1 = SegmentIndex::new(10);
    /// let seg_idx2 = SegmentIndex::new(5);
    /// let length = seg_idx1 - seg_idx2;
    /// assert_eq!(length.value(), 5);
    /// ```
    #[inline]
    fn sub(self, rhs: SegmentIndex) -> Self::Output {
        SegmentLength(
            self.0
                .checked_sub(rhs.0)
                .expect("underflow in SegmentIndex - SegmentIndex"),
        )
    }
}

impl AddAssign<SegmentLength> for SegmentIndex {
    /// Adds a `SegmentLength` to the current `SegmentIndex`, modifying it in place.
    ///
    /// This method takes a `SegmentLength` and adds it to the current `SegmentIndex`,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SegmentIndex, SegmentLength};
    ///
    /// let mut seg_idx = SegmentIndex::new(5);
    /// let length = SegmentLength::new(3);
    /// seg_idx += length;
    /// assert_eq!(seg_idx.value(), 8);
    /// ```
    #[inline]
    fn add_assign(&mut self, rhs: SegmentLength) {
        self.0 = self
            .0
            .checked_add(rhs.0)
            .expect("overflow in SegIdx += SegLen");
    }
}

impl SubAssign<SegmentLength> for SegmentIndex {
    /// Subtracts a `SegmentLength` from the current `SegmentIndex`, modifying it in place.
    ///
    /// This method takes a `SegmentLength` and subtracts it from the current `SegmentIndex`,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SegmentIndex, SegmentLength};
    ///
    /// let mut seg_idx = SegmentIndex::new(5);
    /// let length = SegmentLength::new(3);
    /// seg_idx -= length;
    /// assert_eq!(seg_idx.value(), 2);
    /// ```
    #[inline]
    fn sub_assign(&mut self, rhs: SegmentLength) {
        self.0 = self
            .0
            .checked_sub(rhs.0)
            .expect("underflow in SegIdx -= SegLen");
    }
}

/// Represents the length of a segment along the quay.
///
/// A `SegmentLength` is a wrapper around a primitive unsigned integer type
/// that represents the length of a segment along the quay.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::SegmentLength;
///
/// let seg_length = SegmentLength::new(10);
/// assert_eq!(seg_length.value(), 10);
/// assert_eq!(format!("{}", seg_length), "SegmentLength(10)");
/// ```
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct SegmentLength(pub usize);

impl Display for SegmentLength {
    /// Formats the `SegmentLength` as `SegmentLength(value)`.
    ///
    /// Formats the `SegmentLength` instance as a string in the format `SegmentLength(value)`,
    /// where `value` is the inner value of the `SegmentLength`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let seg_length = SegmentLength::new(10);
    /// assert_eq!(format!("{}", seg_length), "SegmentLength(10)");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SegmentLength({})", self.0)
    }
}

impl From<usize> for SegmentLength {
    /// Converts a primitive unsigned integer type into a `SegmentLength`.
    ///
    /// This implementation allows for easy conversion from a primitive unsigned integer type
    /// to a `SegmentLength`, enabling the use of `SegmentLength`
    /// in contexts where a primitive unsigned integer is available.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let value: usize = 10;
    /// let seg_length: SegmentLength = SegmentLength::from(value);
    /// assert_eq!(seg_length.value(), 10);
    /// ```
    #[inline]
    fn from(v: usize) -> Self {
        SegmentLength(v)
    }
}

impl SegmentLength {
    /// Creates a new `SegmentLength` with the given value.
    ///
    /// Creates a new `SegmentLength` instance wrapping the provided value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let seg_length = SegmentLength::new(10);
    /// assert_eq!(seg_length.value(), 10);
    /// ```
    #[inline]
    pub const fn new(v: usize) -> Self {
        SegmentLength(v)
    }

    /// Returns the value of the `SegmentLength`.
    ///
    /// Returns the inner value of the `SegmentLength` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let seg_length = SegmentLength::new(10);
    /// assert_eq!(seg_length.value(), 10);
    /// ```
    #[inline]
    pub const fn value(self) -> usize {
        self.0
    }

    /// Adds another `SegmentLength` to the current `SegmentLength`, returning a new `SegmentLength`.
    ///
    /// Adds another `SegmentLength` to the current instance,
    /// returning a new `SegmentLength` with the updated value.
    /// If the addition would overflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let seg_length1 = SegmentLength::new(10);
    /// let seg_length2 = SegmentLength::new(5);
    /// let new_seg_length = seg_length1.checked_add(seg_length2);
    /// assert_eq!(new_seg_length.unwrap().value(), 15);
    /// ```
    #[inline]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).map(SegmentLength)
    }

    /// Subtracts another `SegmentLength` from the current `SegmentLength`, returning a new `SegmentLength`.
    ///
    /// Subtracts another `SegmentLength` from the current instance,
    /// returning a new `SegmentLength` with the updated value.
    /// If the subtraction would underflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let seg_length1 = SegmentLength::new(10);
    /// let seg_length2 = SegmentLength::new(5);
    /// let new_seg_length = seg_length1.checked_sub(seg_length2);
    /// assert_eq!(new_seg_length.unwrap().value(), 5);
    /// ```
    #[inline]
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).map(SegmentLength)
    }

    /// Adds another `SegmentLength` to the current `SegmentLength`, returning a new `SegmentLength`.
    ///
    /// Adds another `SegmentLength` to the current instance,
    /// returning a new `SegmentLength` with the updated value.
    /// If the addition would overflow, it returns a `SegmentLength` with the maximum value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let seg_length1 = SegmentLength::new(10);
    /// let seg_length2 = SegmentLength::new(5);
    /// let new_seg_length = seg_length1.saturating_add(seg_length2);
    /// assert_eq!(new_seg_length.value(), 15);
    /// ```
    #[inline]
    pub fn saturating_add(self, rhs: Self) -> Self {
        SegmentLength(self.0.saturating_add(rhs.0))
    }

    /// Subtracts another `SegmentLength` from the current `SegmentLength`, returning a new `SegmentLength`.
    ///
    /// Subtracts another `SegmentLength` from the current instance,
    /// returning a new `SegmentLength` with the updated value.
    /// If the subtraction would underflow, it returns a `SegmentLength` with a value of zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let seg_length1 = SegmentLength::new(10);
    /// let seg_length2 = SegmentLength::new(5);
    /// let new_seg_length = seg_length1.saturating_sub(seg_length2);
    /// assert_eq!(new_seg_length.value(), 5);
    /// ```
    #[inline]
    pub fn saturating_sub(self, rhs: Self) -> Self {
        SegmentLength(self.0.saturating_sub(rhs.0))
    }
}

impl num_traits::Zero for SegmentLength {
    /// Returns a `SegmentLength` with a value of zero.
    ///
    /// This implementation provides a `SegmentLength` with a value of zero,
    /// which is useful when you need to initialize a `SegmentLength`
    /// without a specific value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    /// use num_traits::Zero;
    ///
    /// let seg_length: SegmentLength = SegmentLength::zero();
    /// assert!(seg_length.is_zero());
    /// ```
    #[inline]
    fn zero() -> Self {
        SegmentLength::new(0)
    }

    /// Checks if the `SegmentLength` is zero.
    ///
    /// This implementation checks if the inner value of the `SegmentLength` is zero,
    /// which is useful for determining if a `SegmentLength` represents no length.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    /// use num_traits::identities::Zero;
    ///
    /// let seg_length: SegmentLength = SegmentLength::zero();
    /// assert!(seg_length.is_zero());
    /// let non_zero_seg_length: SegmentLength = SegmentLength::new(10);
    /// assert!(!non_zero_seg_length.is_zero());
    /// ```
    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl Add for SegmentLength {
    type Output = SegmentLength;

    /// Adds two `SegmentLength`s, returning a new `SegmentLength`.
    ///
    /// This method takes another `SegmentLength` and adds it to the current instance,
    /// returning a new `SegmentLength` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let seg_length1 = SegmentLength::new(10);
    /// let seg_length2 = SegmentLength::new(5);
    /// let result = seg_length1 + seg_length2;
    /// assert_eq!(result.value(), 15);
    /// ```
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        SegmentLength(
            self.0
                .checked_add(rhs.0)
                .expect("overflow in SegmentLength + SegmentLength"),
        )
    }
}
impl Sub for SegmentLength {
    type Output = SegmentLength;

    /// Subtracts one `SegmentLength` from another, returning a new `SegmentLength`.
    ///
    /// This method takes another `SegmentLength` and subtracts it from the current instance,
    /// returning a new `SegmentLength` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let seg_length1 = SegmentLength::new(10);
    /// let seg_length2 = SegmentLength::new(5);
    /// let result = seg_length1 - seg_length2;
    /// assert_eq!(result.value(), 5);
    /// ```
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        SegmentLength(
            self.0
                .checked_sub(rhs.0)
                .expect("underflow in SegmentLength - SegmentLength"),
        )
    }
}
impl AddAssign for SegmentLength {
    /// Adds another `SegmentLength` to the current instance, modifying it in place.
    ///
    /// This method takes another `SegmentLength` and adds it to the current instance,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let mut seg_length1 = SegmentLength::new(10);
    /// let seg_length2 = SegmentLength::new(5);
    /// seg_length1 += seg_length2;
    /// assert_eq!(seg_length1.value(), 15);
    /// ```
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_add(rhs.0)
            .expect("overflow in SegLen += SegLen");
    }
}

impl SubAssign for SegmentLength {
    /// Subtracts another `SegmentLength` from the current instance, modifying it in place.
    ///
    /// This method takes another `SegmentLength` and subtracts it from the current instance,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SegmentLength;
    ///
    /// let mut seg_length1 = SegmentLength::new(10);
    /// let seg_length2 = SegmentLength::new(5);
    /// seg_length1 -= seg_length2;
    /// assert_eq!(seg_length1.value(), 5);
    /// ```
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_sub(rhs.0)
            .expect("underflow in SegLen -= SegLen");
    }
}

pub type TimePoint64 = TimePoint<i64>;
pub type TimeDelta64 = TimeDelta<i64>;

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    #[test]
    fn test_time_point_creation() {
        let tp = TimePoint::new(42);
        assert_eq!(tp.value(), 42);
    }

    #[test]
    fn test_time_point_display() {
        let tp = TimePoint::new(42);
        assert_eq!(format!("{}", tp), "TimePoint(42)");
    }

    #[test]
    fn test_time_point_from() {
        let value: i32 = 42;
        let tp: TimePoint<i32> = value.into();
        assert_eq!(tp.value(), 42);
    }

    #[test]
    fn test_time_interval_creation() {
        let start = TimePoint::new(10);
        let end = TimePoint::new(20);
        let interval: TimeInterval<i32> = TimeInterval::new(start, end);
        assert_eq!(interval.start().value(), 10);
        assert_eq!(interval.end().value(), 20);
    }

    #[test]
    fn test_time_interval_display() {
        let start = TimePoint::new(10);
        let end = TimePoint::new(20);
        let interval: TimeInterval<i32> = TimeInterval::new(start, end);
        assert_eq!(format!("{}", interval), "[TimePoint(10), TimePoint(20))");
    }

    #[test]
    fn test_timedelta_creation() {
        let delta = TimeDelta::new(42);
        assert_eq!(delta.value(), 42);
    }

    #[test]
    fn test_timedelta_zero() {
        let delta: TimeDelta<i32> = TimeDelta::zero();
        assert_eq!(delta.value(), 0);
    }

    #[test]
    fn test_timedelta_default() {
        let delta: TimeDelta<i32> = TimeDelta::default();
        assert_eq!(delta.value(), 0);
    }

    #[test]
    fn test_timedelta_display() {
        let delta = TimeDelta::new(-10);
        assert_eq!(format!("{}", delta), "TimeDelta(-10)");
    }

    #[test]
    fn test_timedelta_from() {
        let value: i32 = 42;
        let delta: TimeDelta<i32> = value.into();
        assert_eq!(delta.value(), 42);
    }

    #[test]
    fn test_timedelta_abs() {
        let delta1 = TimeDelta::new(-42);
        assert_eq!(delta1.abs().value(), 42);
        let delta2 = TimeDelta::new(42);
        assert_eq!(delta2.abs().value(), 42);
    }

    #[test]
    fn test_timedelta_is_negative() {
        assert!(TimeDelta::new(-1).is_negative());
        assert!(!TimeDelta::new(0).is_negative());
        assert!(!TimeDelta::new(1).is_negative());
    }

    #[test]
    fn test_timedelta_is_positive() {
        assert!(TimeDelta::new(1).is_positive());
        assert!(!TimeDelta::new(0).is_positive());
        assert!(!TimeDelta::new(-1).is_positive());
    }

    #[test]
    fn test_timedelta_is_zero() {
        assert!(TimeDelta::new(0).is_zero());
        assert!(!TimeDelta::new(1).is_zero());
        assert!(!TimeDelta::new(-1).is_zero());
    }

    #[test]
    fn test_timepoint_add_timedelta() {
        let tp = TimePoint::new(10);
        let delta = TimeDelta::new(5);
        assert_eq!(tp + delta, TimePoint::new(15));
    }

    #[test]
    fn test_timedelta_add_timepoint() {
        let delta = TimeDelta::new(5);
        let tp = TimePoint::new(10);
        assert_eq!(delta + tp, TimePoint::new(15));
    }

    #[test]
    fn test_timepoint_add_assign_timedelta() {
        let mut tp = TimePoint::new(10);
        tp += TimeDelta::new(5);
        assert_eq!(tp, TimePoint::new(15));
    }

    #[test]
    fn test_timepoint_sub_timedelta() {
        let tp = TimePoint::new(20);
        let delta = TimeDelta::new(5);
        assert_eq!(tp - delta, TimePoint::new(15));
    }

    #[test]
    fn test_timepoint_sub_assign_timedelta() {
        let mut tp = TimePoint::new(20);
        tp -= TimeDelta::new(5);
        assert_eq!(tp, TimePoint::new(15));
    }

    #[test]
    fn test_timepoint_sub_timepoint() {
        let tp1 = TimePoint::new(20);
        let tp2 = TimePoint::new(10);
        assert_eq!(tp1 - tp2, TimeDelta::new(10));
    }

    #[test]
    fn test_timedelta_add_timedelta() {
        let d1 = TimeDelta::new(10);
        let d2 = TimeDelta::new(5);
        assert_eq!(d1 + d2, TimeDelta::new(15));
    }

    #[test]
    fn test_timedelta_add_assign_timedelta() {
        let mut d1 = TimeDelta::new(10);
        d1 += TimeDelta::new(5);
        assert_eq!(d1, TimeDelta::new(15));
    }

    #[test]
    fn test_timedelta_sub_timedelta() {
        let d1 = TimeDelta::new(10);
        let d2 = TimeDelta::new(5);
        assert_eq!(d1 - d2, TimeDelta::new(5));
    }

    #[test]
    fn test_timedelta_sub_assign_timedelta() {
        let mut d1 = TimeDelta::new(10);
        d1 -= TimeDelta::new(5);
        assert_eq!(d1, TimeDelta::new(5));
    }

    #[test]
    fn test_timedelta_neg() {
        let delta = TimeDelta::new(42);
        assert_eq!(-delta, TimeDelta::new(-42));
        assert_eq!(-TimeDelta::new(-42), TimeDelta::new(42));
    }

    #[test]
    fn test_timepoint_checked_add() {
        let tp = TimePoint::new(10_i32);
        let delta = TimeDelta::new(5);
        assert_eq!(tp.checked_add(delta), Some(TimePoint::new(15)));
    }

    #[test]
    fn test_timepoint_checked_add_overflow() {
        let tp = TimePoint::new(i32::MAX);
        let delta = TimeDelta::new(1);
        assert_eq!(tp.checked_add(delta), None);
    }

    #[test]
    fn test_timepoint_checked_sub() {
        let tp = TimePoint::new(10_i32);
        let delta = TimeDelta::new(5);
        assert_eq!(tp.checked_sub(delta), Some(TimePoint::new(5)));
    }

    #[test]
    fn test_timepoint_checked_sub_underflow() {
        let tp = TimePoint::new(i32::MIN);
        let delta = TimeDelta::new(1);
        assert_eq!(tp.checked_sub(delta), None);
    }

    #[test]
    fn test_timepoint_saturating_add() {
        let tp = TimePoint::new(i32::MAX - 1);
        let delta = TimeDelta::new(5);
        assert_eq!(tp.saturating_add(delta), TimePoint::new(i32::MAX));
    }

    #[test]
    fn test_timepoint_saturating_sub() {
        let tp = TimePoint::new(i32::MIN + 1);
        let delta = TimeDelta::new(5);
        assert_eq!(tp.saturating_sub(delta), TimePoint::new(i32::MIN));
    }

    #[test]
    #[should_panic(expected = "overflow in TimePoint + TimeDelta")]
    fn test_timepoint_add_panic_on_overflow() {
        let tp = TimePoint::new(i32::MAX);
        let delta = TimeDelta::new(1);
        let _ = tp + delta;
    }

    #[test]
    #[should_panic(expected = "overflow in TimePoint - TimeDelta")]
    fn test_timepoint_sub_panic_on_underflow() {
        let tp = TimePoint::new(i32::MIN);
        let delta = TimeDelta::new(1);
        let _ = tp - delta;
    }

    #[test]
    #[should_panic(expected = "overflow in TimeDelta + TimeDelta")]
    fn test_timedelta_add_panic_on_overflow() {
        let d1 = TimeDelta::new(i32::MAX);
        let d2 = TimeDelta::new(1);
        let _ = d1 + d2;
    }

    #[test]
    #[should_panic(expected = "overflow in TimeDelta - TimeDelta")]
    fn test_timedelta_sub_panic_on_underflow() {
        let d1 = TimeDelta::new(i32::MIN);
        let d2 = TimeDelta::new(1);
        let _ = d1 - d2;
    }

    #[test]
    #[should_panic(expected = "overflow in -TimeDelta")]
    fn test_timedelta_neg_panic_on_overflow() {
        let delta = TimeDelta::new(i32::MIN);
        let _ = -delta;
    }

    #[test]
    fn u64_point_plus_i64_delta() {
        let t = TimePoint64::new(10);
        let dt = TimeDelta64::new(-3);
        assert_eq!((t + dt).value(), 7);
    }

    #[test]
    fn u64_point_minus_point_gives_i64_delta() {
        let a = TimePoint64::new(5);
        let b = TimePoint64::new(12);
        let dt: TimeDelta64 = b - a;
        assert_eq!(dt.value(), 7);
    }

    #[test]
    fn test_segment_index_creation() {
        let seg_idx = SegmentIndex::new(5);
        assert_eq!(seg_idx.value(), 5);
    }

    #[test]
    fn test_segment_index_zero() {
        let seg_idx = SegmentIndex::zero();
        assert_eq!(seg_idx.value(), 0);
        assert!(seg_idx.is_zero());
    }

    #[test]
    fn test_segment_index_display() {
        let seg_idx = SegmentIndex::new(5);
        assert_eq!(format!("{}", seg_idx), "SegmentIndex(5)");
    }

    #[test]
    fn test_segment_index_from() {
        let value: usize = 5;
        let seg_idx: SegmentIndex = value.into();
        assert_eq!(seg_idx.value(), 5);
    }

    #[test]
    fn test_segment_index_add_length() {
        let seg_idx = SegmentIndex::new(5);
        let length = SegmentLength::new(3);
        assert_eq!((seg_idx + length).value(), 8);
    }

    #[test]
    fn test_segment_index_add_assign_length() {
        let mut seg_idx = SegmentIndex::new(5);
        seg_idx += SegmentLength::new(3);
        assert_eq!(seg_idx.value(), 8);
    }

    #[test]
    fn test_segment_index_sub_length() {
        let seg_idx = SegmentIndex::new(5);
        let length = SegmentLength::new(3);
        assert_eq!((seg_idx - length).value(), 2);
    }

    #[test]
    fn test_segment_index_sub_assign_length() {
        let mut seg_idx = SegmentIndex::new(5);
        seg_idx -= SegmentLength::new(3);
        assert_eq!(seg_idx.value(), 2);
    }

    #[test]
    fn test_segment_index_sub_index() {
        let seg_idx1 = SegmentIndex::new(10);
        let seg_idx2 = SegmentIndex::new(4);
        let length = seg_idx1 - seg_idx2;
        assert_eq!(length.value(), 6);
        assert_eq!(length, SegmentLength::new(6));
    }

    #[test]
    fn test_segment_index_checked_add_len() {
        let seg_idx = SegmentIndex::new(usize::MAX - 1);
        let length = SegmentLength::new(1);
        assert_eq!(
            seg_idx.checked_add_len(length),
            Some(SegmentIndex::new(usize::MAX))
        );
        let length_overflow = SegmentLength::new(2);
        assert_eq!(seg_idx.checked_add_len(length_overflow), None);
    }

    #[test]
    fn test_segment_index_checked_sub_len() {
        let seg_idx = SegmentIndex::new(1);
        let length = SegmentLength::new(1);
        assert_eq!(seg_idx.checked_sub_len(length), Some(SegmentIndex::new(0)));
        let length_underflow = SegmentLength::new(2);
        assert_eq!(seg_idx.checked_sub_len(length_underflow), None);
    }

    #[test]
    fn test_segment_index_saturating_add_len() {
        let seg_idx = SegmentIndex::new(usize::MAX - 1);
        let length = SegmentLength::new(5);
        assert_eq!(
            seg_idx.saturating_add_len(length),
            SegmentIndex::new(usize::MAX)
        );
    }

    #[test]
    fn test_segment_index_saturating_sub_len() {
        let seg_idx = SegmentIndex::new(5);
        let length = SegmentLength::new(10);
        assert_eq!(seg_idx.saturating_sub_len(length), SegmentIndex::new(0));
    }

    #[test]
    fn test_segment_index_span_of() {
        let seg_idx = SegmentIndex::new(5);
        let length = SegmentLength::new(10);
        let interval = seg_idx.span_of(length);
        assert_eq!(interval.start(), SegmentIndex::new(5));
        assert_eq!(interval.end(), SegmentIndex::new(15));
    }

    #[test]
    #[should_panic(expected = "overflow in SegmentIndex + SegmentLength")]
    fn test_segment_index_add_panic_on_overflow() {
        let seg_idx = SegmentIndex::new(usize::MAX);
        let length = SegmentLength::new(1);
        let _ = seg_idx + length;
    }

    #[test]
    #[should_panic(expected = "underflow in SegmentIndex - SegmentLength")]
    fn test_segment_index_sub_panic_on_underflow() {
        let seg_idx = SegmentIndex::new(0);
        let length = SegmentLength::new(1);
        let _ = seg_idx - length;
    }

    #[test]
    fn test_segment_length_creation() {
        let seg_len = SegmentLength::new(10);
        assert_eq!(seg_len.value(), 10);
    }

    #[test]
    fn test_segment_length_zero() {
        let seg_len: SegmentLength = num_traits::Zero::zero();
        assert_eq!(seg_len.value(), 0);
        assert!(seg_len.is_zero());
    }

    #[test]
    fn test_segment_length_display() {
        let seg_len = SegmentLength::new(10);
        assert_eq!(format!("{}", seg_len), "SegmentLength(10)");
    }

    #[test]
    fn test_segment_length_from() {
        let value: usize = 10;
        let seg_len: SegmentLength = value.into();
        assert_eq!(seg_len.value(), 10);
    }

    #[test]
    fn test_segment_length_add_length() {
        let len1 = SegmentLength::new(10);
        let len2 = SegmentLength::new(5);
        assert_eq!((len1 + len2).value(), 15);
    }

    #[test]
    fn test_segment_length_add_assign_length() {
        let mut len1 = SegmentLength::new(10);
        len1 += SegmentLength::new(5);
        assert_eq!(len1.value(), 15);
    }

    #[test]
    fn test_segment_length_sub_length() {
        let len1 = SegmentLength::new(10);
        let len2 = SegmentLength::new(5);
        assert_eq!((len1 - len2).value(), 5);
    }

    #[test]
    fn test_segment_length_sub_assign_length() {
        let mut len1 = SegmentLength::new(10);
        len1 -= SegmentLength::new(5);
        assert_eq!(len1.value(), 5);
    }

    #[test]
    #[should_panic(expected = "overflow in SegmentLength + SegmentLength")]
    fn test_segment_length_add_panic_on_overflow() {
        let len1 = SegmentLength::new(usize::MAX);
        let len2 = SegmentLength::new(1);
        let _ = len1 + len2;
    }

    #[test]
    #[should_panic(expected = "underflow in SegmentLength - SegmentLength")]
    fn test_segment_length_sub_panic_on_underflow() {
        let len1 = SegmentLength::new(0);
        let len2 = SegmentLength::new(1);
        let _ = len1 - len2;
    }
}
