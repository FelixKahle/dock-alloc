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

//! # Domain-Specific Core Data Types
//!
//! This module provides the fundamental data types for modeling the Berth Allocation Problem (BAP).
//! It establishes a strong, type-safe foundation for representing the two primary domains
//! of the problem: **time** and **quay space**.
//!
//! ## Key Concepts
//!
//! - **Time**:
//!   - `TimePoint<T>`: Represents a specific point in time.
//!   - `TimeDelta<T>`: Represents a duration or the difference between two time points.
//!   - `TimeInterval<T>`: A half-open interval `[start, end)` composed of two `TimePoint`s.
//!
//! - **Quay Space**:
//!   - `QuayPosition`: Represents a discrete position along the quay.
//!   - `QuayLength`: Represents a length or size, such as that of a vessel.
//!   - `QuayInterval`: A half-open interval `[start, end)` representing a contiguous section of the quay.
//!
//! The use of distinct newtypes enforces correctness at compile time—for example,
//! preventing the addition of two `TimePoint`s.
//! All types implement standard arithmetic traits with checked operations
//! to prevent overflow and underflow, ensuring robust calculations.

#[allow(dead_code)]
use crate::primitives::Interval;
use num_traits::{PrimInt, SaturatingMul, Signed, Zero};
use std::{
    fmt::Display,
    iter::Sum,
    ops::{Add, AddAssign, Div, Mul, Neg, Sub, SubAssign},
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

impl<T: PrimInt + Signed + Display> Display for TimePoint<T> {
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

    /// Creates a new `TimeDelta` with a value of zero.
    ///
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

    /// Returns the inner value of the `TimeDelta`.
    ///
    /// Extracts the primitive integer value from the `TimeDelta` wrapper.
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
    /// Returns `true` if the inner value is less than zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// assert!(TimeDelta::new(-1).is_negative());
    /// assert!(!TimeDelta::new(0).is_negative());
    /// ```
    #[inline(always)]
    pub fn is_negative(self) -> bool {
        self.0.is_negative()
    }

    /// Checks if the `TimeDelta` is positive.
    ///
    /// Returns `true` if the inner value is greater than zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// assert!(TimeDelta::new(1).is_positive());
    /// assert!(!TimeDelta::new(0).is_positive());
    /// ```
    #[inline(always)]
    pub fn is_positive(self) -> bool {
        self.0.is_positive()
    }

    /// Checks if the `TimeDelta` is zero.
    ///
    /// Returns `true` if the inner value is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// assert!(TimeDelta::new(0).is_zero());
    /// assert!(!TimeDelta::new(1).is_zero());
    /// ```
    #[inline(always)]
    pub fn is_zero(self) -> bool {
        self.0.is_zero()
    }

    /// Computes `self + rhs`, returning `None` if overflow occurred.
    ///
    /// Performs an addition that returns `None` instead of panicking if the result overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let max_delta = TimeDelta::new(i32::MAX);
    /// assert!(max_delta.checked_add(TimeDelta::new(1)).is_none());
    /// ```
    #[inline]
    pub fn checked_add(self, rhs: TimeDelta<T>) -> Option<Self> {
        self.0.checked_add(&rhs.0).map(TimeDelta)
    }

    /// Computes `self - rhs`, returning `None` if underflow occurred.
    ///
    /// Performs a subtraction that returns `None` instead of panicking if the result underflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let min_delta = TimeDelta::new(i32::MIN);
    /// assert!(min_delta.checked_sub(TimeDelta::new(1)).is_none());
    /// ```
    #[inline]
    pub fn checked_sub(self, rhs: TimeDelta<T>) -> Option<Self> {
        self.0.checked_sub(&rhs.0).map(TimeDelta)
    }

    /// Saturating addition. Computes `self + rhs`, saturating at the numeric bounds.
    ///
    /// Performs an addition that returns the maximum or minimum value of the type
    /// if the result would otherwise overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(i32::MAX - 2);
    /// let result = delta.saturating_add(TimeDelta::new(5));
    /// assert_eq!(result.value(), i32::MAX);
    /// ```
    #[inline]
    pub fn saturating_add(self, rhs: TimeDelta<T>) -> Self {
        TimeDelta(self.0.saturating_add(rhs.0))
    }

    /// Saturating subtraction. Computes `self - rhs`, saturating at the numeric bounds.
    ///
    /// Performs a subtraction that returns the maximum or minimum value of the type
    /// if the result would otherwise overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(i32::MIN + 2);
    /// let result = delta.saturating_sub(TimeDelta::new(5));
    /// assert_eq!(result.value(), i32::MIN);
    /// ```
    #[inline]
    pub fn saturating_sub(self, rhs: TimeDelta<T>) -> Self {
        TimeDelta(self.0.saturating_sub(rhs.0))
    }

    /// Computes `self * rhs`, returning `None` if overflow occurred.
    ///
    /// Performs a multiplication that returns `None` instead of panicking if the result overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(i32::MAX);
    /// assert!(delta.checked_mul(2).is_none());
    /// ```
    #[inline]
    pub fn checked_mul(self, rhs: T) -> Option<Self> {
        self.0.checked_mul(&rhs).map(TimeDelta)
    }

    /// Saturating multiplication. Computes `self * rhs`, saturating at the numeric bounds.
    ///
    /// Performs a multiplication that returns the maximum or minimum value of the type
    /// if the result would otherwise overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(i32::MAX / 2);
    /// let result = delta.saturating_mul(3);
    /// assert_eq!(result.value(), i32::MAX);
    /// ```
    #[inline]
    pub fn saturating_mul(self, rhs: T) -> Self
    where
        T: SaturatingMul,
    {
        TimeDelta(self.0.saturating_mul(&rhs))
    }

    /// Computes `self / rhs`, returning `None` if `rhs` is zero or the division overflows.
    ///
    /// Performs a division that returns `None` if the divisor is zero or if the division
    /// would overflow (which can happen with `MIN / -1`).
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(10_i32);
    /// assert!(delta.checked_div(0).is_none());
    /// let min_delta = TimeDelta::new(i32::MIN);
    /// assert!(min_delta.checked_div(-1).is_none());
    /// ```
    #[inline]
    pub fn checked_div(self, rhs: T) -> Option<Self> {
        self.0.checked_div(&rhs).map(TimeDelta)
    }
}

impl<T: PrimInt + Signed> TimePoint<T> {
    /// Creates a new `TimePoint` with the given value.
    ///
    /// Creates a new `TimePoint` instance wrapping the provided value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimePoint;
    ///
    /// let tp = TimePoint::new(42_i32);
    /// assert_eq!(tp.value(), 42);
    /// ```
    #[inline(always)]
    pub const fn new(value: T) -> Self {
        TimePoint(value)
    }

    /// Returns the inner value of the `TimePoint`.
    ///
    /// Extracts the primitive integer value from the `TimePoint` wrapper.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimePoint;
    ///
    /// let tp = TimePoint::new(42_i32);
    /// assert_eq!(tp.value(), 42);
    /// ```
    #[inline(always)]
    pub const fn value(&self) -> T {
        self.0
    }

    /// Computes `self + delta`, returning `None` if overflow occurred.
    ///
    /// Performs an addition that returns `None` instead of panicking if the result overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let tp = TimePoint::new(i32::MAX);
    /// assert!(tp.checked_add(TimeDelta::new(1)).is_none());
    /// ```
    #[inline]
    pub fn checked_add(self, delta: TimeDelta<T>) -> Option<Self> {
        self.0.checked_add(&delta.0).map(TimePoint)
    }

    /// Computes `self - delta`, returning `None` if underflow occurred.
    ///
    /// Performs a subtraction that returns `None` instead of panicking if the result underflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let tp = TimePoint::new(i32::MIN);
    /// assert!(tp.checked_sub(TimeDelta::new(1)).is_none());
    /// ```
    #[inline]
    pub fn checked_sub(self, delta: TimeDelta<T>) -> Option<Self> {
        self.0.checked_sub(&delta.0).map(TimePoint)
    }

    /// Saturating addition. Computes `self + delta`, saturating at the numeric bounds.
    ///
    /// Performs an addition that returns `TimePoint(T::MAX)` if the result would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let tp = TimePoint::new(i32::MAX - 2);
    /// let result = tp.saturating_add(TimeDelta::new(5));
    /// assert_eq!(result.value(), i32::MAX);
    /// ```
    #[inline]
    pub fn saturating_add(self, delta: TimeDelta<T>) -> Self {
        TimePoint(self.0.saturating_add(delta.0))
    }

    /// Saturating subtraction. Computes `self - delta`, saturating at the numeric bounds.
    ///
    /// Performs a subtraction that returns `TimePoint(T::MIN)` if the result would underflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta};
    ///
    /// let tp = TimePoint::new(i32::MIN + 2);
    /// let result = tp.saturating_sub(TimeDelta::new(5));
    /// assert_eq!(result.value(), i32::MIN);
    /// ```
    #[inline]
    pub fn saturating_sub(self, delta: TimeDelta<T>) -> Self {
        TimePoint(self.0.saturating_sub(delta.0))
    }

    /// Creates a half-open interval `[self, self + len)`.
    ///
    /// This method returns `None` if the provided `len` is negative or if
    /// adding the length would cause an arithmetic overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta, TimeInterval};
    ///
    /// let start = TimePoint::new(10_i32);
    /// let length = TimeDelta::new(20);
    /// let interval = start.span_of(length).unwrap();
    ///
    /// assert_eq!(interval.start(), start);
    /// assert_eq!(interval.end(), TimePoint::new(30));
    ///
    /// // A negative length returns None
    /// assert!(start.span_of(TimeDelta::new(-1)).is_none());
    /// ```
    #[inline]
    pub fn span_of(self, len: TimeDelta<T>) -> Option<TimeInterval<T>> {
        if len.is_negative() {
            return None;
        }
        self.checked_add(len).map(|end| Interval::new(self, end))
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
    /// This method will panic if an overflow occurs during the operation.
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
    /// This method will panic if an overflow occurs during the operation.
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
    /// This method will panic if an overflow occurs during the operation.
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
    /// This method will panic if an overflow occurs during the operation.
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
                .expect("underflow in TimePoint - TimeDelta"),
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
    /// This method will panic if an underflow occurs during the operation.
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
            .expect("underflow in TimePoint -= TimeDelta");
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
    /// This method will panic if an underflow occurs during the operation.
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
                .expect("underflow in TimePoint - TimePoint"),
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
    /// This method will panic if an overflow occurs during the operation.
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
    /// This method will panic if an underflow occurs during the operation.
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
                .expect("underflow in TimeDelta - TimeDelta"),
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
    /// This method will panic if an underflow occurs during the operation.
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
            .expect("underflow in TimeDelta -= TimeDelta");
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
    /// This method will panic if an underflow occurs during the operation.
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
                .expect("underflow in -TimeDelta"),
        )
    }
}

impl<T: PrimInt + Signed> Mul<T> for TimeDelta<T> {
    type Output = TimeDelta<T>;

    /// Multiplies the `TimeDelta` by a primitive integer, returning a new `TimeDelta`.
    ///
    /// This method takes a primitive integer and multiplies it with the current `TimeDelta`,
    /// returning a new `TimeDelta` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(10);
    /// let result = delta * 2;
    /// assert_eq!(result.value(), 20);
    /// ```
    fn mul(self, rhs: T) -> Self::Output {
        TimeDelta::new(
            self.0
                .checked_mul(&rhs)
                .expect("overflow in TimeDelta * primitive integer"),
        )
    }
}

impl<T: PrimInt + Signed> Div<T> for TimeDelta<T> {
    type Output = TimeDelta<T>;

    /// Divides the `TimeDelta` by a primitive integer, returning a new `TimeDelta`.
    ///
    /// This method takes a primitive integer and divides the current `TimeDelta` by it,
    /// returning a new `TimeDelta` with the updated value.
    ///
    /// # Panics
    ///
    /// Panics on division by zero or if the division overflows (e.g., MIN / -1).
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(20);
    /// let result = delta / 2;
    /// assert_eq!(result.value(), 10);
    /// ```
    fn div(self, rhs: T) -> Self::Output {
        TimeDelta::new(
            self.0
                .checked_div(&rhs)
                .expect("overflow or division by zero in TimeDelta / primitive integer"),
        )
    }
}

impl<T: PrimInt + Signed> Zero for TimeDelta<T> {
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

impl<T: PrimInt + Signed> Sum for TimeDelta<T> {
    /// Sums up a collection of `TimeDelta` instances, returning a new `TimeDelta`.
    ///
    /// This implementation allows for summing multiple `TimeDelta` instances
    /// using an iterator, returning a new `TimeDelta` that represents the total duration.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let deltas = vec![TimeDelta::new(10), TimeDelta::new(20), TimeDelta::new(30)];
    /// let total: TimeDelta<i32> = deltas.into_iter().sum();
    /// assert_eq!(total.value(), 60);
    /// ```
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + x)
    }
}

impl<'a, T: PrimInt + Signed> Sum<&'a TimeDelta<T>> for TimeDelta<T> {
    /// Sums up a collection of references to `TimeDelta` instances, returning a new `TimeDelta`.
    ///
    /// This implementation allows for summing multiple references to `TimeDelta` instances
    /// using an iterator, returning a new `TimeDelta` that represents the total duration.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimeDelta, TimePoint};
    ///
    /// let deltas = vec![TimeDelta::new(10), TimeDelta::new(20), TimeDelta::new(30)];
    /// let total: TimeDelta<i32> = deltas.iter().sum();
    /// assert_eq!(total.value(), 60);
    /// ```
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + *x)
    }
}

/// Represents a position along a quay.
///
/// A `QuayPosition` is a wrapper around a primitive unsigned integer type
/// that represents a position along a quay.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::QuayPosition;
///
/// let seg_idx = QuayPosition::new(5);
/// assert_eq!(seg_idx.value(), 5);
/// assert_eq!(format!("{}", seg_idx), "QuayPosition(5)");
/// ```
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct QuayPosition(usize);

/// Represents an interval along a quay.
///
/// A `QuayInterval` is a half-open interval defined by a start and end `QuayPosition`.
/// It represents a contiguous section of the quay, where the start index is inclusive
/// and the end index is exclusive.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::{QuayPosition, QuayInterval, QuayLength};
///
/// let start = QuayPosition::new(5);
/// let length = QuayLength::new(10);
///
/// let span = start.span_of(length);
/// assert_eq!(span.unwrap().start().value(), 5);
/// assert_eq!(span.unwrap().end().value(), 15);
/// ```
pub type QuayInterval = Interval<QuayPosition>;

impl Display for QuayPosition {
    /// Formats the `QuayPosition` as `QuayPosition(value)`.
    ///
    /// Formats the `QuayPosition` instance as a string in the format `QuayPosition(value)`,
    /// where `value` is the inner value of the `QuayPosition`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayPosition;
    ///
    /// let seg_idx = QuayPosition::new(5);
    /// assert_eq!(format!("{}", seg_idx), "QuayPosition(5)");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "QuayPosition({})", self.0)
    }
}

impl From<usize> for QuayPosition {
    /// Converts a primitive unsigned integer type into a `QuayPosition`.
    ///
    /// This implementation allows for easy conversion from a primitive unsigned integer type
    /// to a `QuayPosition`, enabling the use of `QuayPosition`
    /// in contexts where a primitive unsigned integer is available.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayPosition;
    ///
    /// let value: usize = 5;
    /// let seg_idx: QuayPosition = QuayPosition::from(value);
    /// assert_eq!(seg_idx.value(), 5);
    /// ```
    #[inline]
    fn from(v: usize) -> Self {
        QuayPosition(v)
    }
}

impl QuayPosition {
    /// Creates a new `QuayPosition` with the given value.
    ///
    /// Creates a new `QuayPosition` instance wrapping the provided `usize` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayPosition;
    ///
    /// let pos = QuayPosition::new(5);
    /// assert_eq!(pos.value(), 5);
    /// ```
    #[inline(always)]
    pub const fn new(v: usize) -> Self {
        QuayPosition(v)
    }

    /// Creates a new `QuayPosition` with a value of zero.
    ///
    /// This is a convenient way to get a `QuayPosition` representing the start of the quay.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayPosition;
    ///
    /// let pos = QuayPosition::zero();
    /// assert_eq!(pos.value(), 0);
    /// ```
    #[inline(always)]
    pub const fn zero() -> Self {
        QuayPosition(0)
    }

    /// Returns the inner value of the `QuayPosition`.
    ///
    /// Extracts the primitive `usize` value from the `QuayPosition` wrapper.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayPosition;
    ///
    /// let pos = QuayPosition::new(5);
    /// assert_eq!(pos.value(), 5);
    /// ```
    #[inline(always)]
    pub const fn value(self) -> usize {
        self.0
    }

    /// Checks if the `QuayPosition` is zero.
    ///
    /// Returns `true` if the position is at the start of the quay (value is 0).
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayPosition;
    ///
    /// assert!(QuayPosition::zero().is_zero());
    /// assert!(!QuayPosition::new(1).is_zero());
    /// ```
    #[inline(always)]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Computes `self + len`, returning `None` if overflow occurred.
    ///
    /// Performs an addition that returns `None` instead of panicking if the result overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let pos = QuayPosition::new(usize::MAX);
    /// assert!(pos.checked_add(QuayLength::new(1)).is_none());
    /// ```
    #[inline]
    pub fn checked_add(self, len: QuayLength) -> Option<Self> {
        self.0.checked_add(len.0).map(QuayPosition)
    }

    /// Computes `self - len`, returning `None` if underflow occurred.
    ///
    /// Performs a subtraction that returns `None` instead of panicking if the result is negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let pos = QuayPosition::new(5);
    /// assert!(pos.checked_sub(QuayLength::new(10)).is_none());
    /// ```
    #[inline]
    pub fn checked_sub(self, len: QuayLength) -> Option<Self> {
        self.0.checked_sub(len.0).map(QuayPosition)
    }

    /// Saturating addition. Computes `self + len`, saturating at the numeric bounds.
    ///
    /// Performs an addition that returns `QuayPosition(usize::MAX)` if the result would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let pos = QuayPosition::new(usize::MAX - 2);
    /// let result = pos.saturating_add(QuayLength::new(5));
    /// assert_eq!(result.value(), usize::MAX);
    /// ```
    #[inline]
    pub fn saturating_add(self, len: QuayLength) -> Self {
        QuayPosition(self.0.saturating_add(len.0))
    }

    /// Saturating subtraction. Computes `self - len`, saturating at zero.
    ///
    /// Performs a subtraction that returns `QuayPosition(0)` if the result would be negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let pos = QuayPosition::new(5);
    /// let result = pos.saturating_sub(QuayLength::new(10));
    /// assert_eq!(result.value(), 0);
    /// ```
    #[inline]
    pub fn saturating_sub(self, len: QuayLength) -> Self {
        QuayPosition(self.0.saturating_sub(len.0))
    }

    /// Creates a half-open interval `[self, self + len)`.
    ///
    /// Returns `None` if adding the length would cause an overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength, QuayInterval};
    ///
    /// let start = QuayPosition::new(10);
    /// let length = QuayLength::new(20);
    /// let interval = start.span_of(length).unwrap();
    ///
    /// assert_eq!(interval.start(), start);
    /// assert_eq!(interval.end(), QuayPosition::new(30));
    /// ```
    #[inline]
    pub fn span_of(self, len: QuayLength) -> Option<QuayInterval> {
        self.checked_add(len)
            .map(|end| QuayInterval::new(self, end))
    }
}

impl Add<QuayLength> for QuayPosition {
    type Output = QuayPosition;

    /// Adds a `QuayLength` to a `QuayPosition`, returning a new `QuayPosition`.
    ///
    /// This method takes a `QuayLength` and adds it to the current `QuayPosition`,
    /// returning a new `QuayPosition` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let seg_idx = QuayPosition::new(5);
    /// let length = QuayLength::new(3);
    /// let new_seg_idx = seg_idx + length;
    /// assert_eq!(new_seg_idx.value(), 8);
    /// ```
    #[inline]
    fn add(self, rhs: QuayLength) -> Self::Output {
        QuayPosition(
            self.0
                .checked_add(rhs.0)
                .expect("overflow in QuayPosition + QuayLength"),
        )
    }
}

impl Add<QuayPosition> for QuayLength {
    type Output = QuayPosition;

    /// Adds a `QuayPosition` to a `QuayLength`, returning a new `QuayPosition`.
    ///
    /// This method takes a `QuayPosition` and adds it to the current `QuayLength`,
    /// returning a new `QuayPosition` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let length = QuayLength::new(3);
    /// let seg_idx = QuayPosition::new(5);
    /// let new_seg_idx = length + seg_idx;
    /// assert_eq!(new_seg_idx.value(), 8);
    /// ```
    #[inline]
    fn add(self, rhs: QuayPosition) -> Self::Output {
        rhs + self
    }
}

impl Sub<QuayLength> for QuayPosition {
    type Output = QuayPosition;

    /// Subtracts a `QuayLength` from a `QuayPosition`, returning a new `QuayPosition`.
    ///
    /// This method takes a `QuayLength` and subtracts it from the current `QuayPosition`,
    /// returning a new `QuayPosition` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let seg_idx = QuayPosition::new(5);
    /// let length = QuayLength::new(3);
    /// let new_seg_idx = seg_idx - length;
    /// assert_eq!(new_seg_idx.value(), 2);
    /// ```
    #[inline]
    fn sub(self, rhs: QuayLength) -> Self::Output {
        QuayPosition(
            self.0
                .checked_sub(rhs.0)
                .expect("underflow in QuayPosition - QuayLength"),
        )
    }
}

impl Sub<QuayPosition> for QuayPosition {
    type Output = QuayLength;

    /// Subtracts one `QuayPosition` from another, returning a `QuayLength`.
    ///
    /// This method takes another `QuayPosition` and subtracts it from the current instance,
    /// returning a new `QuayLength` that represents the difference between the two indices.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let seg_idx1 = QuayPosition::new(10);
    /// let seg_idx2 = QuayPosition::new(5);
    /// let length = seg_idx1 - seg_idx2;
    /// assert_eq!(length.value(), 5);
    /// ```
    #[inline]
    fn sub(self, rhs: QuayPosition) -> Self::Output {
        QuayLength(
            self.0
                .checked_sub(rhs.0)
                .expect("underflow in QuayPosition - QuayPosition"),
        )
    }
}

impl AddAssign<QuayLength> for QuayPosition {
    /// Adds a `QuayLength` to the current `QuayPosition`, modifying it in place.
    ///
    /// This method takes a `QuayLength` and adds it to the current `QuayPosition`,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let mut seg_idx = QuayPosition::new(5);
    /// let length = QuayLength::new(3);
    /// seg_idx += length;
    /// assert_eq!(seg_idx.value(), 8);
    /// ```
    #[inline]
    fn add_assign(&mut self, rhs: QuayLength) {
        self.0 = self
            .0
            .checked_add(rhs.0)
            .expect("overflow in QuayPosition += QuayLength");
    }
}

impl SubAssign<QuayLength> for QuayPosition {
    /// Subtracts a `QuayLength` from the current `QuayPosition`, modifying it in place.
    ///
    /// This method takes a `QuayLength` and subtracts it from the current `QuayPosition`,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let mut seg_idx = QuayPosition::new(5);
    /// let length = QuayLength::new(3);
    /// seg_idx -= length;
    /// assert_eq!(seg_idx.value(), 2);
    /// ```
    #[inline]
    fn sub_assign(&mut self, rhs: QuayLength) {
        self.0 = self
            .0
            .checked_sub(rhs.0)
            .expect("underflow in QuayPosition -= QuayLength");
    }
}

/// Represents the length of a segment along a quay.
///
/// A `QuayLength` is a wrapper around a primitive unsigned integer type
/// that represents the length of a segment along the quay.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::QuayLength;
///
/// let seg_length = QuayLength::new(10);
/// assert_eq!(seg_length.value(), 10);
/// assert_eq!(format!("{}", seg_length), "QuayLength(10)");
/// ```
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct QuayLength(usize);

impl Display for QuayLength {
    /// Formats the `QuayLength` as `QuayLength(value)`.
    ///
    /// Formats the `QuayLength` instance as a string in the format `QuayLength(value)`,
    /// where `value` is the inner value of the `QuayLength`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length = QuayLength::new(10);
    /// assert_eq!(format!("{}", seg_length), "QuayLength(10)");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "QuayLength({})", self.0)
    }
}

impl From<usize> for QuayLength {
    /// Converts a primitive unsigned integer type into a `QuayLength`.
    ///
    /// This implementation allows for easy conversion from a primitive unsigned integer type
    /// to a `QuayLength`, enabling the use of `QuayLength`
    /// in contexts where a primitive unsigned integer is available.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let value: usize = 10;
    /// let seg_length: QuayLength = QuayLength::from(value);
    /// assert_eq!(seg_length.value(), 10);
    /// ```
    #[inline]
    fn from(v: usize) -> Self {
        QuayLength(v)
    }
}

impl QuayLength {
    /// Creates a new `QuayLength` with the given value.
    ///
    /// Creates a new `QuayLength` instance wrapping the provided `usize` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let len = QuayLength::new(10);
    /// assert_eq!(len.value(), 10);
    /// ```
    #[inline(always)]
    pub const fn new(v: usize) -> Self {
        QuayLength(v)
    }

    /// Returns the inner value of the `QuayLength`.
    ///
    /// Extracts the primitive `usize` value from the `QuayLength` wrapper.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let len = QuayLength::new(10);
    /// assert_eq!(len.value(), 10);
    /// ```
    #[inline(always)]
    pub const fn value(self) -> usize {
        self.0
    }

    /// Computes `self + rhs`, returning `None` if overflow occurred.
    ///
    /// Performs an addition that returns `None` instead of panicking if the result overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let len = QuayLength::new(usize::MAX);
    /// assert!(len.checked_add(QuayLength::new(1)).is_none());
    /// ```
    #[inline]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).map(QuayLength)
    }

    /// Computes `self - rhs`, returning `None` if underflow occurred.
    ///
    /// Performs a subtraction that returns `None` instead of panicking if the result is negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let len = QuayLength::new(5);
    /// assert!(len.checked_sub(QuayLength::new(10)).is_none());
    /// ```
    #[inline]
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).map(QuayLength)
    }

    /// Saturating addition. Computes `self + rhs`, saturating at the numeric bounds.
    ///
    /// Performs an addition that returns `QuayLength(usize::MAX)` if the result would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let len = QuayLength::new(usize::MAX - 2);
    /// let result = len.saturating_add(QuayLength::new(5));
    /// assert_eq!(result.value(), usize::MAX);
    /// ```
    #[inline]
    pub fn saturating_add(self, rhs: Self) -> Self {
        QuayLength(self.0.saturating_add(rhs.0))
    }

    /// Saturating subtraction. Computes `self - rhs`, saturating at zero.
    ///
    /// Performs a subtraction that returns `QuayLength(0)` if the result would be negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let len = QuayLength::new(5);
    /// let result = len.saturating_sub(QuayLength::new(10));
    /// assert_eq!(result.value(), 0);
    /// ```
    #[inline]
    pub fn saturating_sub(self, rhs: Self) -> Self {
        QuayLength(self.0.saturating_sub(rhs.0))
    }

    /// Computes `self * rhs`, returning `None` if overflow occurred.
    ///
    /// Performs a multiplication that returns `None` instead of panicking if the result overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let len = QuayLength::new(usize::MAX);
    /// assert!(len.checked_mul(2).is_none());
    /// ```
    #[inline]
    pub fn checked_mul(self, rhs: usize) -> Option<Self> {
        self.0.checked_mul(rhs).map(QuayLength)
    }

    /// Computes `self / rhs`, returning `None` if `rhs` is zero.
    ///
    /// Performs a division that returns `None` if the divisor is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let len = QuayLength::new(10);
    /// assert!(len.checked_div(0).is_none());
    /// ```
    #[inline]
    pub fn checked_div(self, rhs: usize) -> Option<Self> {
        self.0.checked_div(rhs).map(QuayLength)
    }

    /// Saturating multiplication. Computes `self * rhs`, saturating at the numeric bounds.
    ///
    /// Performs a multiplication that returns `QuayLength(usize::MAX)` if the result would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let len = QuayLength::new(usize::MAX / 2);
    /// let result = len.saturating_mul(3);
    /// assert_eq!(result.value(), usize::MAX);
    /// ```
    #[inline]
    pub fn saturating_mul(self, rhs: usize) -> Self {
        Self(self.0.saturating_mul(rhs))
    }

    /// Creates a new `QuayLength` with a value of zero.
    ///
    /// This is useful for representing a zero-length segment.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let len = QuayLength::zero();
    /// assert!(len.is_zero());
    /// ```
    #[inline(always)]
    pub const fn zero() -> Self {
        Self(0)
    }

    /// Returns the absolute value of the `QuayLength`.
    ///
    /// Since `QuayLength` is always non-negative, this method simply returns a copy.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let len = QuayLength::new(10);
    /// assert_eq!(len.abs(), len);
    /// ```
    #[inline(always)]
    pub const fn abs(self) -> Self {
        self
    }

    /// Checks if the `QuayLength` is zero.
    ///
    /// Returns `true` if the length is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// assert!(QuayLength::new(0).is_zero());
    /// assert!(!QuayLength::new(1).is_zero());
    /// ```
    #[inline(always)]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Checks if the `QuayLength` is positive.
    ///
    /// Returns `true` if the length is greater than zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// assert!(QuayLength::new(1).is_positive());
    /// assert!(!QuayLength::new(0).is_positive());
    /// ```
    #[inline(always)]
    pub const fn is_positive(self) -> bool {
        self.0 != 0
    }
}

impl Zero for QuayLength {
    /// Returns a `QuayLength` with a value of zero.
    ///
    /// This implementation provides a `QuayLength` with a value of zero,
    /// which is useful when you need to initialize a `QuayLength`
    /// without a specific value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    /// use num_traits::Zero;
    ///
    /// let seg_length: QuayLength = QuayLength::zero();
    /// assert!(seg_length.is_zero());
    /// ```
    #[inline]
    fn zero() -> Self {
        QuayLength::new(0)
    }

    /// Checks if the `QuayLength` is zero.
    ///
    /// This implementation checks if the inner value of the `QuayLength` is zero,
    /// which is useful for determining if a `QuayLength` represents no length.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    /// use num_traits::identities::Zero;
    ///
    /// let seg_length: QuayLength = QuayLength::zero();
    /// assert!(seg_length.is_zero());
    /// let non_zero_seg_length: QuayLength = QuayLength::new(10);
    /// assert!(!non_zero_seg_length.is_zero());
    /// ```
    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl Add for QuayLength {
    type Output = QuayLength;

    /// Adds two `QuayLength`s, returning a new `QuayLength`.
    ///
    /// This method takes another `QuayLength` and adds it to the current instance,
    /// returning a new `QuayLength` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length1 = QuayLength::new(10);
    /// let seg_length2 = QuayLength::new(5);
    /// let result = seg_length1 + seg_length2;
    /// assert_eq!(result.value(), 15);
    /// ```
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        QuayLength(
            self.0
                .checked_add(rhs.0)
                .expect("overflow in QuayLength + QuayLength"),
        )
    }
}
impl Sub for QuayLength {
    type Output = QuayLength;

    /// Subtracts one `QuayLength` from another, returning a new `QuayLength`.
    ///
    /// This method takes another `QuayLength` and subtracts it from the current instance,
    /// returning a new `QuayLength` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length1 = QuayLength::new(10);
    /// let seg_length2 = QuayLength::new(5);
    /// let result = seg_length1 - seg_length2;
    /// assert_eq!(result.value(), 5);
    /// ```
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        QuayLength(
            self.0
                .checked_sub(rhs.0)
                .expect("underflow in QuayLength - QuayLength"),
        )
    }
}
impl AddAssign for QuayLength {
    /// Adds another `QuayLength` to the current instance, modifying it in place.
    ///
    /// This method takes another `QuayLength` and adds it to the current instance,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let mut seg_length1 = QuayLength::new(10);
    /// let seg_length2 = QuayLength::new(5);
    /// seg_length1 += seg_length2;
    /// assert_eq!(seg_length1.value(), 15);
    /// ```
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_add(rhs.0)
            .expect("overflow in QuayLength += QuayLength");
    }
}

impl SubAssign for QuayLength {
    /// Subtracts another `QuayLength` from the current instance, modifying it in place.
    ///
    /// This method takes another `QuayLength` and subtracts it from the current instance,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let mut seg_length1 = QuayLength::new(10);
    /// let seg_length2 = QuayLength::new(5);
    /// seg_length1 -= seg_length2;
    /// assert_eq!(seg_length1.value(), 5);
    /// ```
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_sub(rhs.0)
            .expect("underflow in QuayLength -= QuayLength");
    }
}

impl Mul<usize> for QuayLength {
    type Output = QuayLength;

    /// Multiplies a `QuayLength` by a primitive unsigned integer type, returning a new `QuayLength`.
    ///
    /// This method takes a primitive unsigned integer type and multiplies it with the current `QuayLength`,
    /// returning a new `QuayLength` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length1 = QuayLength::new(10);
    /// let result = seg_length1 * 2;
    /// assert_eq!(result.value(), 20);
    /// ```
    #[inline]
    fn mul(self, rhs: usize) -> Self::Output {
        QuayLength(
            self.0
                .checked_mul(rhs)
                .expect("overflow in QuayLength * usize"),
        )
    }
}

impl Div<usize> for QuayLength {
    type Output = QuayLength;

    /// Divides one `QuayLength` by a usize, returning a new `QuayLength`.
    ///
    /// This method takes a usize and divides the current `QuayLength` by it,
    /// returning a new `QuayLength` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if a division by zero or an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length1 = QuayLength::new(10);
    /// let result = seg_length1 / 2;
    /// assert_eq!(result.value(), 5);
    /// ```
    #[inline]
    fn div(self, rhs: usize) -> Self::Output {
        QuayLength(
            self.0
                .checked_div(rhs)
                .expect("division by zero in QuayLength / usize"),
        )
    }
}

impl Sum for QuayLength {
    /// Sums up a collection of `QuayLength` instances, returning a new `QuayLength`.
    ///
    /// This method takes an iterator of `QuayLength` instances and sums them up,
    /// returning a new `QuayLength` that represents the total length.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let lengths = vec![QuayLength::new(10), QuayLength::new(5)];
    /// let total_length: QuayLength = lengths.into_iter().sum();
    /// assert_eq!(total_length.value(), 15);
    /// ```
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + x)
    }
}

impl<'a> Sum<&'a QuayLength> for QuayLength {
    /// Sums up a collection of references to `QuayLength` instances, returning a new `QuayLength`.
    ///
    /// This method takes an iterator of references to `QuayLength` instances and sums them up,
    /// returning a new `QuayLength` that represents the total length.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let lengths = vec![QuayLength::new(10), QuayLength::new(5)];
    /// let total_length: QuayLength = lengths.iter().sum();
    /// assert_eq!(total_length.value(), 15);
    /// ```
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + *x)
    }
}

pub type TimePoint64 = TimePoint<i64>;
pub type TimeDelta64 = TimeDelta<i64>;

#[cfg(test)]
mod tests {
    use super::*;

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
    #[should_panic(expected = "underflow in TimePoint - TimeDelta")]
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
    #[should_panic(expected = "underflow in TimeDelta - TimeDelta")]
    fn test_timedelta_sub_panic_on_underflow() {
        let d1 = TimeDelta::new(i32::MIN);
        let d2 = TimeDelta::new(1);
        let _ = d1 - d2;
    }

    #[test]
    #[should_panic(expected = "underflow in -TimeDelta")]
    fn test_timedelta_neg_panic_on_overflow() {
        let delta = TimeDelta::new(i32::MIN);
        let _ = -delta;
    }

    #[test]
    fn i64_point_plus_i64_delta() {
        let t = TimePoint64::new(10);
        let dt = TimeDelta64::new(-3);
        assert_eq!((t + dt).value(), 7);
    }

    #[test]
    fn i64_point_minus_point_gives_i64_delta() {
        let a = TimePoint64::new(5);
        let b = TimePoint64::new(12);
        let dt: TimeDelta64 = b - a;
        assert_eq!(dt.value(), 7);
    }

    #[test]
    fn test_quay_position_creation() {
        let seg_idx = QuayPosition::new(5);
        assert_eq!(seg_idx.value(), 5);
    }

    #[test]
    fn test_quay_position_zero() {
        let seg_idx = QuayPosition::zero();
        assert_eq!(seg_idx.value(), 0);
        assert!(seg_idx.is_zero());
    }

    #[test]
    fn test_quay_position_display() {
        let seg_idx = QuayPosition::new(5);
        assert_eq!(format!("{}", seg_idx), "QuayPosition(5)");
    }

    #[test]
    fn test_quay_position_from() {
        let value: usize = 5;
        let seg_idx: QuayPosition = value.into();
        assert_eq!(seg_idx.value(), 5);
    }

    #[test]
    fn test_quay_position_add_length() {
        let seg_idx = QuayPosition::new(5);
        let length = QuayLength::new(3);
        assert_eq!((seg_idx + length).value(), 8);
    }

    #[test]
    fn test_quay_position_add_assign_length() {
        let mut seg_idx = QuayPosition::new(5);
        seg_idx += QuayLength::new(3);
        assert_eq!(seg_idx.value(), 8);
    }

    #[test]
    fn test_quay_position_sub_length() {
        let seg_idx = QuayPosition::new(5);
        let length = QuayLength::new(3);
        assert_eq!((seg_idx - length).value(), 2);
    }

    #[test]
    fn test_quay_position_sub_assign_length() {
        let mut seg_idx = QuayPosition::new(5);
        seg_idx -= QuayLength::new(3);
        assert_eq!(seg_idx.value(), 2);
    }

    #[test]
    fn test_quay_position_sub_index() {
        let seg_idx1 = QuayPosition::new(10);
        let seg_idx2 = QuayPosition::new(4);
        let length = seg_idx1 - seg_idx2;
        assert_eq!(length.value(), 6);
        assert_eq!(length, QuayLength::new(6));
    }

    #[test]
    fn test_quay_position_checked_add() {
        let seg_idx = QuayPosition::new(usize::MAX - 1);
        let length = QuayLength::new(1);
        assert_eq!(
            seg_idx.checked_add(length),
            Some(QuayPosition::new(usize::MAX))
        );
        let length_overflow = QuayLength::new(2);
        assert_eq!(seg_idx.checked_add(length_overflow), None);
    }

    #[test]
    fn test_quay_position_checked_sub_len() {
        let seg_idx = QuayPosition::new(1);
        let length = QuayLength::new(1);
        assert_eq!(seg_idx.checked_sub(length), Some(QuayPosition::new(0)));
        let length_underflow = QuayLength::new(2);
        assert_eq!(seg_idx.checked_sub(length_underflow), None);
    }

    #[test]
    fn test_quay_position_saturating_add() {
        let seg_idx = QuayPosition::new(usize::MAX - 1);
        let length = QuayLength::new(5);
        assert_eq!(
            seg_idx.saturating_add(length),
            QuayPosition::new(usize::MAX)
        );
    }

    #[test]
    fn test_quay_position_saturating_sub() {
        let seg_idx = QuayPosition::new(5);
        let length = QuayLength::new(10);
        assert_eq!(seg_idx.saturating_sub(length), QuayPosition::new(0));
    }

    #[test]
    fn test_quay_position_span_of() {
        let seg_idx = QuayPosition::new(5);
        let length = QuayLength::new(10);
        let interval = seg_idx.span_of(length);
        assert_eq!(interval.unwrap().start(), QuayPosition::new(5));
        assert_eq!(interval.unwrap().end(), QuayPosition::new(15));
    }

    #[test]
    #[should_panic(expected = "overflow in QuayPosition + QuayLength")]
    fn test_quay_position_add_panic_on_overflow() {
        let seg_idx = QuayPosition::new(usize::MAX);
        let length = QuayLength::new(1);
        let _ = seg_idx + length;
    }

    #[test]
    #[should_panic(expected = "underflow in QuayPosition - QuayLength")]
    fn test_quay_position_sub_panic_on_underflow() {
        let seg_idx = QuayPosition::new(0);
        let length = QuayLength::new(1);
        let _ = seg_idx - length;
    }

    #[test]
    fn test_quay_length_creation() {
        let seg_len = QuayLength::new(10);
        assert_eq!(seg_len.value(), 10);
    }

    #[test]
    fn test_quay_length_zero() {
        let seg_len: QuayLength = num_traits::Zero::zero();
        assert_eq!(seg_len.value(), 0);
        assert!(seg_len.is_zero());
    }

    #[test]
    fn test_quay_length_display() {
        let seg_len = QuayLength::new(10);
        assert_eq!(format!("{}", seg_len), "QuayLength(10)");
    }

    #[test]
    fn test_quay_length_from() {
        let value: usize = 10;
        let seg_len: QuayLength = value.into();
        assert_eq!(seg_len.value(), 10);
    }

    #[test]
    fn test_quay_length_add_length() {
        let len1 = QuayLength::new(10);
        let len2 = QuayLength::new(5);
        assert_eq!((len1 + len2).value(), 15);
    }

    #[test]
    fn test_quay_length_add_assign_length() {
        let mut len1 = QuayLength::new(10);
        len1 += QuayLength::new(5);
        assert_eq!(len1.value(), 15);
    }

    #[test]
    fn test_quay_length_sub_length() {
        let len1 = QuayLength::new(10);
        let len2 = QuayLength::new(5);
        assert_eq!((len1 - len2).value(), 5);
    }

    #[test]
    fn test_quay_length_sub_assign_length() {
        let mut len1 = QuayLength::new(10);
        len1 -= QuayLength::new(5);
        assert_eq!(len1.value(), 5);
    }

    #[test]
    #[should_panic(expected = "overflow in QuayLength + QuayLength")]
    fn test_quay_length_add_panic_on_overflow() {
        let len1 = QuayLength::new(usize::MAX);
        let len2 = QuayLength::new(1);
        let _ = len1 + len2;
    }

    #[test]
    #[should_panic(expected = "underflow in QuayLength - QuayLength")]
    fn test_quay_length_sub_panic_on_underflow() {
        let len1 = QuayLength::new(0);
        let len2 = QuayLength::new(1);
        let _ = len1 - len2;
    }

    #[test]
    fn test_timepoint_span_of() {
        let tp = TimePoint::new(10);
        let len = TimeDelta::new(5);
        let i = tp.span_of(len).unwrap();
        assert_eq!(i.start(), TimePoint::new(10));
        assert_eq!(i.end(), TimePoint::new(15));
        assert!(tp.span_of(TimeDelta::new(-1)).is_none());
    }

    #[test]
    fn test_timedelta_mul_scalar() {
        let delta = TimeDelta::new(10_i32);
        assert_eq!(delta * 3, TimeDelta::new(30));
        assert_eq!(delta * -2, TimeDelta::new(-20));
        assert_eq!(delta * 0, TimeDelta::new(0));
    }

    #[test]
    fn test_timedelta_div_scalar() {
        let delta = TimeDelta::new(20_i32);
        assert_eq!(delta / 2, TimeDelta::new(10));
        assert_eq!(delta / -4, TimeDelta::new(-5));
    }

    #[test]
    #[should_panic(expected = "overflow or division by zero in TimeDelta / primitive integer")]
    fn test_timedelta_div_by_zero_panic() {
        let delta = TimeDelta::new(20_i32);
        let _ = delta / 0;
    }

    #[test]
    fn test_quay_length_mul_scalar() {
        let length = QuayLength::new(15);
        assert_eq!(length * 2, QuayLength::new(30));
        assert_eq!(length * 0, QuayLength::new(0));
    }

    #[test]
    fn test_quay_length_div_scalar() {
        let length = QuayLength::new(30);
        assert_eq!(length / 3, QuayLength::new(10));
    }

    #[test]
    #[should_panic(expected = "division by zero")]
    fn test_quay_length_div_by_zero_panic() {
        let length = QuayLength::new(30);
        let _ = length / 0;
    }

    #[test]
    #[should_panic(expected = "overflow in TimeDelta * primitive integer")]
    fn test_timedelta_mul_panic_on_overflow() {
        let delta = TimeDelta::new(i32::MAX);
        let _ = delta * 2;
    }

    #[test]
    #[should_panic(expected = "overflow or division by zero")]
    fn test_timedelta_div_panic_on_overflow() {
        let delta = TimeDelta::new(i32::MIN);
        let _ = delta / -1;
    }

    #[test]
    fn test_timedelta_div_truncation() {
        let delta = TimeDelta::new(10_i32);
        assert_eq!(delta / 3, TimeDelta::new(3));
    }

    #[test]
    #[should_panic(expected = "overflow in QuayLength * usize")]
    fn test_quay_length_mul_panic_on_overflow() {
        let length = QuayLength::new(usize::MAX);
        let _ = length * 2;
    }

    #[test]
    fn test_quay_length_div_truncation() {
        let length = QuayLength::new(17);
        assert_eq!(length / 4, QuayLength::new(4));
    }
}
