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
//! of the problem: **time** and **space**.
//!
//! ## Key Concepts
//!
//! - **Time**:
//!   - `TimePoint<T>`: Represents a specific point in time.
//!   - `TimeDelta<T>`: Represents a duration or the difference between two time points.
//!   - `TimeInterval<T>`: A half-open interval `[start, end)` composed of two `TimePoint`s.
//!
//! - **Space**:
//!   - `SpacePosition`: Represents a discrete position along the quay.
//!   - `SpaceLength`: Represents a length or size, such as that of a vessel.
//!   - `SpaceInterval`: A half-open interval `[start, end)` representing a contiguous section of the quay.
//!
//! - **Cost**:
//!   - `Cost`: Represents a cost associated with a specific operation or allocation.
//!
//! The use of distinct newtypes enforces correctness at compile time—for example,
//! preventing the addition of two `TimePoint`s.
//! All types implement standard arithmetic traits with checked operations
//! to prevent overflow and underflow, ensuring robust calculations.

#[allow(dead_code)]
use crate::primitives::Interval;
use num_traits::{
    CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, PrimInt, SaturatingAdd, SaturatingMul,
    SaturatingSub, Signed, Zero,
};
use std::{
    fmt::Display,
    iter::Sum,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

pub trait DomainType: PrimInt + Signed {}

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

impl<T: PrimInt> Default for TimePoint<T> {
    /// Creates a default `TimePoint` with a value of zero.
    ///
    /// This is useful for initializing a `TimePoint` to a known state.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimePoint;
    ///
    /// let tp: TimePoint<i32> = TimePoint::default();
    /// assert_eq!(tp.value(), 0);
    /// ```
    #[inline]
    fn default() -> Self {
        TimePoint(T::zero())
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn is_zero(self) -> bool {
        self.0.is_zero()
    }

    /// Clamps the `TimeDelta` between `min` and `max`.
    ///
    /// Returns `min` if `self < min`, `max` if `self > max`, otherwise returns `self`.
    ///
    /// # Panics
    ///
    /// Panics if `min > max`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta = TimeDelta::new(5);
    /// let clamped = delta.clamp(TimeDelta::new(0), TimeDelta::new(10));
    /// assert_eq!(clamped.value(), 5);
    /// ```
    #[inline]
    pub fn clamp(self, min: TimeDelta<T>, max: TimeDelta<T>) -> TimeDelta<T> {
        assert!(min <= max, "min must be <= max");
        if self < min {
            min
        } else if self > max {
            max
        } else {
            self
        }
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
    /// let tp = TimePoint::new(42_i32);
    /// assert_eq!(tp.value(), 42);
    /// ```
    #[inline]
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
    #[inline]
    pub const fn value(self) -> T {
        self.0
    }
}

impl<T: PrimInt + Signed> TimePoint<T> {
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

impl<T: PrimInt + Signed> CheckedAdd for TimeDelta<T> {
    /// Checks if adding another `TimeDelta` results in overflow.
    ///
    /// Returns `None` if the addition would overflow, otherwise returns `Some(TimeDelta)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta1 = TimeDelta::new(10);
    /// let delta2 = TimeDelta::new(5);
    /// assert_eq!(delta1.checked_add(delta2), Some(TimeDelta::new(15)));
    ///
    /// let max_delta = TimeDelta::new(i32::MAX);
    /// assert!(max_delta.checked_add(TimeDelta::new(1)).is_none());
    /// ```
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_add(&rhs.0).map(TimeDelta)
    }
}

impl<T: PrimInt + Signed> SaturatingAdd for TimeDelta<T> {
    /// Adds another `TimeDelta` and saturates at the numeric bounds.
    ///
    /// Returns a new `TimeDelta` that is the result of the addition,
    /// saturating at the maximum or minimum value if overflow occurs.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta1 = TimeDelta::new(i32::MAX - 1);
    /// let delta2 = TimeDelta::new(5);
    /// let result = delta1.saturating_add(delta2);
    /// assert_eq!(result.value(), i32::MAX);
    /// ```
    fn saturating_add(&self, rhs: &Self) -> Self {
        TimeDelta(self.0.saturating_add(rhs.0))
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

impl<T: PrimInt + Signed> CheckedSub for TimeDelta<T> {
    /// Checks if subtracting another `TimeDelta` results in underflow.
    ///
    /// Returns `None` if the subtraction would underflow, otherwise returns `Some(TimeDelta)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta1 = TimeDelta::new(10);
    /// let delta2 = TimeDelta::new(5);
    /// assert_eq!(delta1.checked_sub(delta2), Some(TimeDelta::new(5)));
    ///
    /// let min_delta = TimeDelta::new(i32::MIN);
    /// assert!(min_delta.checked_sub(TimeDelta::new(1)).is_none());
    /// ```
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_sub(&rhs.0).map(TimeDelta)
    }
}

impl<T: PrimInt + Signed> SaturatingSub for TimeDelta<T> {
    /// Subtracts another `TimeDelta` and saturates at the numeric bounds.
    ///
    /// Returns a new `TimeDelta` that is the result of the subtraction,
    /// saturating at the maximum or minimum value if underflow occurs.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::TimeDelta;
    ///
    /// let delta1 = TimeDelta::new(i32::MIN + 1);
    /// let delta2 = TimeDelta::new(5);
    /// let result = delta1.saturating_sub(delta2);
    /// assert_eq!(result.value(), i32::MIN);
    /// ```
    fn saturating_sub(&self, rhs: &Self) -> Self {
        TimeDelta(self.0.saturating_sub(rhs.0))
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
                .expect("overflow in TimeDelta * scalar"),
        )
    }
}

impl<T: PrimInt + Signed> MulAssign<T> for TimeDelta<T> {
    /// Multiplies the `TimeDelta` by a primitive integer, modifying it in place.
    ///
    /// This method takes a primitive integer and multiplies it with the current `TimeDelta`,
    /// modifying the current instance to reflect the new value.
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
    /// let mut delta = TimeDelta::new(10);
    /// delta *= 2;
    /// assert_eq!(delta.value(), 20);
    /// ```
    fn mul_assign(&mut self, rhs: T) {
        self.0 = self
            .0
            .checked_mul(&rhs)
            .expect("overflow in TimeDelta *= scalar");
    }
}

impl<T: PrimInt + Signed> Div<T> for TimeDelta<T> {
    type Output = TimeDelta<T>;

    /// Divides the `TimeDelta` by a primitive integer, returning a new `TimeDelta`.
    ///
    /// This method takes a primitive integer and divides the current `TimeDelta` by it,
    /// returning a new `TimeDelta` with the updated value.
    ///
    /// # Note
    /// For signed `T`, division truncates toward zero (Rust semantics):
    /// `10 / -3 == -3`, not `-4`. Panics on division by zero or `MIN / -1`.
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
                .expect("div-by-zero or overflow in TimeDelta / scalar"),
        )
    }
}

impl<T: PrimInt + Signed> DivAssign<T> for TimeDelta<T> {
    /// Divides the `TimeDelta` by a primitive integer, modifying it in place.
    ///
    /// This method takes a primitive integer and divides the current `TimeDelta` by it,
    /// modifying the current instance to reflect the new value.
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
    /// let mut delta = TimeDelta::new(20);
    /// delta /= 2;
    /// assert_eq!(delta.value(), 10);
    /// ```
    fn div_assign(&mut self, rhs: T) {
        self.0 = self
            .0
            .checked_div(&rhs)
            .expect("div-by-zero or overflow in TimeDelta /= scalar");
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

/// Represents a position along a one-dimensional space (e.g., a quay).
///
/// A `SpacePosition` is a wrapper around a primitive unsigned integer type
/// that represents a specific position along a quay or similar structure.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::SpacePosition;
///
/// let pos = SpacePosition::new(5);
/// assert_eq!(pos.value(), 5);
/// assert_eq!(format!("{}", pos), "SpacePosition(5)");
/// ```
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct SpacePosition(usize);

/// Represents a contiguous half-open interval `[start, end)` along the space.
///
/// A `SpaceInterval` is a half-open interval defined by a start and end `SpacePosition`.
/// It represents a contiguous segment of space, such as a section of a quay.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::{SpacePosition, SpaceInterval, SpaceLength};
///
/// let start = SpacePosition::new(5);
/// let length = SpaceLength::new(10);
///
/// let span = start.span_of(length);
/// assert_eq!(span.unwrap().start().value(), 5);
/// assert_eq!(span.unwrap().end().value(), 15);
/// ```
pub type SpaceInterval = Interval<SpacePosition>;

impl Display for SpacePosition {
    /// Formats the `SpacePosition` as `SpacePosition(value)`.
    ///
    /// Formats the `SpacePosition` instance as a string in the format `SpacePosition(value)`,
    /// where `value` is the inner value of the `SpacePosition`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpacePosition;
    ///
    /// let pos = SpacePosition::new(5);
    /// assert_eq!(format!("{}", pos), "SpacePosition(5)");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SpacePosition({})", self.0)
    }
}

impl From<usize> for SpacePosition {
    /// Converts a primitive unsigned integer type into a `SpacePosition`.
    ///
    /// This implementation allows for easy conversion from a primitive unsigned integer type
    /// to a `SpacePosition`, enabling the use of `SpacePosition`
    /// in contexts where a primitive unsigned integer is available.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpacePosition;
    ///
    /// let value: usize = 5;
    /// let pos: SpacePosition = SpacePosition::from(value);
    /// assert_eq!(pos.value(), 5);
    /// ```
    #[inline]
    fn from(v: usize) -> Self {
        SpacePosition(v)
    }
}

impl SpacePosition {
    /// Creates a new `SpacePosition` with the given value.
    ///
    /// Creates a new `SpacePosition` instance wrapping the provided `usize` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpacePosition;
    ///
    /// let pos = SpacePosition::new(5);
    /// assert_eq!(pos.value(), 5);
    /// ```
    #[inline]
    pub const fn new(v: usize) -> Self {
        SpacePosition(v)
    }

    /// Creates a new `SpacePosition` with a value of zero.
    ///
    /// This is a convenient way to get a `SpacePosition` representing the start of the quay.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpacePosition;
    ///
    /// let pos = SpacePosition::zero();
    /// assert_eq!(pos.value(), 0);
    /// ```
    #[inline]
    pub const fn zero() -> Self {
        SpacePosition(0)
    }

    /// Returns the inner value of the `SpacePosition`.
    ///
    /// Extracts the primitive `usize` value from the `SpacePosition` wrapper.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpacePosition;
    ///
    /// let pos = SpacePosition::new(5);
    /// assert_eq!(pos.value(), 5);
    /// ```
    #[inline]
    pub const fn value(self) -> usize {
        self.0
    }

    /// Checks if the `SpacePosition` is zero.
    ///
    /// Returns `true` if the position is at the start of the quay (value is 0).
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpacePosition;
    ///
    /// assert!(SpacePosition::zero().is_zero());
    /// assert!(!SpacePosition::new(1).is_zero());
    /// ```
    #[inline]
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
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength};
    ///
    /// let pos = SpacePosition::new(usize::MAX);
    /// assert!(pos.checked_add(SpaceLength::new(1)).is_none());
    /// ```
    #[inline]
    pub fn checked_add(self, len: SpaceLength) -> Option<Self> {
        self.0.checked_add(len.0).map(SpacePosition)
    }

    /// Computes `self - len`, returning `None` if underflow occurred.
    ///
    /// Performs a subtraction that returns `None` instead of panicking if the result is negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength};
    ///
    /// let pos = SpacePosition::new(5);
    /// assert!(pos.checked_sub(SpaceLength::new(10)).is_none());
    /// ```
    #[inline]
    pub fn checked_sub(self, len: SpaceLength) -> Option<Self> {
        self.0.checked_sub(len.0).map(SpacePosition)
    }

    /// Saturating addition. Computes `self + len`, saturating at the numeric bounds.
    ///
    /// Performs an addition that returns `SpacePosition(usize::MAX)` if the result would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength};
    ///
    /// let pos = SpacePosition::new(usize::MAX - 2);
    /// let result = pos.saturating_add(SpaceLength::new(5));
    /// assert_eq!(result.value(), usize::MAX);
    /// ```
    #[inline]
    pub fn saturating_add(self, len: SpaceLength) -> Self {
        SpacePosition(self.0.saturating_add(len.0))
    }

    /// Saturating subtraction. Computes `self - len`, saturating at zero.
    ///
    /// Performs a subtraction that returns `SpacePosition(0)` if the result would be negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength};
    ///
    /// let pos = SpacePosition::new(5);
    /// let result = pos.saturating_sub(SpaceLength::new(10));
    /// assert_eq!(result.value(), 0);
    /// ```
    #[inline]
    pub fn saturating_sub(self, len: SpaceLength) -> Self {
        SpacePosition(self.0.saturating_sub(len.0))
    }

    /// Creates a half-open interval `[self, self + len)`.
    ///
    /// Returns `None` if adding the length would cause an overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength, SpaceInterval};
    ///
    /// let start = SpacePosition::new(10);
    /// let length = SpaceLength::new(20);
    /// let interval = start.span_of(length).unwrap();
    ///
    /// assert_eq!(interval.start(), start);
    /// assert_eq!(interval.end(), SpacePosition::new(30));
    /// ```
    #[inline]
    pub fn span_of(self, len: SpaceLength) -> Option<SpaceInterval> {
        self.checked_add(len)
            .map(|end| SpaceInterval::new(self, end))
    }
}

impl Add<SpaceLength> for SpacePosition {
    type Output = SpacePosition;

    /// Adds a `SpaceLength` to a `SpacePosition`, returning a new `SpacePosition`.
    ///
    /// This method takes a `SpaceLength` and adds it to the current `SpacePosition`,
    /// returning a new `SpacePosition` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength};
    ///
    /// let pos = SpacePosition::new(5);
    /// let length = SpaceLength::new(3);
    /// let new_pos = pos + length;
    /// assert_eq!(new_pos.value(), 8);
    /// ```
    #[inline]
    fn add(self, rhs: SpaceLength) -> Self::Output {
        SpacePosition(
            self.0
                .checked_add(rhs.0)
                .expect("overflow in SpacePosition + SpaceLength"),
        )
    }
}

impl Add<SpacePosition> for SpaceLength {
    type Output = SpacePosition;

    /// Adds a `SpacePosition` to a `SpaceLength`, returning a new `SpacePosition`.
    ///
    /// This method takes a `SpacePosition` and adds it to the current `SpaceLength`,
    /// returning a new `SpacePosition` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength};
    ///
    /// let length = SpaceLength::new(3);
    /// let pos = SpacePosition::new(5);
    /// let new_pos = length + pos;
    /// assert_eq!(new_pos.value(), 8);
    /// ```
    #[inline]
    fn add(self, rhs: SpacePosition) -> Self::Output {
        rhs + self
    }
}

impl Sub<SpaceLength> for SpacePosition {
    type Output = SpacePosition;

    /// Subtracts a `SpaceLength` from a `SpacePosition`, returning a new `SpacePosition`.
    ///
    /// This method takes a `SpaceLength` and subtracts it from the current `SpacePosition`,
    /// returning a new `SpacePosition` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength};
    ///
    /// let pos = SpacePosition::new(5);
    /// let length = SpaceLength::new(3);
    /// let new_pos = pos - length;
    /// assert_eq!(new_pos.value(), 2);
    /// ```
    #[inline]
    fn sub(self, rhs: SpaceLength) -> Self::Output {
        SpacePosition(
            self.0
                .checked_sub(rhs.0)
                .expect("underflow in SpacePosition - SpaceLength"),
        )
    }
}

impl Sub<SpacePosition> for SpacePosition {
    type Output = SpaceLength;

    /// Subtracts one `SpacePosition` from another, returning a `SpaceLength`.
    ///
    /// The result is the absolute (order-independent) distance between the two positions.
    /// This operation never panics.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength};
    ///
    /// let a = SpacePosition::new(10);
    /// let b = SpacePosition::new(4);
    /// assert_eq!(a - b, SpaceLength::new(6));
    /// assert_eq!(b - a, SpaceLength::new(6)); // order-independent
    /// ```
    #[inline]
    fn sub(self, rhs: SpacePosition) -> Self::Output {
        SpaceLength::new(self.value().abs_diff(rhs.value()))
    }
}

impl AddAssign<SpaceLength> for SpacePosition {
    /// Adds a `SpaceLength` to the current `SpacePosition`, modifying it in place.
    ///
    /// This method takes a `SpaceLength` and adds it to the current `SpacePosition`,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength};
    ///
    /// let mut pos = SpacePosition::new(5);
    /// let length = SpaceLength::new(3);
    /// pos += length;
    /// assert_eq!(pos.value(), 8);
    /// ```
    #[inline]
    fn add_assign(&mut self, rhs: SpaceLength) {
        self.0 = self
            .0
            .checked_add(rhs.0)
            .expect("overflow in SpacePosition += SpaceLength");
    }
}

impl SubAssign<SpaceLength> for SpacePosition {
    /// Subtracts a `SpaceLength` from the current `SpacePosition`, modifying it in place.
    ///
    /// This method takes a `SpaceLength` and subtracts it from the current `SpacePosition`,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength};
    ///
    /// let mut pos = SpacePosition::new(5);
    /// let length = SpaceLength::new(3);
    /// pos -= length;
    /// assert_eq!(pos.value(), 2);
    /// ```
    #[inline]
    fn sub_assign(&mut self, rhs: SpaceLength) {
        self.0 = self
            .0
            .checked_sub(rhs.0)
            .expect("underflow in SpacePosition -= SpaceLength");
    }
}

/// Represents a non-negative length along the space.
///
/// A `SpaceLength` is a wrapper around a primitive unsigned integer type
/// that represents a length or size along a quay or similar structure.
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::SpaceLength;
///
/// let seg_length = SpaceLength::new(10);
/// assert_eq!(seg_length.value(), 10);
/// assert_eq!(format!("{}", seg_length), "SpaceLength(10)");
/// ```
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct SpaceLength(usize);

impl Display for SpaceLength {
    /// Formats the `SpaceLength` as `SpaceLength(value)`.
    ///
    /// Formats the `SpaceLength` instance as a string in the format `SpaceLength(value)`,
    /// where `value` is the inner value of the `SpaceLength`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let seg_length = SpaceLength::new(10);
    /// assert_eq!(format!("{}", seg_length), "SpaceLength(10)");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SpaceLength({})", self.0)
    }
}

impl From<usize> for SpaceLength {
    /// Converts a primitive unsigned integer type into a `SpaceLength`.
    ///
    /// This implementation allows for easy conversion from a primitive unsigned integer type
    /// to a `SpaceLength`, enabling the use of `SpaceLength`
    /// in contexts where a primitive unsigned integer is available.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let value: usize = 10;
    /// let seg_length: SpaceLength = SpaceLength::from(value);
    /// assert_eq!(seg_length.value(), 10);
    /// ```
    #[inline]
    fn from(v: usize) -> Self {
        SpaceLength(v)
    }
}

impl SpaceLength {
    /// Creates a new `SpaceLength` with the given value.
    ///
    /// Creates a new `SpaceLength` instance wrapping the provided `usize` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::new(10);
    /// assert_eq!(len.value(), 10);
    /// ```
    #[inline]
    pub const fn new(v: usize) -> Self {
        SpaceLength(v)
    }

    /// Returns the inner value of the `SpaceLength`.
    ///
    /// Extracts the primitive `usize` value from the `SpaceLength` wrapper.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::new(10);
    /// assert_eq!(len.value(), 10);
    /// ```
    #[inline]
    pub const fn value(self) -> usize {
        self.0
    }

    /// Clamps the `SpaceLength` between a minimum and maximum value.
    ///
    /// Returns a new `SpaceLength` that is at least `min` and at most `max`.
    ///
    /// # Panics
    ///
    /// This method will panic if `min` is greater than `max`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::new(15);
    /// let clamped = len.clamp(SpaceLength::new(10), SpaceLength::new(20));
    /// assert_eq!(clamped.value(), 15);
    /// let clamped_low = len.clamp(SpaceLength::new(20), SpaceLength::new(30));
    /// assert_eq!(clamped_low.value(), 20);
    /// let clamped_high = len.clamp(SpaceLength::new(5), SpaceLength::new(10));
    /// assert_eq!(clamped_high.value(), 10);
    /// ```
    #[inline]
    pub fn clamp(self, min: Self, max: Self) -> Self {
        assert!(min <= max, "min must be <= max");
        SpaceLength(self.0.clamp(min.0, max.0))
    }

    /// Computes `self + rhs`, returning `None` if overflow occurred.
    ///
    /// Performs an addition that returns `None` instead of panicking if the result overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::new(usize::MAX);
    /// assert!(len.checked_add(SpaceLength::new(1)).is_none());
    /// ```
    #[inline]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).map(SpaceLength)
    }

    /// Computes `self - rhs`, returning `None` if underflow occurred.
    ///
    /// Performs a subtraction that returns `None` instead of panicking if the result is negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::new(5);
    /// assert!(len.checked_sub(SpaceLength::new(10)).is_none());
    /// ```
    #[inline]
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).map(SpaceLength)
    }

    /// Saturating addition. Computes `self + rhs`, saturating at the numeric bounds.
    ///
    /// Performs an addition that returns `SpaceLength(usize::MAX)` if the result would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::new(usize::MAX - 2);
    /// let result = len.saturating_add(SpaceLength::new(5));
    /// assert_eq!(result.value(), usize::MAX);
    /// ```
    #[inline]
    pub fn saturating_add(self, rhs: Self) -> Self {
        SpaceLength(self.0.saturating_add(rhs.0))
    }

    /// Saturating subtraction. Computes `self - rhs`, saturating at zero.
    ///
    /// Performs a subtraction that returns `SpaceLength(0)` if the result would be negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::new(5);
    /// let result = len.saturating_sub(SpaceLength::new(10));
    /// assert_eq!(result.value(), 0);
    /// ```
    #[inline]
    pub fn saturating_sub(self, rhs: Self) -> Self {
        SpaceLength(self.0.saturating_sub(rhs.0))
    }

    /// Computes `self * rhs`, returning `None` if overflow occurred.
    ///
    /// Performs a multiplication that returns `None` instead of panicking if the result overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::new(usize::MAX);
    /// assert!(len.checked_mul(2).is_none());
    /// ```
    #[inline]
    pub fn checked_mul(self, rhs: usize) -> Option<Self> {
        self.0.checked_mul(rhs).map(SpaceLength)
    }

    /// Computes `self / rhs`, returning `None` if `rhs` is zero.
    ///
    /// Performs a division that returns `None` if the divisor is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::new(10);
    /// assert!(len.checked_div(0).is_none());
    /// ```
    #[inline]
    pub fn checked_div(self, rhs: usize) -> Option<Self> {
        self.0.checked_div(rhs).map(SpaceLength)
    }

    /// Saturating multiplication. Computes `self * rhs`, saturating at the numeric bounds.
    ///
    /// Performs a multiplication that returns `SpaceLength(usize::MAX)` if the result would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::new(usize::MAX / 2);
    /// let result = len.saturating_mul(3);
    /// assert_eq!(result.value(), usize::MAX);
    /// ```
    #[inline]
    pub fn saturating_mul(self, rhs: usize) -> Self {
        Self(self.0.saturating_mul(rhs))
    }

    /// Creates a new `SpaceLength` with a value of zero.
    ///
    /// This is useful for representing a zero-length segment.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::zero();
    /// assert!(len.is_zero());
    /// ```
    #[inline]
    pub const fn zero() -> Self {
        Self(0)
    }

    /// Returns the absolute value of the `SpaceLength`.
    ///
    /// Since `SpaceLength` is always non-negative, this method simply returns a copy.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let len = SpaceLength::new(10);
    /// assert_eq!(len.abs(), len);
    /// ```
    #[inline]
    pub const fn abs(self) -> Self {
        self
    }

    /// Checks if the `SpaceLength` is zero.
    ///
    /// Returns `true` if the length is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// assert!(SpaceLength::new(0).is_zero());
    /// assert!(!SpaceLength::new(1).is_zero());
    /// ```
    #[inline]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Checks if the `SpaceLength` is positive.
    ///
    /// Returns `true` if the length is greater than zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// assert!(SpaceLength::new(1).is_positive());
    /// assert!(!SpaceLength::new(0).is_positive());
    /// ```
    #[inline]
    pub const fn is_positive(self) -> bool {
        self.0 != 0
    }
}

impl Zero for SpaceLength {
    /// Returns a `SpaceLength` with a value of zero.
    ///
    /// This implementation provides a `SpaceLength` with a value of zero,
    /// which is useful when you need to initialize a `SpaceLength`
    /// without a specific value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    /// use num_traits::Zero;
    ///
    /// let seg_length: SpaceLength = SpaceLength::zero();
    /// assert!(seg_length.is_zero());
    /// ```
    #[inline]
    fn zero() -> Self {
        SpaceLength::new(0)
    }

    /// Checks if the `SpaceLength` is zero.
    ///
    /// This implementation checks if the inner value of the `SpaceLength` is zero,
    /// which is useful for determining if a `SpaceLength` represents no length.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    /// use num_traits::identities::Zero;
    ///
    /// let seg_length: SpaceLength = SpaceLength::zero();
    /// assert!(seg_length.is_zero());
    /// let non_zero_seg_length: SpaceLength = SpaceLength::new(10);
    /// assert!(!non_zero_seg_length.is_zero());
    /// ```
    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl Add for SpaceLength {
    type Output = SpaceLength;

    /// Adds two `SpaceLength`s, returning a new `SpaceLength`.
    ///
    /// This method takes another `SpaceLength` and adds it to the current instance,
    /// returning a new `SpaceLength` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let seg_length1 = SpaceLength::new(10);
    /// let seg_length2 = SpaceLength::new(5);
    /// let result = seg_length1 + seg_length2;
    /// assert_eq!(result.value(), 15);
    /// ```
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        SpaceLength(
            self.0
                .checked_add(rhs.0)
                .expect("overflow in SpaceLength + SpaceLength"),
        )
    }
}

impl CheckedAdd for SpaceLength {
    /// Adds another `SpaceLength` to the current instance, returning `None` if overflow occurs.
    ///
    /// This method takes another `SpaceLength` and attempts to add it to the current instance,
    /// returning `None` if the addition would overflow.
    ///
    /// # Examples
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    /// use num_traits::CheckedAdd;
    ///
    /// let seg_length1 = SpaceLength::new(10);
    /// let seg_length2 = SpaceLength::new(5);
    ///
    /// // Call the trait method explicitly to avoid clashing with the inherent method
    /// let result = <SpaceLength as CheckedAdd>::checked_add(&seg_length1, &seg_length2);
    /// assert_eq!(result, Some(SpaceLength::new(15)));
    /// ```
    #[inline]
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_add(rhs.0).map(SpaceLength)
    }
}

impl SaturatingAdd for SpaceLength {
    /// Adds another `SpaceLength` to the current instance, saturating at the numeric bounds.
    ///
    /// This method takes another `SpaceLength` and adds it to the current instance,
    /// returning a new `SpaceLength` that saturates at `usize::MAX` if the addition would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let seg_length1 = SpaceLength::new(usize::MAX - 1);
    /// let seg_length2 = SpaceLength::new(2);
    /// let result = seg_length1.saturating_add(seg_length2);
    /// assert_eq!(result.value(), usize::MAX);
    /// ```
    #[inline]
    fn saturating_add(&self, rhs: &Self) -> Self {
        SpaceLength(self.0.saturating_add(rhs.0))
    }
}

impl Sub for SpaceLength {
    type Output = SpaceLength;

    /// Subtracts one `SpaceLength` from another, returning a new `SpaceLength`.
    ///
    /// This method takes another `SpaceLength` and subtracts it from the current instance,
    /// returning a new `SpaceLength` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let seg_length1 = SpaceLength::new(10);
    /// let seg_length2 = SpaceLength::new(5);
    /// let result = seg_length1 - seg_length2;
    /// assert_eq!(result.value(), 5);
    /// ```
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        SpaceLength(
            self.0
                .checked_sub(rhs.0)
                .expect("underflow in SpaceLength - SpaceLength"),
        )
    }
}

impl CheckedSub for SpaceLength {
    /// Subtracts another `SpaceLength` from the current instance, returning `None` if underflow occurs.
    ///
    /// This method takes another `SpaceLength` and attempts to subtract it from the current instance,
    /// returning `None` if the subtraction would underflow.
    ///
    /// # Examples
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    /// use num_traits::CheckedSub;
    ///
    /// let seg_length1 = SpaceLength::new(10);
    /// let seg_length2 = SpaceLength::new(5);
    ///
    /// // Call the trait method explicitly to avoid clashing with the inherent method
    /// let result = <SpaceLength as CheckedSub>::checked_sub(&seg_length1, &seg_length2);
    /// assert_eq!(result, Some(SpaceLength::new(5)));
    /// ```
    #[inline]
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).map(SpaceLength)
    }
}

impl SaturatingSub for SpaceLength {
    /// Subtracts another `SpaceLength` from the current instance, saturating at zero.
    ///
    /// This method takes another `SpaceLength` and subtracts it from the current instance,
    /// returning a new `SpaceLength` that saturates at zero if the subtraction would result in a negative value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let seg_length1 = SpaceLength::new(5);
    /// let seg_length2 = SpaceLength::new(10);
    /// let result = seg_length1.saturating_sub(seg_length2);
    /// assert_eq!(result.value(), 0);
    /// ```
    #[inline]
    fn saturating_sub(&self, rhs: &Self) -> Self {
        SpaceLength(self.0.saturating_sub(rhs.0))
    }
}

impl AddAssign for SpaceLength {
    /// Adds another `SpaceLength` to the current instance, modifying it in place.
    ///
    /// This method takes another `SpaceLength` and adds it to the current instance,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let mut seg_length1 = SpaceLength::new(10);
    /// let seg_length2 = SpaceLength::new(5);
    /// seg_length1 += seg_length2;
    /// assert_eq!(seg_length1.value(), 15);
    /// ```
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_add(rhs.0)
            .expect("overflow in SpaceLength += SpaceLength");
    }
}

impl SubAssign for SpaceLength {
    /// Subtracts another `SpaceLength` from the current instance, modifying it in place.
    ///
    /// This method takes another `SpaceLength` and subtracts it from the current instance,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let mut seg_length1 = SpaceLength::new(10);
    /// let seg_length2 = SpaceLength::new(5);
    /// seg_length1 -= seg_length2;
    /// assert_eq!(seg_length1.value(), 5);
    /// ```
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_sub(rhs.0)
            .expect("underflow in SpaceLength -= SpaceLength");
    }
}

impl Mul<usize> for SpaceLength {
    type Output = SpaceLength;

    /// Multiplies a `SpaceLength` by a primitive unsigned integer type, returning a new `SpaceLength`.
    ///
    /// This method takes a primitive unsigned integer type and multiplies it with the current `SpaceLength`,
    /// returning a new `SpaceLength` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let seg_length1 = SpaceLength::new(10);
    /// let result = seg_length1 * 2;
    /// assert_eq!(result.value(), 20);
    /// ```
    #[inline]
    fn mul(self, rhs: usize) -> Self::Output {
        SpaceLength(
            self.0
                .checked_mul(rhs)
                .expect("overflow in SpaceLength * scalar"),
        )
    }
}

impl MulAssign<usize> for SpaceLength {
    /// Multiplies the current `SpaceLength` by a primitive unsigned integer type, modifying it in place.
    ///
    /// This method takes a primitive unsigned integer type and multiplies it with the current `SpaceLength`,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let mut seg_length1 = SpaceLength::new(10);
    /// seg_length1 *= 2;
    /// assert_eq!(seg_length1.value(), 20);
    /// ```
    #[inline]
    fn mul_assign(&mut self, rhs: usize) {
        self.0 = self
            .0
            .checked_mul(rhs)
            .expect("overflow in SpaceLength *= scalar");
    }
}

impl Div<usize> for SpaceLength {
    type Output = SpaceLength;

    /// Divides one `SpaceLength` by a usize, returning a new `SpaceLength`.
    ///
    /// This method takes a usize and divides the current `SpaceLength` by it,
    /// returning a new `SpaceLength` with the updated value.
    ///
    /// # Note
    ///
    /// Unsigned integer division; panics on division by zero.
    ///
    /// # Panics
    ///
    /// This method will panic if a division by zero or an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let seg_length1 = SpaceLength::new(10);
    /// let result = seg_length1 / 2;
    /// assert_eq!(result.value(), 5);
    /// ```
    #[inline]
    fn div(self, rhs: usize) -> Self::Output {
        SpaceLength(
            self.0
                .checked_div(rhs)
                .expect("division by zero in SpaceLength / scalar"),
        )
    }
}

impl DivAssign<usize> for SpaceLength {
    /// Divides the current `SpaceLength` by a usize, modifying it in place.
    ///
    /// This method takes a usize and divides the current `SpaceLength` by it,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if a division by zero occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let mut seg_length1 = SpaceLength::new(10);
    /// seg_length1 /= 2;
    /// assert_eq!(seg_length1.value(), 5);
    /// ```
    #[inline]
    fn div_assign(&mut self, rhs: usize) {
        self.0 = self
            .0
            .checked_div(rhs)
            .expect("division by zero in SpaceLength /= scalar");
    }
}

impl Sum for SpaceLength {
    /// Sums up a collection of `SpaceLength` instances, returning a new `SpaceLength`.
    ///
    /// This method takes an iterator of `SpaceLength` instances and sums them up,
    /// returning a new `SpaceLength` that represents the total length.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let lengths = vec![SpaceLength::new(10), SpaceLength::new(5)];
    /// let total_length: SpaceLength = lengths.into_iter().sum();
    /// assert_eq!(total_length.value(), 15);
    /// ```
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + x)
    }
}

impl<'a> Sum<&'a SpaceLength> for SpaceLength {
    /// Sums up a collection of references to `SpaceLength` instances, returning a new `SpaceLength`.
    ///
    /// This method takes an iterator of references to `SpaceLength` instances and sums them up,
    /// returning a new `SpaceLength` that represents the total length.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let lengths = vec![SpaceLength::new(10), SpaceLength::new(5)];
    /// let total_length: SpaceLength = lengths.iter().sum();
    /// assert_eq!(total_length.value(), 15);
    /// ```
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + *x)
    }
}

pub type TimePoint64 = TimePoint<i64>;
pub type TimeDelta64 = TimeDelta<i64>;

impl<T: PrimInt + Signed> Interval<TimePoint<T>> {
    /// Calculates the duration of the time interval.
    ///
    /// Returns a `TimeDelta` representing the difference between the end and start points of the interval.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta, TimeInterval};
    ///
    /// let start = TimePoint::new(10);
    /// let end = TimePoint::new(20);
    /// let interval = TimeInterval::new(start, end);
    /// assert_eq!(interval.duration(), TimeDelta::new(10));
    /// ```
    #[inline]
    pub fn duration(&self) -> TimeDelta<T> {
        self.end() - self.start()
    }
}

impl Interval<SpacePosition> {
    /// Calculates the extent of the space interval.
    ///
    /// Returns a `SpaceLength` representing the difference between the end and start positions of the interval.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, SpaceLength, SpaceInterval};
    ///
    /// let start = SpacePosition::new(10);
    /// let end = SpacePosition::new(20);
    /// let interval = SpaceInterval::new(start, end);
    /// assert_eq!(interval.extent(), SpaceLength::new(10));
    /// ```
    #[inline]
    pub fn extent(&self) -> SpaceLength {
        self.end() - self.start()
    }
}

#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Cost<T>(T);

impl<T: Copy> Cost<T> {
    /// Creates a new `Cost` instance with the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let cost = Cost::new(42);
    /// assert_eq!(cost.value(), 42);
    /// ```
    #[inline]
    pub const fn new(value: T) -> Self {
        Cost(value)
    }

    /// Returns the inner value of the `Cost`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let cost = Cost::new(42);
    /// assert_eq!(cost.value(), 42);
    /// ```
    #[inline]
    pub const fn value(self) -> T {
        self.0
    }

    /// Computes `self + other`, returning `None` if overflow occurred.
    ///
    /// Performs an addition that returns `None` instead of panicking if an overflow occurs.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let cost1 = Cost::new(10);
    /// let cost2 = Cost::new(5);
    /// let result = cost1.checked_add(cost2);
    /// assert_eq!(result.unwrap().value(), 15);
    /// ```
    #[inline]
    pub fn checked_add(self, other: Cost<T>) -> Option<Self>
    where
        T: CheckedAdd<Output = T> + Copy,
    {
        self.0.checked_add(&other.0).map(Cost)
    }

    /// Computes `self - other`, returning `None` if underflow occurred.
    ///
    /// Performs a subtraction that returns `None` instead of panicking if an underflow occurs.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let cost1 = Cost::new(10);
    /// let cost2 = Cost::new(5);
    /// let result = cost1.checked_sub(cost2);
    /// assert_eq!(result.unwrap().value(), 5);
    /// ```
    #[inline]
    pub fn checked_sub(self, other: Cost<T>) -> Option<Self>
    where
        T: CheckedSub<Output = T> + Copy,
    {
        self.0.checked_sub(&other.0).map(Cost)
    }

    /// Saturating addition. Computes `self + other`, saturating at the numeric bounds.
    ///
    /// Performs an addition that returns `Cost(T::MAX)` if the result would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    /// let cost1 = Cost::new(usize::MAX - 2);
    /// let cost2 = Cost::new(5);
    /// let result = cost1.saturating_add(cost2);
    /// assert_eq!(result.value(), usize::MAX);
    /// ```
    #[inline]
    pub fn saturating_add(self, other: Cost<T>) -> Self
    where
        T: SaturatingAdd<Output = T> + Copy,
    {
        Cost(self.0.saturating_add(&other.0))
    }

    /// Saturating subtraction. Computes `self - other`, saturating at numeric bounds.
    ///
    /// Behavior depends on `T`:
    /// - Unsigned (e.g., `u32`): clamps at `0`.
    /// - Signed (e.g., `i32`): clamps at `T::MIN`.
    ///
    /// # Examples
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// // Unsigned: clamps to 0
    /// let a = Cost::new(10_u32);
    /// let b = Cost::new(20_u32);
    /// assert_eq!(a.saturating_sub(b).value(), 0);
    ///
    /// // Signed: clamps to i32::MIN
    /// let c = Cost::new(i32::MIN + 1);
    /// let d = Cost::new(5_i32);
    /// assert_eq!(c.saturating_sub(d).value(), i32::MIN);
    /// ```
    #[inline]
    pub fn saturating_sub(self, other: Cost<T>) -> Self
    where
        T: SaturatingSub<Output = T> + Copy,
    {
        Cost(self.0.saturating_sub(&other.0))
    }
}

impl<T: Copy + Display> Display for Cost<T> {
    /// Formats the `Cost` as `Cost(value)`.
    ///
    /// Formats the `Cost` instance as a string in the format `Cost(value)`,
    /// where `value` is the inner value of the `Cost`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let cost = Cost::new(42);
    /// assert_eq!(format!("{}", cost), "Cost(42)");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Cost({})", self.0)
    }
}

impl<T> Add for Cost<T>
where
    T: Copy + CheckedAdd<Output = T>,
{
    type Output = Cost<T>;

    /// Adds two `Cost` instances, returning a new `Cost`.
    ///
    /// This method takes another `Cost` and adds it to the current instance,
    /// returning a new `Cost` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let cost1 = Cost::new(10);
    /// let cost2 = Cost::new(5);
    /// let result = cost1 + cost2;
    /// assert_eq!(result.value(), 15);
    /// ```
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Cost(self.0.checked_add(&rhs.0).expect("overflow in Cost + Cost"))
    }
}

impl<T> AddAssign for Cost<T>
where
    T: Copy + CheckedAdd<Output = T>,
{
    /// Adds another `Cost` to the current instance, modifying it in place.
    ///
    /// This method takes another `Cost` and adds it to the current instance,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let mut cost1 = Cost::new(10);
    /// let cost2 = Cost::new(5);
    /// cost1 += cost2;
    /// assert_eq!(cost1.value(), 15);
    /// ```
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_add(&rhs.0)
            .expect("overflow in Cost += Cost");
    }
}

impl<T: Copy + CheckedAdd<Output = T>> CheckedAdd for Cost<T> {
    /// Adds another `Cost` to the current instance, returning `None` if overflow occurs.
    ///
    /// This method takes another `Cost` and attempts to add it to the current instance,
    /// returning `None` if the addition would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    /// use num_traits::CheckedAdd;
    ///
    /// let cost1 = Cost::new(10);
    /// let cost2 = Cost::new(5);
    ///
    /// // Call the trait method explicitly to avoid clashing with the inherent method
    /// let result = <Cost<i32> as CheckedAdd>::checked_add(&cost1, &cost2);
    /// assert_eq!(result, Some(Cost::new(15)));
    /// ```
    #[inline]
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_add(&rhs.0).map(Cost)
    }
}

impl<T> SaturatingAdd for Cost<T>
where
    T: Copy + CheckedAdd + SaturatingAdd<Output = T>,
{
    /// Adds another `Cost` to the current instance, saturating at the numeric bounds.
    ///
    /// This method takes another `Cost` and adds it to the current instance,
    /// returning a new `Cost` that saturates at `T::MAX` if the addition would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let cost1 = Cost::new(usize::MAX - 1);
    /// let cost2 = Cost::new(2);
    /// let result = cost1.saturating_add(cost2);
    /// assert_eq!(result.value(), usize::MAX);
    /// ```
    #[inline]
    fn saturating_add(&self, rhs: &Self) -> Self {
        Cost(self.0.saturating_add(&rhs.0))
    }
}

impl<T> Sub for Cost<T>
where
    T: Copy + CheckedSub<Output = T>,
{
    type Output = Cost<T>;

    /// Subtracts one `Cost` from another, returning a new `Cost`.
    ///
    /// This method takes another `Cost` and subtracts it from the current instance,
    /// returning a new `Cost` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let cost1 = Cost::new(10);
    /// let cost2 = Cost::new(5);
    /// let result = cost1 - cost2;
    /// assert_eq!(result.value(), 5);
    /// ```
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Cost(
            self.0
                .checked_sub(&rhs.0)
                .expect("underflow in Cost - Cost"),
        )
    }
}

impl<T> SubAssign for Cost<T>
where
    T: Copy + CheckedSub<Output = T>,
{
    /// Subtracts another `Cost` from the current instance, modifying it in place.
    ///
    /// This method takes another `Cost` and subtracts it from the current instance,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an underflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let mut cost1 = Cost::new(10);
    /// let cost2 = Cost::new(5);
    /// cost1 -= cost2;
    /// assert_eq!(cost1.value(), 5);
    /// ```
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_sub(&rhs.0)
            .expect("underflow in Cost -= Cost");
    }
}

impl<T: Copy + CheckedSub<Output = T>> CheckedSub for Cost<T> {
    /// Subtracts another `Cost` from the current instance, returning `None` if underflow occurs.
    ///
    /// This method takes another `Cost` and attempts to subtract it from the current instance,
    /// returning `None` if the subtraction would underflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    /// use num_traits::CheckedSub;
    ///
    /// let cost1 = Cost::new(10);
    /// let cost2 = Cost::new(5);
    ///
    /// // Call the trait method explicitly to avoid clashing with the inherent method
    /// let result = <Cost<i32> as CheckedSub>::checked_sub(&cost1, &cost2);
    /// assert_eq!(result, Some(Cost::new(5)));
    /// ```
    #[inline]
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_sub(&rhs.0).map(Cost)
    }
}

impl<T> SaturatingSub for Cost<T>
where
    T: Copy + CheckedSub<Output = T> + SaturatingSub<Output = T>,
{
    /// Subtracts another `Cost` from the current instance, saturating at zero.
    ///
    /// This method takes another `Cost` and subtracts it from the current instance,
    /// returning a new `Cost` that saturates at zero if the subtraction would result in a negative value.
    ///
    /// Behavior depends on `T`:
    /// - Unsigned (e.g., `u32`): clamps at `0`.
    /// - Signed (e.g., `i32`): clamps at `T::MIN`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let cost1 = Cost::new(15);
    /// let cost2 = Cost::new(10);
    /// let result = cost1.saturating_sub(cost2);
    /// assert_eq!(result.value(), 5);
    /// ```
    #[inline]
    fn saturating_sub(&self, rhs: &Self) -> Self {
        Cost(self.0.saturating_sub(&rhs.0))
    }
}

impl<T> Mul<T> for Cost<T>
where
    T: Copy + CheckedMul<Output = T>,
{
    type Output = Cost<T>;

    /// Multiplies a `Cost` by a primitive value, returning a new `Cost`.
    ///
    /// This method takes a primitive value and multiplies it with the current `Cost`,
    /// returning a new `Cost` with the updated value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let cost = Cost::new(10);
    /// let result = cost * 2;
    /// assert_eq!(result.value(), 20);
    /// ```
    #[inline]
    fn mul(self, rhs: T) -> Self::Output {
        Cost(self.0.checked_mul(&rhs).expect("overflow in Cost * scalar"))
    }
}

impl<T> MulAssign<T> for Cost<T>
where
    T: Copy + CheckedMul<Output = T>,
{
    /// Multiplies the current `Cost` by a primitive value, modifying it in place.
    ///
    /// This method takes a primitive value and multiplies it with the current `Cost`,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if an overflow occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let mut cost = Cost::new(10);
    /// cost *= 2;
    /// assert_eq!(cost.value(), 20);
    /// ```
    #[inline]
    fn mul_assign(&mut self, rhs: T) {
        self.0 = self
            .0
            .checked_mul(&rhs)
            .expect("overflow in Cost *= scalar");
    }
}

impl<T> Div<T> for Cost<T>
where
    T: Copy + CheckedDiv<Output = T>,
{
    type Output = Cost<T>;

    /// Divides a `Cost` by a primitive value, returning a new `Cost`.
    ///
    /// This method takes a primitive value and divides the current `Cost` by it,
    /// returning a new `Cost` with the updated value.
    ///
    /// # Note
    /// For signed `T`, division truncates toward zero. Panics on division by zero.
    /// For unsigned `T`, standard integer division.
    ///
    /// # Panics
    ///
    /// This method will panic if a division by zero occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let cost = Cost::new(10);
    /// let result = cost / 2;
    /// assert_eq!(result.value(), 5);
    /// ```
    #[inline]
    fn div(self, rhs: T) -> Self::Output {
        Cost(
            self.0
                .checked_div(&rhs)
                .expect("division by zero in Cost / scalar"),
        )
    }
}

impl<T> DivAssign<T> for Cost<T>
where
    T: Copy + CheckedDiv<Output = T>,
{
    /// Divides the current `Cost` by a primitive value, modifying it in place.
    ///
    /// This method takes a primitive value and divides the current `Cost` by it,
    /// modifying the current instance to reflect the new value.
    ///
    /// # Panics
    ///
    /// This method will panic if a division by zero occurs during the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let mut cost = Cost::new(10);
    /// cost /= 2;
    /// assert_eq!(cost.value(), 5);
    /// ```
    #[inline]
    fn div_assign(&mut self, rhs: T) {
        self.0 = self
            .0
            .checked_div(&rhs)
            .expect("division by zero in Cost /= scalar");
    }
}

impl<T> Sum for Cost<T>
where
    T: Copy + CheckedAdd<Output = T> + Zero,
{
    /// Sums up a collection of `Cost` instances, returning a new `Cost`.
    ///
    /// This method takes an iterator of `Cost` instances and sums them up,
    /// returning a new `Cost` that represents the total cost.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let costs = vec![Cost::new(10), Cost::new(5)];
    /// let total_cost: Cost<i32> = costs.into_iter().sum();
    /// assert_eq!(total_cost.value(), 15);
    /// ```
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Cost::new(T::zero()), |a, b| a + b)
    }
}

impl<'a, T> Sum<&'a Cost<T>> for Cost<T>
where
    T: Copy + CheckedAdd<Output = T> + Zero,
{
    /// Sums up a collection of references to `Cost` instances, returning a new `Cost`.
    ///
    /// This method takes an iterator of references to `Cost` instances and sums them up,
    /// returning a new `Cost` that represents the total cost.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    ///
    /// let costs = vec![Cost::new(10), Cost::new(5)];
    /// let total_cost: Cost<i32> = costs.iter().sum();
    /// assert_eq!(total_cost.value(), 15);
    /// ```
    #[inline]
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Cost::new(T::zero()), |a, b| a + *b)
    }
}

impl<T: Copy + Zero + CheckedAdd> Zero for Cost<T> {
    /// Creates a new `Cost` instance with a value of zero.
    ///
    /// This method returns a new `Cost` with the inner value set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    /// use num_traits::identities::Zero;
    ///
    /// let cost: Cost<i32> = Cost::zero();
    /// assert_eq!(cost.value(), 0);
    /// ```
    fn zero() -> Self {
        Cost(T::zero())
    }

    /// Checks if the `Cost` is zero.
    ///
    /// This method returns `true` if the inner value of the `Cost` is zero, otherwise it returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::Cost;
    /// use num_traits::identities::Zero;
    ///
    /// let cost = Cost::new(0);
    /// assert!(cost.is_zero());
    /// let non_zero_cost = Cost::new(5);
    /// assert!(!non_zero_cost.is_zero());
    /// ```
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

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
    fn test_space_position_creation() {
        let pos = SpacePosition::new(5);
        assert_eq!(pos.value(), 5);
    }

    #[test]
    fn test_space_position_zero() {
        let pos = SpacePosition::zero();
        assert_eq!(pos.value(), 0);
        assert!(pos.is_zero());
    }

    #[test]
    fn test_space_position_display() {
        let pos = SpacePosition::new(5);
        assert_eq!(format!("{}", pos), "SpacePosition(5)");
    }

    #[test]
    fn test_space_position_from() {
        let value: usize = 5;
        let pos: SpacePosition = value.into();
        assert_eq!(pos.value(), 5);
    }

    #[test]
    fn test_space_position_add_length() {
        let pos = SpacePosition::new(5);
        let length = SpaceLength::new(3);
        assert_eq!((pos + length).value(), 8);
    }

    #[test]
    fn test_space_position_add_assign_length() {
        let mut pos = SpacePosition::new(5);
        pos += SpaceLength::new(3);
        assert_eq!(pos.value(), 8);
    }

    #[test]
    fn test_space_position_sub_length() {
        let pos = SpacePosition::new(5);
        let length = SpaceLength::new(3);
        assert_eq!((pos - length).value(), 2);
    }

    #[test]
    fn test_space_position_sub_assign_length() {
        let mut pos = SpacePosition::new(5);
        pos -= SpaceLength::new(3);
        assert_eq!(pos.value(), 2);
    }

    #[test]
    fn test_space_position_sub_index() {
        let pos1 = SpacePosition::new(10);
        let pos2 = SpacePosition::new(4);
        let length = pos1 - pos2;
        assert_eq!(length.value(), 6);
        assert_eq!(length, SpaceLength::new(6));
    }

    #[test]
    fn test_space_position_checked_add() {
        let pos = SpacePosition::new(usize::MAX - 1);
        let length = SpaceLength::new(1);
        assert_eq!(
            pos.checked_add(length),
            Some(SpacePosition::new(usize::MAX))
        );
        let length_overflow = SpaceLength::new(2);
        assert_eq!(pos.checked_add(length_overflow), None);
    }

    #[test]
    fn test_space_position_checked_sub_len() {
        let pos = SpacePosition::new(1);
        let length = SpaceLength::new(1);
        assert_eq!(pos.checked_sub(length), Some(SpacePosition::new(0)));
        let length_underflow = SpaceLength::new(2);
        assert_eq!(pos.checked_sub(length_underflow), None);
    }

    #[test]
    fn test_space_position_saturating_add() {
        let pos = SpacePosition::new(usize::MAX - 1);
        let length = SpaceLength::new(5);
        assert_eq!(pos.saturating_add(length), SpacePosition::new(usize::MAX));
    }

    #[test]
    fn test_space_position_saturating_sub() {
        let pos = SpacePosition::new(5);
        let length = SpaceLength::new(10);
        assert_eq!(pos.saturating_sub(length), SpacePosition::new(0));
    }

    #[test]
    fn test_space_position_span_of() {
        let pos = SpacePosition::new(5);
        let length = SpaceLength::new(10);
        let interval = pos.span_of(length);
        assert_eq!(interval.unwrap().start(), SpacePosition::new(5));
        assert_eq!(interval.unwrap().end(), SpacePosition::new(15));
    }

    #[test]
    #[should_panic(expected = "overflow in SpacePosition + SpaceLength")]
    fn test_space_position_add_panic_on_overflow() {
        let pos = SpacePosition::new(usize::MAX);
        let length = SpaceLength::new(1);
        let _ = pos + length;
    }

    #[test]
    #[should_panic(expected = "underflow in SpacePosition - SpaceLength")]
    fn test_space_position_sub_panic_on_underflow() {
        let pos = SpacePosition::new(0);
        let length = SpaceLength::new(1);
        let _ = pos - length;
    }

    #[test]
    fn test_space_length_creation() {
        let seg_len = SpaceLength::new(10);
        assert_eq!(seg_len.value(), 10);
    }

    #[test]
    fn test_space_length_zero() {
        let seg_len: SpaceLength = num_traits::Zero::zero();
        assert_eq!(seg_len.value(), 0);
        assert!(seg_len.is_zero());
    }

    #[test]
    fn test_space_length_display() {
        let seg_len = SpaceLength::new(10);
        assert_eq!(format!("{}", seg_len), "SpaceLength(10)");
    }

    #[test]
    fn test_space_length_from() {
        let value: usize = 10;
        let seg_len: SpaceLength = value.into();
        assert_eq!(seg_len.value(), 10);
    }

    #[test]
    fn test_space_length_add_length() {
        let len1 = SpaceLength::new(10);
        let len2 = SpaceLength::new(5);
        assert_eq!((len1 + len2).value(), 15);
    }

    #[test]
    fn test_space_length_add_assign_length() {
        let mut len1 = SpaceLength::new(10);
        len1 += SpaceLength::new(5);
        assert_eq!(len1.value(), 15);
    }

    #[test]
    fn test_space_length_sub_length() {
        let len1 = SpaceLength::new(10);
        let len2 = SpaceLength::new(5);
        assert_eq!((len1 - len2).value(), 5);
    }

    #[test]
    fn test_space_length_sub_assign_length() {
        let mut len1 = SpaceLength::new(10);
        len1 -= SpaceLength::new(5);
        assert_eq!(len1.value(), 5);
    }

    #[test]
    #[should_panic(expected = "overflow in SpaceLength + SpaceLength")]
    fn test_space_length_add_panic_on_overflow() {
        let len1 = SpaceLength::new(usize::MAX);
        let len2 = SpaceLength::new(1);
        let _ = len1 + len2;
    }

    #[test]
    #[should_panic(expected = "underflow in SpaceLength - SpaceLength")]
    fn test_space_length_sub_panic_on_underflow() {
        let len1 = SpaceLength::new(0);
        let len2 = SpaceLength::new(1);
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
    #[should_panic(expected = "div-by-zero or overflow in TimeDelta / scalar")]
    fn test_timedelta_div_by_zero_panic() {
        let delta = TimeDelta::new(20_i32);
        let _ = delta / 0;
    }

    #[test]
    fn test_space_length_mul_scalar() {
        let length = SpaceLength::new(15);
        assert_eq!(length * 2, SpaceLength::new(30));
        assert_eq!(length * 0, SpaceLength::new(0));
    }

    #[test]
    fn test_space_length_div_scalar() {
        let length = SpaceLength::new(30);
        assert_eq!(length / 3, SpaceLength::new(10));
    }

    #[test]
    #[should_panic(expected = "division by zero")]
    fn test_space_length_div_by_zero_panic() {
        let length = SpaceLength::new(30);
        let _ = length / 0;
    }

    #[test]
    #[should_panic(expected = "overflow in TimeDelta * scalar")]
    fn test_timedelta_mul_panic_on_overflow() {
        let delta = TimeDelta::new(i32::MAX);
        let _ = delta * 2;
    }

    #[test]
    #[should_panic(expected = "div-by-zero or overflow in TimeDelta / scalar")]
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
    #[should_panic(expected = "overflow in SpaceLength * scalar")]
    fn test_space_length_mul_panic_on_overflow() {
        let length = SpaceLength::new(usize::MAX);
        let _ = length * 2;
    }

    #[test]
    fn test_space_length_div_truncation() {
        let length = SpaceLength::new(17);
        assert_eq!(length / 4, SpaceLength::new(4));
    }

    #[test]
    fn test_timedelta_sum() {
        let deltas = vec![TimeDelta::new(10), TimeDelta::new(20), TimeDelta::new(-5)];
        let total_owned: TimeDelta<i32> = deltas.clone().into_iter().sum();
        assert_eq!(total_owned, TimeDelta::new(25));
        let total_borrowed: TimeDelta<i32> = deltas.iter().sum();
        assert_eq!(total_borrowed, TimeDelta::new(25));
    }

    #[test]
    fn test_space_length_sum() {
        let lengths = vec![
            SpaceLength::new(5),
            SpaceLength::new(8),
            SpaceLength::new(2),
        ];
        let total_owned: SpaceLength = lengths.clone().into_iter().sum();
        assert_eq!(total_owned, SpaceLength::new(15));
        let total_borrowed: SpaceLength = lengths.iter().sum();
        assert_eq!(total_borrowed, SpaceLength::new(15));
    }

    #[test]
    fn test_assign_ops() {
        let mut delta = TimeDelta::new(20_i32);
        delta *= 2;
        assert_eq!(delta, TimeDelta::new(40));
        delta /= 4;
        assert_eq!(delta, TimeDelta::new(10));

        let mut length = SpaceLength::new(20);
        length *= 2;
        assert_eq!(length, SpaceLength::new(40));
        length /= 4;
        assert_eq!(length, SpaceLength::new(10));
    }

    #[test]
    fn test_cost_creation_and_value() {
        let cost = Cost::new(100);
        assert_eq!(cost.value(), 100);
    }

    #[test]
    fn test_cost_display() {
        let cost = Cost::new(100);
        assert_eq!(format!("{}", cost), "Cost(100)");
    }

    #[test]
    fn test_cost_arithmetic() {
        let cost1 = Cost::new(100);
        let cost2 = Cost::new(50);
        assert_eq!((cost1 + cost2).value(), 150);
        assert_eq!((cost1 - cost2).value(), 50);
    }

    #[test]
    fn test_cost_scalar_arithmetic() {
        let cost = Cost::new(100);
        assert_eq!((cost * 2).value(), 200);
        assert_eq!((cost / 4).value(), 25);
    }

    #[test]
    fn test_cost_assign_ops() {
        let mut cost = Cost::new(100);
        cost += Cost::new(50);
        assert_eq!(cost.value(), 150);
        cost -= Cost::new(25);
        assert_eq!(cost.value(), 125);
        cost *= 2;
        assert_eq!(cost.value(), 250);
        cost /= 5;
        assert_eq!(cost.value(), 50);
    }

    #[test]
    #[should_panic]
    fn test_cost_add_overflow_panics() {
        let cost = Cost::new(u32::MAX);
        let _ = cost + Cost::new(1);
    }

    #[test]
    fn test_cost_checked_ops() {
        let cost1 = Cost::new(100_u32);
        let cost2 = Cost::new(50);
        assert_eq!(cost1.checked_add(cost2).unwrap().value(), 150);
        assert_eq!(cost1.checked_sub(cost2).unwrap().value(), 50);

        let max_cost = Cost::new(u32::MAX);
        assert!(max_cost.checked_add(Cost::new(1)).is_none());
    }

    #[test]
    fn test_cost_saturating_ops() {
        let cost1 = Cost::new(u32::MAX - 10);
        let cost2 = Cost::new(20);
        assert_eq!(cost1.saturating_add(cost2).value(), u32::MAX);

        let cost3 = Cost::new(10_u32);
        let cost4 = Cost::new(20);
        assert_eq!(cost3.saturating_sub(cost4).value(), 0);
    }

    #[test]
    fn test_cost_saturating_sub_unsigned_clamps_to_zero() {
        let a = Cost::new(10_u32);
        let b = Cost::new(20_u32);
        assert_eq!(a.saturating_sub(b).value(), 0);
    }

    #[test]
    fn test_cost_saturating_sub_signed_clamps_to_min() {
        let a = Cost::new(i32::MIN + 1);
        let b = Cost::new(5_i32);
        assert_eq!(a.saturating_sub(b).value(), i32::MIN);
    }

    #[test]
    fn test_timedelta_division_truncates_toward_zero() {
        assert_eq!(TimeDelta::new(10_i32) / -3, TimeDelta::new(-3));
        assert_eq!(TimeDelta::new(-10_i32) / 3, TimeDelta::new(-3));
    }

    #[test]
    fn test_space_position_sub_is_order_independent() {
        let a = SpacePosition::new(4);
        let b = SpacePosition::new(10);
        assert_eq!(a - b, SpaceLength::new(6));
        assert_eq!(b - a, SpaceLength::new(6));
    }
}
