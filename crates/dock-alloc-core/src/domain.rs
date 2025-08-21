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

//! This module defines the fundamental units of **time** and **space** that form
//! the domain model for the berth allocation solver. The primary goal is to
//! leverage Rust's type system to provide strong compile-time guarantees,
//! preventing common logical errors like mixing temporal and spatial units.
//!
//! All types are designed as **zero-cost abstractions**, compiling down to
//! primitive integers for maximum performance.
//!
//! # Time
//!
//! The temporal dimension is modeled with two main types:
//!
//! - [`TimePoint<T>`]: Represents a specific, absolute instant in time. It is
//!   typically instantiated as [`TimePoint64`] (wrapping an `i64`).
//! - [`TimeDelta<T>`]: Represents a duration or the difference between two
//!   `TimePoint`s. It is a signed value, typically [`TimeDelta64`] (wrapping an `i64`).
//!
//! The type system enforces correct arithmetic. For example, subtracting two
//! `TimePoint`s yields a `TimeDelta`, and adding a `TimeDelta` to a `TimePoint`
//! yields a new `TimePoint`.
//!
//! # Space
//!
//! The spatial dimension, representing the quay, is modeled with:
//!
//! - [`Segment<T>`]: A discrete, non-negative index representing a location
//!   along the quay. It is an alias for an unsigned integer, typically
//!   [`Segment64`] (`u64`).
//! - [`SegmentInterval<T>`]: A contiguous, half-open `[start, end)` span of
//!   segments, representing a section of the quay.
//!
//! # Example Usage
//!
//! ```
//! use dock_alloc_core::domain::{TimePoint64, TimeDelta64, Segment64, SegmentInterval64, TimeInterval};
//! use dock_alloc_core::primitives::Interval;
//!
//! // A vessel is scheduled to arrive at time 100 and stay for 50 time units.
//! let arrival_time = TimePoint64::new(100);
//! let handling_duration = TimeDelta64::new(50);
//! let departure_time = arrival_time + handling_duration;
//!
//! let time_window: TimeInterval<i64> = Interval::new(arrival_time, departure_time);
//!
//! // It will occupy segments 5 through 9 (a length of 5 segments).
//! let berth_span: SegmentInterval64 = Interval::new(5 as Segment64, 10 as Segment64);
//!
//! println!(
//!     "Vessel berthed at segments [{}, {}) from time {} to {}.",
//!     berth_span.start(),
//!     berth_span.end(),
//!     time_window.start().value(),
//!     time_window.end().value()
//! );
//! ```

#[allow(dead_code)]
use crate::primitives::Interval;
use num_traits::{PrimInt, Signed, Unsigned};
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

/// Represents a **discrete, non-negative index** on a spatial axis.
///
/// A `Segment<T>` is the integer **position** (grid cell index) along an axis.
/// It is intentionally just an alias to an unsigned integer so it compiles down
/// to a plain integer with **zero overhead** and integrates seamlessly with
/// standard Rust indexing, ranges, and bitsets (which all use `usize`).
///
/// # Examples
/// ```
/// use dock_alloc_core::domain::Segment;
///
/// let s0: Segment<usize> = 5;
/// let s1: Segment<usize> = 12;
/// // You will typically use `s0..s1` to denote a span on the quay.
/// assert!(s0 < s1);
/// ```
#[allow(type_alias_bounds)]
pub type Segment<T: PrimInt + Unsigned> = T;

/// A half-open **spatial interval** `[start, end)` over quay segments.
///
/// `SegmentInterval<T>` represents a **contiguous span of segments** on
/// an axis. It is backed by the generic [`Interval`] type but specialized
/// to use [`Segment<T>`] as endpoints. The interval is **half-open**:
/// it includes `start` and excludes `end`, so its length is `end - start`
/// (and it is **empty** when `start == end`).
///
/// # Examples
///
/// ```
/// use dock_alloc_core::domain::{Segment, SegmentInterval};
/// use dock_alloc_core::primitives::Interval;
///
/// let a: Segment<u32> = 5;
/// let b: Segment<u32> = 12;
/// let span: SegmentInterval<u32> = Interval::new(a, b); // [5,12)
///
/// assert_eq!(span.start(), 5);
/// assert_eq!(span.end(), 12);
/// // Convert to a standard Rust range when needed:
/// let as_range = span.start()..span.end();
/// assert_eq!(as_range, 5..12);
///
/// // Empty span:
/// let empty: SegmentInterval<u32> = Interval::new(7, 7);
/// assert!(empty.start() == empty.end());
/// ```
#[allow(type_alias_bounds)]
pub type SegmentInterval<T: PrimInt + Unsigned> = Interval<Segment<T>>;

pub type TimePoint64 = TimePoint<i64>;
pub type TimeDelta64 = TimeDelta<i64>;

pub type Segment64 = Segment<u64>;
pub type SegmentInterval64 = SegmentInterval<u64>;

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
}
