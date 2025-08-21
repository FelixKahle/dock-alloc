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
use num_traits::{PrimInt, Signed, Zero};
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

    /// Creates a half-open interval `[self, self + len)`.
    ///
    /// Returns `None` if `len` is negative. Zero-length is allowed.
    /// If addition would overflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{TimePoint, TimeDelta, TimeInterval};
    ///
    /// let tp = TimePoint::new(10);
    /// let len = TimeDelta::new(5);
    /// let interval = tp.span_of(len).unwrap();
    /// assert_eq!(interval.start().value(), 10);
    /// assert_eq!(interval.end().value(), 15);
    /// assert!(tp.span_of(TimeDelta::new(-1)).is_none());
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
    /// This method will panic if a underflow occurs during the operation.
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
    /// This method will panic if a underflow occurs during the operation.
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
    /// This method will panic if a underflow occurs during the operation.
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
    /// This method will panic if a underflow occurs during the operation.
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
    /// This method will panic if a underflow occurs during the operation.
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

/// Represents a segment index along the quay.
///
/// A `QuayPosition` is a wrapper around a primitive unsigned integer type
/// that represents a specific segment along the quay.
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

/// Represents a segment index along the quay with a length.
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
    /// Creates a new `QuayPosition` instance wrapping the provided value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayPosition;
    ///
    /// let seg_idx = QuayPosition::new(5);
    /// assert_eq!(seg_idx.value(), 5);
    /// ```
    #[inline]
    pub const fn new(v: usize) -> Self {
        QuayPosition(v)
    }

    /// Creates a new `QuayPosition` with a value of zero.
    ///
    /// Creates a new `QuayPosition` instance with a value of zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayPosition;
    ///
    /// let seg_idx = QuayPosition::zero();
    /// assert_eq!(seg_idx.value(), 0);
    /// ```
    #[inline]
    pub const fn zero() -> Self {
        QuayPosition::new(0)
    }

    /// Returns the value of the `QuayPosition`.
    ///
    /// Returns the inner value of the `QuayPosition` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayPosition;
    ///
    /// let seg_idx = QuayPosition::new(5);
    /// assert_eq!(seg_idx.value(), 5);
    /// ```
    #[inline]
    pub const fn value(self) -> usize {
        self.0
    }

    /// Checks if the `QuayPosition` is zero.
    ///
    /// Returns `true` if the inner value is zero, otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayPosition;
    ///
    /// let seg_idx = QuayPosition::new(0);
    /// assert!(seg_idx.is_zero());
    /// let non_zero_seg_idx = QuayPosition::new(5);
    /// assert!(!non_zero_seg_idx.is_zero());
    /// ```
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Adds a `QuayLength` to the `QuayPosition`, returning a new `QuayPosition`.
    ///
    /// Adds a `QuayLength` to the current `QuayPosition`, returning a new `QuayPosition`.
    /// If the addition would overflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let seg_idx = QuayPosition::new(5);
    /// let length = QuayLength::new(3);
    /// let new_seg_idx = seg_idx.checked_add_len(length);
    /// assert_eq!(new_seg_idx.unwrap().value(), 8);
    /// ```
    #[inline]
    pub fn checked_add_len(self, d: QuayLength) -> Option<Self> {
        self.0.checked_add(d.0).map(QuayPosition)
    }

    /// Subtracts a `QuayLength` from the `QuayPosition`, returning a new `QuayPosition`.
    ///
    /// Subtracts a `QuayLength` from the current `QuayPosition`,
    /// returning a new `QuayPosition`.
    /// If the subtraction would underflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let seg_idx = QuayPosition::new(5);
    /// let length = QuayLength::new(3);
    /// let new_seg_idx = seg_idx.checked_sub_len(length);
    /// assert_eq!(new_seg_idx.unwrap().value(), 2);
    /// ```
    #[inline]
    pub fn checked_sub_len(self, d: QuayLength) -> Option<Self> {
        self.0.checked_sub(d.0).map(QuayPosition)
    }

    /// Adds a `QuayLength` to the `QuayPosition`, returning a new `QuayPosition`.
    ///
    /// Adds a `QuayLength` to the current `QuayPosition`, returning a new `QuayPosition`.
    /// If the addition would overflow, it returns a `QuayPosition` with the maximum value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let seg_idx = QuayPosition::new(5);
    /// let length = QuayLength::new(3);
    /// let new_seg_idx = seg_idx.saturating_add_len(length);
    /// assert_eq!(new_seg_idx.value(), 8);
    /// ```
    #[inline]
    pub fn saturating_add_len(self, d: QuayLength) -> Self {
        QuayPosition(self.0.saturating_add(d.0))
    }

    /// Subtracts a `QuayLength` from the `QuayPosition`, returning a new `QuayPosition`.
    ///
    /// Subtracts a `QuayLength` from the current `QuayPosition`, returning a new `QuayPosition`.
    /// If the subtraction would underflow, it returns a `QuayPosition` with a value of zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayLength};
    ///
    /// let seg_idx = QuayPosition::new(5);
    /// let length = QuayLength::new(3);
    /// let new_seg_idx = seg_idx.saturating_sub_len(length);
    /// assert_eq!(new_seg_idx.value(), 2);
    /// ```
    #[inline]
    pub fn saturating_sub_len(self, d: QuayLength) -> Self {
        QuayPosition(self.0.saturating_sub(d.0))
    }

    /// Creates a `QuayInterval` starting from the current `QuayPosition` with the specified length.
    ///
    /// Creates a `QuayInterval` that represents a half-open interval starting from the current `QuayPosition`
    /// and extending by the specified `QuayLength`.
    /// If addition of the length would overflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{QuayPosition, QuayInterval, QuayLength}; // Add QuayLength here
    ///
    /// let start = QuayPosition::new(5);
    /// let length = QuayLength::new(10);
    /// let span = start.span_of(length);
    /// assert_eq!(span.unwrap().start().value(), 5);
    /// assert_eq!(span.unwrap().end().value(), 15);
    /// ```
    #[inline]
    pub fn span_of(self, len: QuayLength) -> Option<QuayInterval> {
        self.checked_add_len(len)
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

/// Represents the length of a segment along the quay.
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
pub struct QuayLength(pub usize);

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
    /// Creates a new `QuayLength` instance wrapping the provided value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length = QuayLength::new(10);
    /// assert_eq!(seg_length.value(), 10);
    /// ```
    #[inline]
    pub const fn new(v: usize) -> Self {
        QuayLength(v)
    }

    /// Returns the value of the `QuayLength`.
    ///
    /// Returns the inner value of the `QuayLength` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length = QuayLength::new(10);
    /// assert_eq!(seg_length.value(), 10);
    /// ```
    #[inline]
    pub const fn value(self) -> usize {
        self.0
    }

    /// Adds another `QuayLength` to the current `QuayLength`, returning a new `QuayLength`.
    ///
    /// Adds another `QuayLength` to the current instance,
    /// returning a new `QuayLength` with the updated value.
    /// If the addition would overflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length1 = QuayLength::new(10);
    /// let seg_length2 = QuayLength::new(5);
    /// let new_seg_length = seg_length1.checked_add(seg_length2);
    /// assert_eq!(new_seg_length.unwrap().value(), 15);
    /// ```
    #[inline]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).map(QuayLength)
    }

    /// Subtracts another `QuayLength` from the current `QuayLength`, returning a new `QuayLength`.
    ///
    /// Subtracts another `QuayLength` from the current instance,
    /// returning a new `QuayLength` with the updated value.
    /// If the subtraction would underflow, it returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length1 = QuayLength::new(10);
    /// let seg_length2 = QuayLength::new(5);
    /// let new_seg_length = seg_length1.checked_sub(seg_length2);
    /// assert_eq!(new_seg_length.unwrap().value(), 5);
    /// ```
    #[inline]
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).map(QuayLength)
    }

    /// Adds another `QuayLength` to the current `QuayLength`, returning a new `QuayLength`.
    ///
    /// Adds another `QuayLength` to the current instance,
    /// returning a new `QuayLength` with the updated value.
    /// If the addition would overflow, it returns a `QuayLength` with the maximum value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length1 = QuayLength::new(10);
    /// let seg_length2 = QuayLength::new(5);
    /// let new_seg_length = seg_length1.saturating_add(seg_length2);
    /// assert_eq!(new_seg_length.value(), 15);
    /// ```
    #[inline]
    pub fn saturating_add(self, rhs: Self) -> Self {
        QuayLength(self.0.saturating_add(rhs.0))
    }

    /// Subtracts another `QuayLength` from the current `QuayLength`, returning a new `QuayLength`.
    ///
    /// Subtracts another `QuayLength` from the current instance,
    /// returning a new `QuayLength` with the updated value.
    /// If the subtraction would underflow, it returns a `QuayLength` with a value of zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length1 = QuayLength::new(10);
    /// let seg_length2 = QuayLength::new(5);
    /// let new_seg_length = seg_length1.saturating_sub(seg_length2);
    /// assert_eq!(new_seg_length.value(), 5);
    /// ```
    #[inline]
    pub fn saturating_sub(self, rhs: Self) -> Self {
        QuayLength(self.0.saturating_sub(rhs.0))
    }

    /// Creates a new `QuayLength` with a value of zero.
    ///
    /// Creates a new `QuayLength` instance with a value of zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length = QuayLength::zero();
    /// assert_eq!(seg_length.value(), 0);
    /// ```
    #[inline]
    pub const fn zero() -> Self {
        Self(0)
    }

    /// Returns the absolute value of the `QuayLength`.
    ///
    /// Since `QuayLength` is always non-negative,
    /// this method simply returns the current instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length = QuayLength::new(10);
    /// assert_eq!(seg_length.abs().value(), 10);
    /// ```
    #[inline(always)]
    pub const fn abs(self) -> Self {
        self
    }

    /// Checks if the `QuayLength` is zero.
    ///
    /// Returns `true` if the inner value is zero, otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length = QuayLength::new(0);
    /// assert!(seg_length.is_zero());
    /// let non_zero_seg_length = QuayLength::new(10);
    /// assert!(!non_zero_seg_length.is_zero());
    /// ```
    #[inline(always)]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Checks if the `QuayLength` is positive.
    ///
    /// Returns `true` if the inner value is greater than zero, otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::QuayLength;
    ///
    /// let seg_length = QuayLength::new(10);
    /// assert!(seg_length.is_positive());
    /// let zero_seg_length = QuayLength::new(0);
    /// assert!(!zero_seg_length.is_positive());
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
            .expect("overflow in SegLen += SegLen");
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
            .expect("underflow in SegLen -= SegLen");
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
    fn test_quay_position_checked_add_len() {
        let seg_idx = QuayPosition::new(usize::MAX - 1);
        let length = QuayLength::new(1);
        assert_eq!(
            seg_idx.checked_add_len(length),
            Some(QuayPosition::new(usize::MAX))
        );
        let length_overflow = QuayLength::new(2);
        assert_eq!(seg_idx.checked_add_len(length_overflow), None);
    }

    #[test]
    fn test_quay_position_checked_sub_len() {
        let seg_idx = QuayPosition::new(1);
        let length = QuayLength::new(1);
        assert_eq!(seg_idx.checked_sub_len(length), Some(QuayPosition::new(0)));
        let length_underflow = QuayLength::new(2);
        assert_eq!(seg_idx.checked_sub_len(length_underflow), None);
    }

    #[test]
    fn test_quay_position_saturating_add_len() {
        let seg_idx = QuayPosition::new(usize::MAX - 1);
        let length = QuayLength::new(5);
        assert_eq!(
            seg_idx.saturating_add_len(length),
            QuayPosition::new(usize::MAX)
        );
    }

    #[test]
    fn test_quay_position_saturating_sub_len() {
        let seg_idx = QuayPosition::new(5);
        let length = QuayLength::new(10);
        assert_eq!(seg_idx.saturating_sub_len(length), QuayPosition::new(0));
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
}
