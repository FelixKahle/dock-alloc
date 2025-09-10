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
    CheckedAdd, CheckedSub, PrimInt, SaturatingAdd, SaturatingMul, SaturatingSub, Signed, Zero,
};
use std::{
    fmt::Display,
    iter::Sum,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TimePoint<T: PrimInt>(T);

impl<T: PrimInt> Default for TimePoint<T> {
    #[inline]
    fn default() -> Self {
        TimePoint(T::zero())
    }
}

impl<T: PrimInt + Display> Display for TimePoint<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TimePoint({})", self.value())
    }
}

impl<T: PrimInt> From<T> for TimePoint<T> {
    #[inline]
    fn from(v: T) -> Self {
        TimePoint(v)
    }
}

pub type TimeInterval<T> = Interval<TimePoint<T>>;

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TimeDelta<T: PrimInt + Signed>(T);

impl<T: PrimInt + Signed> TimeDelta<T> {
    #[inline]
    pub const fn new(value: T) -> Self {
        Self(value)
    }

    #[inline]
    pub fn zero() -> Self {
        Self(T::zero())
    }

    #[inline]
    pub const fn value(self) -> T {
        self.0
    }

    #[inline]
    pub fn abs(self) -> Self {
        Self(self.0.abs())
    }

    #[inline]
    pub fn is_negative(self) -> bool {
        self.0.is_negative()
    }

    #[inline]
    pub fn is_positive(self) -> bool {
        self.0.is_positive()
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        self.0.is_zero()
    }

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

    #[inline]
    pub fn checked_add(self, rhs: TimeDelta<T>) -> Option<Self> {
        self.0.checked_add(&rhs.0).map(TimeDelta)
    }

    #[inline]
    pub fn checked_sub(self, rhs: TimeDelta<T>) -> Option<Self> {
        self.0.checked_sub(&rhs.0).map(TimeDelta)
    }

    #[inline]
    pub fn saturating_add(self, rhs: TimeDelta<T>) -> Self {
        TimeDelta(self.0.saturating_add(rhs.0))
    }

    #[inline]
    pub fn saturating_sub(self, rhs: TimeDelta<T>) -> Self {
        TimeDelta(self.0.saturating_sub(rhs.0))
    }

    #[inline]
    pub fn checked_mul(self, rhs: T) -> Option<Self> {
        self.0.checked_mul(&rhs).map(TimeDelta)
    }

    #[inline]
    pub fn saturating_mul(self, rhs: T) -> Self
    where
        T: SaturatingMul,
    {
        TimeDelta(self.0.saturating_mul(&rhs))
    }

    #[inline]
    pub fn checked_div(self, rhs: T) -> Option<Self> {
        self.0.checked_div(&rhs).map(TimeDelta)
    }
}

impl<T: PrimInt> TimePoint<T> {
    #[inline]
    pub const fn new(value: T) -> Self {
        TimePoint(value)
    }

    #[inline]
    pub fn zero() -> Self {
        TimePoint::new(T::zero())
    }

    #[inline]
    pub const fn value(self) -> T {
        self.0
    }
}

impl<T: PrimInt + Signed> TimePoint<T> {
    #[inline]
    pub fn checked_add(self, delta: TimeDelta<T>) -> Option<Self> {
        self.0.checked_add(&delta.0).map(TimePoint)
    }

    #[inline]
    pub fn checked_sub(self, delta: TimeDelta<T>) -> Option<Self> {
        self.0.checked_sub(&delta.0).map(TimePoint)
    }

    #[inline]
    pub fn saturating_add(self, delta: TimeDelta<T>) -> Self {
        TimePoint(self.0.saturating_add(delta.0))
    }

    #[inline]
    pub fn saturating_sub(self, delta: TimeDelta<T>) -> Self {
        TimePoint(self.0.saturating_sub(delta.0))
    }

    #[inline]
    pub fn span_of(self, len: TimeDelta<T>) -> Option<TimeInterval<T>> {
        if len.is_negative() {
            return None;
        }
        self.checked_add(len).map(|end| Interval::new(self, end))
    }
}

impl<T: PrimInt + Display + Signed> Display for TimeDelta<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TimeDelta({})", self.0)
    }
}

impl<T: PrimInt + Signed> Add<TimeDelta<T>> for TimePoint<T> {
    type Output = TimePoint<T>;

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
    fn add_assign(&mut self, rhs: TimeDelta<T>) {
        self.0 = self
            .0
            .checked_add(&rhs.0)
            .expect("overflow in TimePoint += TimeDelta");
    }
}

impl<T: PrimInt + Signed> Sub<TimeDelta<T>> for TimePoint<T> {
    type Output = TimePoint<T>;

    fn sub(self, rhs: TimeDelta<T>) -> Self::Output {
        TimePoint(
            self.0
                .checked_sub(&rhs.0)
                .expect("underflow in TimePoint - TimeDelta"),
        )
    }
}
impl<T: PrimInt + Signed> SubAssign<TimeDelta<T>> for TimePoint<T> {
    fn sub_assign(&mut self, rhs: TimeDelta<T>) {
        self.0 = self
            .0
            .checked_sub(&rhs.0)
            .expect("underflow in TimePoint -= TimeDelta");
    }
}

impl<T: PrimInt + Signed> Sub<TimePoint<T>> for TimePoint<T> {
    type Output = TimeDelta<T>;

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

    fn add(self, rhs: Self) -> Self::Output {
        TimeDelta::new(
            self.0
                .checked_add(&rhs.0)
                .expect("overflow in TimeDelta + TimeDelta"),
        )
    }
}

impl<T: PrimInt + Signed> CheckedAdd for TimeDelta<T> {
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_add(&rhs.0).map(TimeDelta)
    }
}

impl<T: PrimInt + Signed> SaturatingAdd for TimeDelta<T> {
    fn saturating_add(&self, rhs: &Self) -> Self {
        TimeDelta(self.0.saturating_add(rhs.0))
    }
}

impl<T: PrimInt + Signed> Sub for TimeDelta<T> {
    type Output = TimeDelta<T>;

    fn sub(self, rhs: Self) -> Self::Output {
        TimeDelta(
            self.0
                .checked_sub(&rhs.0)
                .expect("underflow in TimeDelta - TimeDelta"),
        )
    }
}

impl<T: PrimInt + Signed> CheckedSub for TimeDelta<T> {
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_sub(&rhs.0).map(TimeDelta)
    }
}

impl<T: PrimInt + Signed> SaturatingSub for TimeDelta<T> {
    fn saturating_sub(&self, rhs: &Self) -> Self {
        TimeDelta(self.0.saturating_sub(rhs.0))
    }
}

impl<T: PrimInt + Signed> AddAssign for TimeDelta<T> {
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_add(&rhs.0)
            .expect("overflow in TimeDelta += TimeDelta");
    }
}

impl<T: PrimInt + Signed> SubAssign for TimeDelta<T> {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_sub(&rhs.0)
            .expect("underflow in TimeDelta -= TimeDelta");
    }
}

impl<T: PrimInt + Signed> Neg for TimeDelta<T> {
    type Output = TimeDelta<T>;

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

    fn mul(self, rhs: T) -> Self::Output {
        TimeDelta::new(
            self.0
                .checked_mul(&rhs)
                .expect("overflow in TimeDelta * scalar"),
        )
    }
}

impl<T: PrimInt + Signed> MulAssign<T> for TimeDelta<T> {
    fn mul_assign(&mut self, rhs: T) {
        self.0 = self
            .0
            .checked_mul(&rhs)
            .expect("overflow in TimeDelta *= scalar");
    }
}

impl<T: PrimInt + Signed> Div<T> for TimeDelta<T> {
    type Output = TimeDelta<T>;

    fn div(self, rhs: T) -> Self::Output {
        TimeDelta::new(
            self.0
                .checked_div(&rhs)
                .expect("div-by-zero or overflow in TimeDelta / scalar"),
        )
    }
}

impl<T: PrimInt + Signed> DivAssign<T> for TimeDelta<T> {
    fn div_assign(&mut self, rhs: T) {
        self.0 = self
            .0
            .checked_div(&rhs)
            .expect("div-by-zero or overflow in TimeDelta /= scalar");
    }
}

impl<T: PrimInt + Signed> Zero for TimeDelta<T> {
    #[inline]
    fn zero() -> Self {
        TimeDelta(T::zero())
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<T: PrimInt + Signed> From<T> for TimeDelta<T> {
    #[inline]
    fn from(v: T) -> Self {
        TimeDelta(v)
    }
}

impl<T: PrimInt + Signed> Default for TimeDelta<T> {
    #[inline]
    fn default() -> Self {
        TimeDelta::zero()
    }
}

impl<T: PrimInt + Signed> Sum for TimeDelta<T> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + x)
    }
}

impl<'a, T: PrimInt + Signed> Sum<&'a TimeDelta<T>> for TimeDelta<T> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + *x)
    }
}

impl<T: PrimInt + Signed> Interval<TimePoint<T>> {
    #[inline]
    pub fn duration(&self) -> TimeDelta<T> {
        self.end() - self.start()
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
}
