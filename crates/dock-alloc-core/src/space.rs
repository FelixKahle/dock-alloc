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

use crate::primitives::Interval;
use num_traits::{CheckedAdd, CheckedSub, SaturatingAdd, SaturatingSub, Zero};
use std::{
    iter::Sum,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
};

#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct SpacePosition(usize);

pub type SpaceInterval = Interval<SpacePosition>;

impl std::fmt::Display for SpacePosition {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SpacePosition({})", self.0)
    }
}

impl From<usize> for SpacePosition {
    #[inline]
    fn from(v: usize) -> Self {
        SpacePosition(v)
    }
}

impl SpacePosition {
    #[inline]
    pub const fn new(v: usize) -> Self {
        SpacePosition(v)
    }

    #[inline]
    pub const fn zero() -> Self {
        SpacePosition(0)
    }

    #[inline]
    pub const fn value(self) -> usize {
        self.0
    }

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    #[inline]
    pub fn checked_add(self, len: SpaceLength) -> Option<Self> {
        self.0.checked_add(len.0).map(SpacePosition)
    }

    #[inline]
    pub fn checked_sub(self, len: SpaceLength) -> Option<Self> {
        self.0.checked_sub(len.0).map(SpacePosition)
    }

    #[inline]
    pub fn saturating_add(self, len: SpaceLength) -> Self {
        SpacePosition(self.0.saturating_add(len.0))
    }

    #[inline]
    pub fn saturating_sub(self, len: SpaceLength) -> Self {
        SpacePosition(self.0.saturating_sub(len.0))
    }

    #[inline]
    pub fn span_of(self, len: SpaceLength) -> Option<SpaceInterval> {
        self.checked_add(len)
            .map(|end| SpaceInterval::new(self, end))
    }
}

impl Add<SpaceLength> for SpacePosition {
    type Output = SpacePosition;

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

    #[inline]
    fn add(self, rhs: SpacePosition) -> Self::Output {
        rhs + self
    }
}

impl Sub<SpaceLength> for SpacePosition {
    type Output = SpacePosition;

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

    #[inline]
    fn sub(self, rhs: SpacePosition) -> Self::Output {
        SpaceLength::new(self.value().abs_diff(rhs.value()))
    }
}

impl AddAssign<SpaceLength> for SpacePosition {
    #[inline]
    fn add_assign(&mut self, rhs: SpaceLength) {
        self.0 = self
            .0
            .checked_add(rhs.0)
            .expect("overflow in SpacePosition += SpaceLength");
    }
}

impl SubAssign<SpaceLength> for SpacePosition {
    #[inline]
    fn sub_assign(&mut self, rhs: SpaceLength) {
        self.0 = self
            .0
            .checked_sub(rhs.0)
            .expect("underflow in SpacePosition -= SpaceLength");
    }
}

#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct SpaceLength(usize);

impl std::fmt::Display for SpaceLength {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SpaceLength({})", self.0)
    }
}

impl From<usize> for SpaceLength {
    #[inline]
    fn from(v: usize) -> Self {
        SpaceLength(v)
    }
}

impl SpaceLength {
    #[inline]
    pub const fn new(v: usize) -> Self {
        SpaceLength(v)
    }

    #[inline]
    pub const fn value(self) -> usize {
        self.0
    }

    #[inline]
    pub fn clamp(self, min: Self, max: Self) -> Self {
        assert!(min <= max, "min must be <= max");
        SpaceLength(self.0.clamp(min.0, max.0))
    }

    #[inline]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).map(SpaceLength)
    }

    #[inline]
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).map(SpaceLength)
    }

    #[inline]
    pub fn saturating_add(self, rhs: Self) -> Self {
        SpaceLength(self.0.saturating_add(rhs.0))
    }

    #[inline]
    pub fn saturating_sub(self, rhs: Self) -> Self {
        SpaceLength(self.0.saturating_sub(rhs.0))
    }

    #[inline]
    pub fn checked_mul(self, rhs: usize) -> Option<Self> {
        self.0.checked_mul(rhs).map(SpaceLength)
    }

    #[inline]
    pub fn checked_div(self, rhs: usize) -> Option<Self> {
        self.0.checked_div(rhs).map(SpaceLength)
    }

    #[inline]
    pub fn saturating_mul(self, rhs: usize) -> Self {
        Self(self.0.saturating_mul(rhs))
    }

    #[inline]
    pub const fn zero() -> Self {
        Self(0)
    }

    #[inline]
    pub const fn abs(self) -> Self {
        self
    }

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    #[inline]
    pub const fn is_positive(self) -> bool {
        self.0 != 0
    }
}

impl Zero for SpaceLength {
    #[inline]
    fn zero() -> Self {
        SpaceLength::new(0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl Add for SpaceLength {
    type Output = SpaceLength;

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
    #[inline]
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_add(rhs.0).map(SpaceLength)
    }
}

impl SaturatingAdd for SpaceLength {
    #[inline]
    fn saturating_add(&self, rhs: &Self) -> Self {
        SpaceLength(self.0.saturating_add(rhs.0))
    }
}

impl Sub for SpaceLength {
    type Output = SpaceLength;

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
    #[inline]
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).map(SpaceLength)
    }
}

impl SaturatingSub for SpaceLength {
    #[inline]
    fn saturating_sub(&self, rhs: &Self) -> Self {
        SpaceLength(self.0.saturating_sub(rhs.0))
    }
}

impl AddAssign for SpaceLength {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_add(rhs.0)
            .expect("overflow in SpaceLength += SpaceLength");
    }
}

impl SubAssign for SpaceLength {
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
    #[inline]
    fn div_assign(&mut self, rhs: usize) {
        self.0 = self
            .0
            .checked_div(rhs)
            .expect("division by zero in SpaceLength /= scalar");
    }
}

impl Sum for SpaceLength {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + x)
    }
}

impl<'a> Sum<&'a SpaceLength> for SpaceLength {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), |acc, x| acc + *x)
    }
}

impl Interval<SpacePosition> {
    #[inline]
    pub fn extent(&self) -> SpaceLength {
        self.end() - self.start()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
