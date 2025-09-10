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

use std::{
    fmt::Display,
    iter::Sum,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
};

use num_traits::{
    CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, SaturatingAdd, SaturatingMul, SaturatingSub,
    Zero,
};

#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Cost<T>(T);

impl<T: Copy> Cost<T> {
    #[inline]
    pub const fn new(value: T) -> Self {
        Cost(value)
    }

    #[inline]
    pub const fn value(self) -> T {
        self.0
    }

    #[inline]
    pub fn checked_add(self, other: Cost<T>) -> Option<Self>
    where
        T: CheckedAdd<Output = T> + Copy,
    {
        self.0.checked_add(&other.0).map(Cost)
    }

    #[inline]
    pub fn checked_sub(self, other: Cost<T>) -> Option<Self>
    where
        T: CheckedSub<Output = T> + Copy,
    {
        self.0.checked_sub(&other.0).map(Cost)
    }

    #[inline]
    pub fn saturating_add(self, other: Cost<T>) -> Self
    where
        T: SaturatingAdd<Output = T> + Copy,
    {
        Cost(self.0.saturating_add(&other.0))
    }

    #[inline]
    pub fn saturating_sub(self, other: Cost<T>) -> Self
    where
        T: SaturatingSub<Output = T> + Copy,
    {
        Cost(self.0.saturating_sub(&other.0))
    }

    pub fn saturating_mul(self, factor: T) -> Self
    where
        T: SaturatingMul<Output = T> + Copy,
    {
        Cost(self.0.saturating_mul(&factor))
    }

    pub fn ratio<D>(self, divisor: Cost<T>) -> Option<D>
    where
        T: Copy + Zero + Into<D>,
        D: Copy + std::ops::Div<Output = D>,
    {
        if divisor.0.is_zero() {
            None
        } else {
            let dividend: D = self.0.into();
            let divisor_val: D = divisor.0.into();
            Some(dividend / divisor_val)
        }
    }
}

impl<T: Copy + Display> Display for Cost<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Cost({})", self.0)
    }
}

impl<T> Add for Cost<T>
where
    T: Copy + CheckedAdd<Output = T>,
{
    type Output = Cost<T>;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Cost(self.0.checked_add(&rhs.0).expect("overflow in Cost + Cost"))
    }
}

impl<T> AddAssign for Cost<T>
where
    T: Copy + CheckedAdd<Output = T>,
{
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_add(&rhs.0)
            .expect("overflow in Cost += Cost");
    }
}

impl<T: Copy + CheckedAdd<Output = T>> CheckedAdd for Cost<T> {
    #[inline]
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_add(&rhs.0).map(Cost)
    }
}

impl<T> SaturatingAdd for Cost<T>
where
    T: Copy + CheckedAdd + SaturatingAdd<Output = T>,
{
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
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = self
            .0
            .checked_sub(&rhs.0)
            .expect("underflow in Cost -= Cost");
    }
}

impl<T: Copy + CheckedSub<Output = T>> CheckedSub for Cost<T> {
    #[inline]
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        self.0.checked_sub(&rhs.0).map(Cost)
    }
}

impl<T> SaturatingSub for Cost<T>
where
    T: Copy + CheckedSub<Output = T> + SaturatingSub<Output = T>,
{
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

    #[inline]
    fn mul(self, rhs: T) -> Self::Output {
        Cost(self.0.checked_mul(&rhs).expect("overflow in Cost * scalar"))
    }
}

impl<T> MulAssign<T> for Cost<T>
where
    T: Copy + CheckedMul<Output = T>,
{
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
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Cost::new(T::zero()), |a, b| a + b)
    }
}

impl<'a, T> Sum<&'a Cost<T>> for Cost<T>
where
    T: Copy + CheckedAdd<Output = T> + Zero,
{
    #[inline]
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Cost::new(T::zero()), |a, b| a + *b)
    }
}

impl<T: Copy + Zero + CheckedAdd> Zero for Cost<T> {
    fn zero() -> Self {
        Cost(T::zero())
    }

    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
