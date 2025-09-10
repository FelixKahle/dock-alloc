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

use crate::domain::SpaceTimeRectangle;
use dock_alloc_core::{space::SpaceInterval, time::TimePoint};
use num_traits::{PrimInt, Signed};
use std::fmt::Display;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FreeSlot<T>
where
    T: PrimInt + Signed,
{
    start_time: TimePoint<T>,
    space: SpaceInterval,
}

impl<T> FreeSlot<T>
where
    T: PrimInt + Signed,
{
    #[inline]
    pub(crate) fn new(space: SpaceInterval, start_time: TimePoint<T>) -> Self {
        Self { start_time, space }
    }

    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }

    #[inline]
    pub fn space(&self) -> SpaceInterval {
        self.space
    }
}

impl<T> Display for FreeSlot<T>
where
    T: PrimInt + Signed + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FreeSlot({}, {})", self.space, self.start_time)
    }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FreeRegion<T>(SpaceTimeRectangle<T>)
where
    T: PrimInt + Signed;

impl<T> FreeRegion<T>
where
    T: PrimInt + Signed,
{
    #[inline]
    pub fn new(rect: SpaceTimeRectangle<T>) -> Self {
        Self(rect)
    }

    #[inline]
    pub fn rectangle(&self) -> &SpaceTimeRectangle<T> {
        &self.0
    }
}

impl<T> Display for FreeRegion<T>
where
    T: PrimInt + Signed + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FreeRegion({})", self.0)
    }
}

impl<T> From<SpaceTimeRectangle<T>> for FreeRegion<T>
where
    T: PrimInt + Signed,
{
    fn from(rect: SpaceTimeRectangle<T>) -> Self {
        Self::new(rect)
    }
}
