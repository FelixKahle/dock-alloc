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

use dock_alloc_core::{space::SpaceInterval, time::TimeInterval};
use num_traits::{PrimInt, Signed};
use std::fmt::Display;

/// A version number used to track iterations or generations in optimization algorithms.
///
/// `Version` represents a monotonically increasing counter that can be used to track
/// the evolution of solutions, algorithm iterations, or other versioned entities
/// in the dock allocation solver. It provides a type-safe wrapper around a `u64`
/// counter with convenient methods for incrementing and accessing the underlying value.
///
/// # Examples
///
/// ```
/// use dock_alloc_solver::domain::Version;
///
/// let v1 = Version::default();
/// assert_eq!(v1.value(), 0);
///
/// let v2 = v1.next();
/// assert_eq!(v2.value(), 1);
///
/// let v3 = v2.next();
/// assert_eq!(v3.value(), 2);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Version(u64);

impl Version {
    pub fn new(value: u64) -> Self {
        Version(value)
    }
    /// Returns the next version by incrementing the current version number.
    ///
    /// This method creates a new `Version` instance with a value that is one
    /// greater than the current version. The original version is not modified
    /// since `Version` is `Copy`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::domain::Version;
    ///
    /// let v1 = Version::default(); // v0
    /// let v2 = v1.next();          // v1
    /// let v3 = v2.next();          // v2
    ///
    /// assert_eq!(v1.value(), 0);
    /// assert_eq!(v2.value(), 1);
    /// assert_eq!(v3.value(), 2);
    /// ```
    #[inline]
    pub fn next(self) -> Self {
        Version(self.0 + 1)
    }

    /// Returns the underlying version number as a `u64`.
    ///
    /// This method provides access to the raw numeric value of the version,
    /// which can be useful for comparisons, logging, or interfacing with
    /// external systems that expect numeric version identifiers.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::domain::Version;
    ///
    /// let version = Version::default().next().next().next();
    /// assert_eq!(version.value(), 3);
    ///
    /// // Useful for logging or debugging
    /// println!("Current version: {}", version.value());
    /// ```
    #[inline]
    pub fn value(self) -> u64 {
        self.0
    }
}

impl Display for Version {
    /// Formats the version for display with a "v" prefix.
    ///
    /// This implementation provides a human-readable representation of the version
    /// in the format "v{number}", which is commonly used in software versioning.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::domain::Version;
    ///
    /// let version = Version::default().next().next();
    /// assert_eq!(format!("{}", version), "v2");
    ///
    /// // Useful for user-facing output
    /// println!("Algorithm iteration: {}", version);
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "v{}", self.0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SpaceTimeRectangle<T: PrimInt + Signed> {
    space: SpaceInterval,
    time: TimeInterval<T>,
}

impl<T: PrimInt + Signed> SpaceTimeRectangle<T> {
    pub fn new(space: SpaceInterval, time: TimeInterval<T>) -> Self {
        Self { space, time }
    }

    pub fn space(&self) -> SpaceInterval {
        self.space
    }

    pub fn time(&self) -> TimeInterval<T> {
        self.time
    }

    pub fn is_empty(&self) -> bool {
        self.space.is_empty() || self.time.is_empty()
    }

    pub fn into_inner(self) -> (SpaceInterval, TimeInterval<T>) {
        (self.space, self.time)
    }

    pub fn intersects(&self, other: &Self) -> bool {
        self.space.intersects(&other.space) && self.time.intersects(&other.time)
    }

    pub fn intersection(&self, other: &Self) -> Option<Self> {
        let space = self.space.intersection(&other.space)?;
        let time = self.time.intersection(&other.time)?;
        Some(Self { space, time })
    }
}

impl<T: PrimInt + Signed + Display> Display for SpaceTimeRectangle<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{} x {}] (space x time)", self.space, self.time)
    }
}

impl<T: PrimInt + Signed> From<(SpaceInterval, TimeInterval<T>)> for SpaceTimeRectangle<T> {
    fn from(value: (SpaceInterval, TimeInterval<T>)) -> Self {
        Self {
            space: value.0,
            time: value.1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dock_alloc_core::{space::SpacePosition, time::TimePoint};

    #[test]
    fn test_space_time_rectangle_creation() {
        // Create using constructor
        let space = SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(20));
        let time = TimeInterval::new(TimePoint::new(100), TimePoint::new(200));
        let rect = SpaceTimeRectangle::new(space.clone(), time.clone());

        assert_eq!(rect.space(), space);
        assert_eq!(rect.time(), time);

        // Create using From trait
        let rect_from_tuple: SpaceTimeRectangle<i32> = (space.clone(), time.clone()).into();
        assert_eq!(rect_from_tuple.space(), space);
        assert_eq!(rect_from_tuple.time(), time);
    }

    #[test]
    fn test_space_time_rectangle_accessors() {
        let space = SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(20));
        let time = TimeInterval::new(TimePoint::new(100), TimePoint::new(200));
        let rect = SpaceTimeRectangle::new(space.clone(), time.clone());

        // Test accessors
        let space_ref = rect.space();
        assert_eq!(space_ref.start().value(), 10);
        assert_eq!(space_ref.end().value(), 20);

        let time_ref = rect.time();
        assert_eq!(time_ref.start().value(), 100);
        assert_eq!(time_ref.end().value(), 200);
    }

    #[test]
    fn test_space_time_rectangle_into_inner() {
        let space = SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(20));
        let time = TimeInterval::new(TimePoint::new(100), TimePoint::new(200));
        let rect = SpaceTimeRectangle::new(space.clone(), time.clone());

        // Test into_inner method
        let (returned_space, returned_time) = rect.into_inner();
        assert_eq!(returned_space, space);
        assert_eq!(returned_time, time);
    }

    #[test]
    fn test_space_time_rectangle_intersects() {
        // Setup rectangles that intersect in both dimensions
        let rect1 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(30)),
            TimeInterval::new(TimePoint::new(100), TimePoint::new(300)),
        );
        let rect2 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(20), SpacePosition::new(40)),
            TimeInterval::new(TimePoint::new(200), TimePoint::new(400)),
        );
        assert!(rect1.intersects(&rect2));

        // Setup rectangles that don't intersect in space dimension
        let rect3 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(20)),
            TimeInterval::new(TimePoint::new(100), TimePoint::new(300)),
        );
        let rect4 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(30), SpacePosition::new(40)),
            TimeInterval::new(TimePoint::new(200), TimePoint::new(400)),
        );
        assert!(!rect3.intersects(&rect4));

        // Setup rectangles that don't intersect in time dimension
        let rect5 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(30)),
            TimeInterval::new(TimePoint::new(100), TimePoint::new(200)),
        );
        let rect6 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(20), SpacePosition::new(40)),
            TimeInterval::new(TimePoint::new(300), TimePoint::new(400)),
        );
        assert!(!rect5.intersects(&rect6));

        // Test with rectangles that touch at edges (should not intersect due to half-open intervals)
        let rect7 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(20)),
            TimeInterval::new(TimePoint::new(100), TimePoint::new(200)),
        );
        let rect8 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(20), SpacePosition::new(30)),
            TimeInterval::new(TimePoint::new(200), TimePoint::new(300)),
        );
        assert!(!rect7.intersects(&rect8));
    }

    #[test]
    fn test_space_time_rectangle_intersection() {
        // Test intersection between two overlapping rectangles
        let rect1 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(30)),
            TimeInterval::new(TimePoint::new(100), TimePoint::new(300)),
        );
        let rect2 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(20), SpacePosition::new(40)),
            TimeInterval::new(TimePoint::new(200), TimePoint::new(400)),
        );

        let intersection = rect1.intersection(&rect2).unwrap();
        assert_eq!(intersection.space().start().value(), 20);
        assert_eq!(intersection.space().end().value(), 30);
        assert_eq!(intersection.time().start().value(), 200);
        assert_eq!(intersection.time().end().value(), 300);

        // Test when there is no intersection (should return None)
        let rect3 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(20)),
            TimeInterval::new(TimePoint::new(100), TimePoint::new(300)),
        );
        let rect4 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(30), SpacePosition::new(40)),
            TimeInterval::new(TimePoint::new(200), TimePoint::new(400)),
        );
        assert!(rect3.intersection(&rect4).is_none());

        // Test when rectangles touch at edges (should return None due to half-open intervals)
        let rect5 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(20)),
            TimeInterval::new(TimePoint::new(100), TimePoint::new(200)),
        );
        let rect6 = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(20), SpacePosition::new(30)),
            TimeInterval::new(TimePoint::new(200), TimePoint::new(300)),
        );
        assert!(rect5.intersection(&rect6).is_none());
    }

    #[test]
    fn test_space_time_rectangle_display() {
        let rect = SpaceTimeRectangle::new(
            SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(20)),
            TimeInterval::new(TimePoint::new(100), TimePoint::new(200)),
        );

        let display_string = format!("{}", rect);
        assert!(display_string.contains("[SpacePosition(10), SpacePosition(20))"));
        assert!(display_string.contains("[TimePoint(100), TimePoint(200))"));
        assert!(display_string.contains("(space x time)"));
    }
}
