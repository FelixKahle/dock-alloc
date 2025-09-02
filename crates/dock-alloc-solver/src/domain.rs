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
