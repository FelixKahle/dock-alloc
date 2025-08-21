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

#[allow(dead_code)]
use std::fmt::Display;

/// Represents a unique identifier for a vessel.
///
/// This identifier is used to track vessels in the system.
/// It is a wrapper around a `u64` value, providing methods to create and access
/// the identifier value.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::VesselId;
///
/// let vessel_id = VesselId::new(12345);
/// assert_eq!(vessel_id.value(), 12345);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VesselId(u64);

impl VesselId {
    /// Creates a new `VesselId` with the given identifier value.
    ///
    /// This function creates a new `VesselId` instance with the specified `u64` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::VesselId;
    ///
    /// let id = VesselId::new(42);
    /// assert_eq!(id.value(), 42);
    /// ```
    #[inline]
    pub const fn new(id: u64) -> Self {
        VesselId(id)
    }

    /// Returns the underlying `u64` value of the `VesselId`.
    ///
    /// This function retrieves the `u64` value that the `VesselId` wraps.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::VesselId;
    ///
    /// let id = VesselId::new(42);
    /// assert_eq!(id.value(), 42);
    /// ```
    #[inline]
    pub const fn value(&self) -> u64 {
        self.0
    }
}

impl Display for VesselId {
    /// Formats the `VesselId` for display.
    ///
    /// This implementation provides a string representation of the `VesselId`
    /// in the format `VesselId(value)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::VesselId;
    ///
    /// let id = VesselId::new(42);
    /// assert_eq!(format!("{}", id), "VesselId(42)");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "VesselId({})", self.0)
    }
}

impl From<u64> for VesselId {
    /// Converts a `u64` value into a `VesselId`.
    ///
    /// This implementation allows for easy conversion from a `u64` to a `VesselId`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::VesselId;
    ///
    /// let id: VesselId = 42.into();
    /// assert_eq!(id.value(), 42);
    /// ```
    fn from(value: u64) -> Self {
        VesselId(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vessel_id_creation() {
        let id = VesselId::new(42);
        assert_eq!(id.value(), 42);
    }

    #[test]
    fn test_vessel_id_display() {
        let id = VesselId::new(42);
        assert_eq!(format!("{}", id), "VesselId(42)");
    }

    #[test]
    fn test_vessel_id_equality() {
        let id1 = VesselId::new(42);
        let id2 = VesselId::new(42);
        assert_eq!(id1, id2);
    }

    #[test]
    fn test_vessel_id_from_u64() {
        let id: VesselId = 42.into();
        assert_eq!(id.value(), 42);
    }
}
