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
use std::{collections::HashSet, hash::Hash};

use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint};
use num_traits::{PrimInt, Signed};

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

/// Represents a vessel in the Berthing Allocation Problem.
///
/// This struct encapsulates all the necessary information about a vessel,
/// including its unique identifier, length, arrival time, processing duration,
/// target berthing position, and associated costs.
#[derive(Debug, Clone, Copy)]
pub struct Vessel<TimeType = i64, CostType = i64>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    id: VesselId,
    length: SpaceLength,
    arrival_time: TimePoint<TimeType>,
    processing_duration: TimeDelta<TimeType>,
    target_berthing_position: SpacePosition,
    cost_per_waiting_time: Cost<CostType>,
    cost_per_target_berthing_deviation: Cost<CostType>,
}

impl<TimeType, CostType> PartialEq for Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<TimeType, CostType> Eq for Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
}

impl<TimeType, CostType> Hash for Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl<TimeType, CostType> PartialOrd for Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<TimeType, CostType> Ord for Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl<TimeType, CostType> Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    /// Creates a new `Vessel` instance with the specified parameters.
    ///
    /// This function initializes a `Vessel` with its unique identifier, length,
    /// arrival time, processing duration, target berthing position, and cost parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// assert_eq!(vessel.id(), VesselId::new(1));
    /// assert_eq!(vessel.length(), SpaceLength::new(100));
    /// assert_eq!(vessel.arrival_time(), TimePoint::new(1622547800));
    /// assert_eq!(vessel.processing_duration(), TimeDelta::new(3600));
    /// assert_eq!(vessel.target_berthing_position(), SpacePosition::new(50));
    /// assert_eq!(vessel.cost_per_waiting_time(), Cost::new(10));
    /// assert_eq!(vessel.cost_per_target_berthing_deviation(), Cost::new(5));
    /// ```
    pub fn new(
        id: VesselId,
        length: SpaceLength,
        arrival_time: TimePoint<TimeType>,
        processing_duration: TimeDelta<TimeType>,
        target_berthing_position: SpacePosition,
        cost_per_waiting_time: Cost<CostType>,
        cost_per_target_berthing_deviation: Cost<CostType>,
    ) -> Self {
        Vessel {
            id,
            length,
            arrival_time,
            processing_duration,
            target_berthing_position,
            cost_per_waiting_time,
            cost_per_target_berthing_deviation,
        }
    }

    /// Returns the unique identifier of the vessel.
    ///
    /// This function retrieves the `VesselId` associated with the vessel.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// assert_eq!(vessel.id(), VesselId::new(1));
    /// ```
    #[inline]
    pub fn id(&self) -> VesselId {
        self.id
    }

    /// Returns the length of the vessel.
    ///
    /// This function retrieves the `SpaceLength` of the vessel, which represents its size.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// assert_eq!(vessel.length(), SpaceLength::new(100));
    /// ```
    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.length
    }

    /// Returns the arrival time of the vessel.
    ///
    /// This function retrieves the `TimePoint` representing when the vessel arrives.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// assert_eq!(vessel.arrival_time(), TimePoint::new(1622547800));
    /// ```
    pub fn arrival_time(&self) -> TimePoint<TimeType> {
        self.arrival_time
    }

    /// Returns the processing duration of the vessel.
    ///
    /// This function retrieves the `TimeDelta` representing how long it takes to process the vessel.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// assert_eq!(vessel.processing_duration(), TimeDelta::new(3600));
    /// ```
    pub fn processing_duration(&self) -> TimeDelta<TimeType> {
        self.processing_duration
    }

    /// Returns the target berthing position of the vessel.
    ///
    /// This function retrieves the `SpacePosition` where the vessel is expected to berth.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// assert_eq!(vessel.target_berthing_position(), SpacePosition::new(50));
    /// ```
    pub fn target_berthing_position(&self) -> SpacePosition {
        self.target_berthing_position
    }

    /// Returns the cost per waiting time for the vessel.
    ///
    /// This function retrieves the `Cost` associated with waiting time for the vessel.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// assert_eq!(vessel.cost_per_waiting_time().value(), 10);
    /// ```
    pub fn cost_per_waiting_time(&self) -> Cost<CostType> {
        self.cost_per_waiting_time
    }

    /// Returns the cost per target berthing deviation for the vessel.
    ///
    /// This function retrieves the `Cost` associated with deviations from the target berthing position.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// assert_eq!(vessel.cost_per_target_berthing_deviation().value(), 5);
    /// ```
    pub fn cost_per_target_berthing_deviation(&self) -> Cost<CostType> {
        self.cost_per_target_berthing_deviation
    }
}

impl<TimeType, CostType> Display for Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed + Display,
    CostType: PrimInt + Signed + Display,
{
    /// Formats the `Vessel` for display.
    ///
    /// This implementation provides a string representation of the `Vessel`
    /// including its identifier, length, arrival time, processing duration,
    /// target berthing position, and cost parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// println!("{}", vessel);
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Vessel(id: {}, length: {}, arrival_time: {}, processing_duration: {}, target_berthing_position: {}, cost_per_waiting_time: {}, cost_per_target_berthing_deviation: {})",
            self.id,
            self.length,
            self.arrival_time,
            self.processing_duration,
            self.target_berthing_position,
            self.cost_per_waiting_time,
            self.cost_per_target_berthing_deviation
        )
    }
}

/// Represents the Berthing Allocation Problem.
///
/// This struct encapsulates the problem's vessels and the quay length available for berthing.
/// It provides methods to create a new problem instance, retrieve the quay length,
/// and access the set of vessels involved in the problem.
pub struct Problem<TimeType = i64, CostType = i64>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    vessels: HashSet<Vessel<TimeType, CostType>>,
    quay_length: SpaceLength,
}

impl<TimeType, CostType> Problem<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    /// Creates a new `Problem` instance with the specified quay length.
    ///
    /// This function initializes a `Problem` with an empty set of vessels and the given quay length.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use dock_alloc_model::{Problem, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessels = HashSet::new();
    /// let quay_length = SpaceLength::new(1000);
    /// let problem = Problem::<i64, i64>::new(vessels, quay_length);
    /// assert_eq!(problem.quay_length(), SpaceLength::new(1000));
    /// ```
    #[inline]
    pub fn new(vessels: HashSet<Vessel<TimeType, CostType>>, quay_length: SpaceLength) -> Self {
        Problem {
            vessels,
            quay_length,
        }
    }

    /// Returns the quay length of the problem.
    ///
    /// This function retrieves the `SpaceLength` representing the length of the quay available for berthing vessels.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use dock_alloc_model::{Problem, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessels = HashSet::new();
    /// let quay_length = SpaceLength::new(1000);
    /// let problem = Problem::<i64, i64>::new(vessels, quay_length);
    /// assert_eq!(problem.quay_length(), SpaceLength::new(1000));
    /// ```
    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    /// Returns a reference to the set of vessels in the problem.
    ///
    /// This function provides access to the `HashSet` of vessels, allowing iteration or inspection of the vessels involved in the problem.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use dock_alloc_model::{Problem, Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint};
    ///
    /// let vessels = HashSet::new();
    /// let quay_length = SpaceLength::new(1000);
    /// let problem = Problem::<i64, i64>::new(vessels, quay_length);
    /// assert!(problem.vessels().is_empty());
    /// ```
    #[inline]
    pub fn vessels(&self) -> &HashSet<Vessel<TimeType, CostType>> {
        &self.vessels
    }

    /// Returns the number of vessels in the problem.
    ///
    /// This function returns the count of vessels currently stored in the problem's vessel set.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use dock_alloc_model::{Problem, Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint};
    ///
    /// let vessels = HashSet::new();
    /// let quay_length = SpaceLength::new(1000);
    /// let problem = Problem::<i64, i64>::new(vessels, quay_length);
    /// assert_eq!(problem.vessel_len(), 0);
    /// ```
    #[inline]
    pub fn vessel_len(&self) -> usize {
        self.vessels.len()
    }
}

/// Type alias for the Berthing Allocation Problem with default types for time and cost.
///
/// This alias simplifies the usage of the `Problem` struct by providing a default type for time and cost,
/// which are both `i64`.
pub type BerthAllocationProblem = Problem<i64, i64>;

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

    #[test]
    fn test_vessel_display() {
        let vessel = Vessel::new(
            VesselId::new(1),
            SpaceLength::new(100),
            TimePoint::new(1622547800),
            TimeDelta::new(3600),
            SpacePosition::new(50),
            Cost::new(10),
            Cost::new(5),
        );
        assert_eq!(
            format!("{}", vessel),
            "Vessel(id: VesselId(1), \
            length: SpaceLength(100), \
            arrival_time: TimePoint(1622547800), \
            processing_duration: TimeDelta(3600), \
            target_berthing_position: SpacePosition(50), \
            cost_per_waiting_time: Cost(10), \
            cost_per_target_berthing_deviation: Cost(5))"
        );
    }

    #[test]
    fn vessels_are_unique_by_id() {
        let mut set = std::collections::HashSet::new();
        let v1 = Vessel::new(
            VesselId::new(1),
            SpaceLength::new(100),
            TimePoint::new(0),
            TimeDelta::new(10),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
        );
        let v2 = Vessel::new(
            // same id, different fields
            VesselId::new(1),
            SpaceLength::new(200),
            TimePoint::new(5),
            TimeDelta::new(20),
            SpacePosition::new(10),
            Cost::new(2),
            Cost::new(3),
        );
        set.insert(v1);
        set.insert(v2);
        assert_eq!(set.len(), 1);
    }
}
