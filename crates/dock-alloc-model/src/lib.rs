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
    /// Compares two `Vessel` instances for equality based on their unique identifiers.
    ///
    /// This implementation checks if the `id` of one vessel is equal to the `id` of another vessel.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint};
    ///
    /// let vessel1 = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// let vessel2 = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(200),
    ///     TimePoint::new(3), // Example timestamp
    ///     TimeDelta::new(2), // Example duration in seconds
    ///     SpacePosition::new(1),
    ///     Cost::new(300), // Example cost per waiting time
    ///     Cost::new(500), // Example cost per target berthing deviation
    /// );
    /// assert!(vessel1 == vessel2);
    /// ```
    #[inline]
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
    /// Computes the hash of the `Vessel` based on its unique identifier.
    ///
    /// This implementation hashes the `id` of the vessel, allowing it to be used in hash-based collections.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use std::hash::{Hash, Hasher};
    /// use std::collections::hash_map::DefaultHasher;
    /// use std::collections::HashSet;
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint};
    ///
    /// let vessel1 = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// let vessel2 = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(200),
    ///     TimePoint::new(3), // Example timestamp
    ///     TimeDelta::new(2), // Example duration in seconds
    ///     SpacePosition::new(1),
    ///     Cost::new(300), // Example cost per waiting time
    ///     Cost::new(500), // Example cost per target berthing deviation
    /// );
    /// let mut h1 = DefaultHasher::new();
    /// vessel1.hash(&mut h1);
    /// let mut h2 = DefaultHasher::new();
    /// vessel2.hash(&mut h2);
    /// assert_eq!(h1.finish(), h2.finish());
    /// ```
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl<TimeType, CostType> PartialOrd for Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    /// Compares two `Vessel` instances for ordering based on their unique identifiers.
    ///
    /// This implementation allows for partial ordering of vessels, primarily based on their `id`.
    ///
    /// # Note
    ///
    /// You might expect ordering based on the arrival time or other attributes,
    /// but this implementation only considers the `id` for simplicity. You need
    /// to implement additional logic if you want to compare vessels based on other attributes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint};
    ///
    /// let vessel1 = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// let vessel2 = Vessel::new(
    ///     VesselId::new(2),
    ///     SpaceLength::new(200),
    ///     TimePoint::new(3), // Example timestamp
    ///     TimeDelta::new(2), // Example duration in seconds
    ///     SpacePosition::new(1),
    ///     Cost::new(300), // Example cost per waiting time
    ///     Cost::new(500), // Example cost per target berthing deviation
    /// );
    /// assert!(vessel1 < vessel2);
    /// ```
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<TimeType, CostType> Ord for Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    /// Compares two `Vessel` instances for total ordering based on their unique identifiers.
    ///
    /// This implementation allows for total ordering of vessels, primarily based on their `id`.
    ///
    /// # Note
    ///
    /// You might expect ordering based on the arrival time or other attributes,
    /// but this implementation only considers the `id` for simplicity. You need
    /// to implement additional logic if you want to compare vessels based on other attributes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint};
    ///
    /// let vessel1 = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800), // Example timestamp
    ///     TimeDelta::new(3600), // Example duration in seconds
    ///     SpacePosition::new(50),
    ///     Cost::new(10), // Example cost per waiting time
    ///     Cost::new(5), // Example cost per target berthing deviation
    /// );
    /// let vessel2 = Vessel::new(
    ///     VesselId::new(2),
    ///     SpaceLength::new(200),
    ///     TimePoint::new(3), // Example timestamp
    ///     TimeDelta::new(2), // Example duration in seconds
    ///     SpacePosition::new(1),
    ///     Cost::new(300), // Example cost per waiting time
    ///     Cost::new(500), // Example cost per target berthing deviation
    /// );
    /// assert!(vessel1 < vessel2);
    /// ```
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn cost_per_target_berthing_deviation(&self) -> Cost<CostType> {
        self.cost_per_target_berthing_deviation
    }
}

impl<TimeType, CostType> Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed + TryFrom<TimeType>,
{
    /// Calculates the cost incurred by the vessel for waiting time.
    ///
    /// This function computes the cost based on the waiting time provided as a `TimeDelta`.
    /// It multiplies the waiting time by the cost per waiting time to determine the total cost.
    ///
    /// # Panics
    ///
    /// This function will panic if the waiting time does not fit into the `CostType` and a conversion
    /// would result in an overflow or underflow.
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
    /// let waiting_time = TimeDelta::new(2); // Example waiting time in seconds
    /// let cost = vessel.waiting_cost(waiting_time);
    /// assert_eq!(cost.value(), 20); // 10 * 2
    /// ```
    #[inline]
    pub fn waiting_cost(&self, waiting_time: TimeDelta<TimeType>) -> Cost<CostType> {
        let scalar: CostType = CostType::try_from(waiting_time.value())
            .ok()
            .expect("waiting time does not fit in CostType");
        self.cost_per_waiting_time * scalar
    }
}

impl<TimeType, CostType> Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed + TryFrom<usize>,
{
    /// Calculates the cost incurred by the vessel for deviations from the target berthing position.
    ///
    /// This function computes the cost based on the deviation from the target berthing position
    /// provided as a `SpaceLength`. It multiplies the deviation by the cost per target berthing deviation
    /// to determine the total cost.
    ///
    /// # Panics
    ///
    /// This function will panic if the deviation does not fit into the `CostType` and a conversion
    /// would result in an overflow or underflow.
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
    /// let deviation = SpaceLength::new(3); // Example deviation in length
    /// let cost = vessel.target_berthing_deviation_cost(deviation);
    /// assert_eq!(cost.value(), 15); // 5 * 3
    /// ```
    #[inline]
    pub fn target_berthing_deviation_cost(&self, deviation: SpaceLength) -> Cost<CostType> {
        let scalar: CostType = CostType::try_from(deviation.value())
            .ok()
            .expect("deviation does not fit in CostType");
        self.cost_per_target_berthing_deviation * scalar
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

/// Represents an assignment of a vessel to a berthing position and time.
///
/// This struct encapsulates the details of a vessel's assignment, including the vessel itself,
/// the berthing position along the quay, and the berthing time.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{Assignment, VesselId};
/// use dock_alloc_core::domain::{SpacePosition, TimePoint};
///
/// let assignment = Assignment::new(
///     VesselId::new(1),
///     SpacePosition::new(100),
///     TimePoint::new(1622547800)
/// );
/// assert_eq!(assignment.vessel_id(), VesselId::new(1));
/// assert_eq!(assignment.berthing_position(), SpacePosition::new(100));
/// assert_eq!(assignment.berthing_time(), TimePoint::new(1622547800));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Assignment<TimeType = i64>
where
    TimeType: PrimInt + Signed,
{
    vessel_id: VesselId,
    berthing_position: SpacePosition,
    berthing_time: TimePoint<TimeType>,
}

impl<TimeType> Assignment<TimeType>
where
    TimeType: PrimInt + Signed,
{
    /// Creates a new `Assignment` instance with the specified parameters.
    ///
    /// This function initializes an `Assignment` with the vessel's unique identifier,
    /// the berthing position along the quay, and the berthing time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Assignment, VesselId};
    /// use dock_alloc_core::domain::{SpacePosition, TimePoint};
    ///
    /// let assignment = Assignment::new(
    ///     VesselId::new(1),
    ///     SpacePosition::new(100),
    ///     TimePoint::new(1622547800)
    /// );
    /// assert_eq!(assignment.vessel_id(), VesselId::new(1));
    /// assert_eq!(assignment.berthing_position(), SpacePosition::new(100));
    /// assert_eq!(assignment.berthing_time(), TimePoint::new(1622547800));
    /// ```
    #[inline]
    pub fn new(
        vessel_id: VesselId,
        berthing_position: SpacePosition,
        berthing_time: TimePoint<TimeType>,
    ) -> Self {
        Assignment {
            vessel_id,
            berthing_position,
            berthing_time,
        }
    }

    /// Returns the unique identifier of the vessel associated with the assignment.
    ///
    /// This function retrieves the `VesselId` of the vessel that has
    /// been assigned to a specific berthing position and time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Assignment, VesselId};
    /// use dock_alloc_core::domain::{SpacePosition, TimePoint};
    ///
    /// let assignment = Assignment::new(
    ///     VesselId::new(1),
    ///     SpacePosition::new(100),
    ///     TimePoint::new(1622547800)
    /// );
    /// assert_eq!(assignment.vessel_id(), VesselId::new(1));
    /// ```
    #[inline]
    pub fn vessel_id(&self) -> VesselId {
        self.vessel_id
    }

    /// Returns the berthing position of the vessel.
    ///
    /// This function retrieves the `SpacePosition` along the
    /// quay where the vessel is assigned to berth.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Assignment, VesselId};
    /// use dock_alloc_core::domain::{SpacePosition, TimePoint};
    ///
    /// let assignment = Assignment::new(
    ///     VesselId::new(1),
    ///     SpacePosition::new(100),
    ///     TimePoint::new(1622547800)
    /// );
    /// assert_eq!(assignment.berthing_position(), SpacePosition::new(100));
    /// ```
    #[inline]
    pub fn berthing_position(&self) -> SpacePosition {
        self.berthing_position
    }

    /// Returns the berthing time of the vessel.
    ///
    /// This function retrieves the `TimePoint` representing
    /// when the vessel is scheduled to berth.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Assignment, VesselId};
    /// use dock_alloc_core::domain::{SpacePosition, TimePoint};
    ///
    /// let assignment = Assignment::new(
    ///     VesselId::new(1),
    ///     SpacePosition::new(100),
    ///     TimePoint::new(1622547800)
    /// );
    /// assert_eq!(assignment.berthing_time(), TimePoint::new(1622547800));
    /// ```
    #[inline]
    pub fn berthing_time(&self) -> TimePoint<TimeType> {
        self.berthing_time
    }
}

impl<TimeType> Display for Assignment<TimeType>
where
    TimeType: PrimInt + Signed + Display,
{
    /// Formats the `Assignment` for display.
    ///
    /// This implementation provides a string representation of the `Assignment`
    /// including the vessel identifier, berthing position, and berthing time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Assignment, VesselId};
    /// use dock_alloc_core::domain::{SpacePosition, TimePoint};
    ///
    /// let assignment = Assignment::new(
    ///     VesselId::new(1),
    ///     SpacePosition::new(100),
    ///     TimePoint::new(1622547800)
    /// );
    /// println!("{}", assignment);
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment(vessel_id: {}, berthing_position: {}, berthing_time: {})",
            self.vessel_id, self.berthing_position, self.berthing_time
        )
    }
}

/// Represents an entry in the Berthing Allocation Problem.
///
/// This enum distinguishes between vessels that are unassigned and those
/// that have been pre-assigned specific berthing positions and times.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{ProblemEntry, Assignment, VesselId};
/// use dock_alloc_core::domain::{SpacePosition, TimePoint};
///
/// let unassigned: ProblemEntry<i64> = ProblemEntry::Unassigned(VesselId::new(1));
/// let pre_assigned: ProblemEntry<i64> = ProblemEntry::PreAssigned(Assignment::new(
///     VesselId::new(2),
///     SpacePosition::new(100),
///     TimePoint::new(1622547800)
/// ));
/// assert!(matches!(unassigned, ProblemEntry::Unassigned(_)));
/// assert!(matches!(pre_assigned, ProblemEntry::PreAssigned(_)));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProblemEntry<TimeType = i64>
where
    TimeType: PrimInt + Signed,
{
    /// A vessel that has not been assigned a berthing position or time.
    ///
    /// This variant holds the `VesselId` of the unassigned vessel.
    /// The solver can decide freely where and when to berth this vessel.
    Unassigned(VesselId),

    /// A vessel that has been pre-assigned a specific berthing position and time.
    ///
    /// This variant holds an `Assignment` struct containing the details of the pre-assignment.
    /// The solver must respect this assignment and cannot change it.
    PreAssigned(Assignment<TimeType>),
}

impl<TimeType> Display for ProblemEntry<TimeType>
where
    TimeType: PrimInt + Signed + Display,
{
    /// Formats the `ProblemEntry` for display.
    ///
    /// This implementation provides a string representation of the `ProblemEntry`
    /// indicating whether it is an unassigned vessel or a pre-assigned vessel with its details.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{ProblemEntry, Assignment, VesselId};
    /// use dock_alloc_core::domain::{SpacePosition, TimePoint};
    ///
    /// let unassigned: ProblemEntry<i64> = ProblemEntry::Unassigned(VesselId::new(1));
    /// let pre_assigned: ProblemEntry<i64> = ProblemEntry::PreAssigned(Assignment::new(
    ///     VesselId::new(2),
    ///     SpacePosition::new(100),
    ///     TimePoint::new(1622547800)
    /// ));
    /// println!("{}", unassigned);
    /// println!("{}", pre_assigned);
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProblemEntry::Unassigned(vessel_id) => {
                write!(f, "Unassigned(vessel_id: {})", vessel_id)
            }
            ProblemEntry::PreAssigned(assignment) => {
                write!(f, "PreAssigned({})", assignment)
            }
        }
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
    entries: HashSet<ProblemEntry<TimeType>>,
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
    /// use dock_alloc_model::{ProblemEntry, Problem, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessels = HashSet::new();
    /// let entries = HashSet::new();
    /// let quay_length = SpaceLength::new(1000);
    /// let problem = Problem::<i64, i64>::new(vessels, entries, quay_length);
    /// assert_eq!(problem.quay_length(), SpaceLength::new(1000));
    /// ```
    #[inline]
    pub fn new(
        vessels: HashSet<Vessel<TimeType, CostType>>,
        entries: HashSet<ProblemEntry<TimeType>>,
        quay_length: SpaceLength,
    ) -> Self {
        Problem {
            vessels,
            entries,
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
    /// use dock_alloc_model::{ProblemEntry, Problem, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint};
    ///
    /// let vessels = HashSet::new();
    /// let entries = HashSet::new();
    /// let quay_length = SpaceLength::new(1000);
    /// let problem = Problem::<i64, i64>::new(vessels, entries, quay_length);
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
    /// use dock_alloc_model::{ProblemEntry, Problem, Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint};
    ///
    /// let vessels = HashSet::new();
    /// let entries = HashSet::new();
    /// let quay_length = SpaceLength::new(1000);
    /// let problem = Problem::<i64, i64>::new(vessels, entries, quay_length);
    /// assert!(problem.vessels().is_empty());
    /// ```
    #[inline]
    pub fn vessels(&self) -> &HashSet<Vessel<TimeType, CostType>> {
        &self.vessels
    }

    /// Returns a reference to the set of problem entries.
    ///
    /// This function provides access to the `HashSet` of problem entries,
    /// allowing iteration or inspection of the entries involved in the problem.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use dock_alloc_model::{ProblemEntry, Problem, Vessel, VesselId};
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint};
    ///
    /// let vessels = HashSet::new();
    /// let entries = HashSet::new();
    /// let quay_length = SpaceLength::new(1000);
    /// let problem = Problem::<i64, i64>::new(vessels, entries, quay_length);
    /// assert!(problem.entries().is_empty());
    /// ```
    #[inline]
    pub fn entries(&self) -> &HashSet<ProblemEntry<TimeType>> {
        &self.entries
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
    /// let entries = HashSet::new();
    /// let quay_length = SpaceLength::new(1000);
    /// let problem = Problem::<i64, i64>::new(vessels, entries, quay_length);
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
    fn test_vessels_are_unique_by_id() {
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

    #[test]
    fn test_waiting_cost() {
        let vessel = Vessel::new(
            VesselId::new(1),
            SpaceLength::new(100),
            TimePoint::new(1622547800),
            TimeDelta::new(3600),
            SpacePosition::new(50),
            Cost::new(10),
            Cost::new(5),
        );
        let waiting_time = TimeDelta::new(2);
        let cost = vessel.waiting_cost(waiting_time);
        assert_eq!(cost.value(), 20); // 10 * 2
    }

    #[test]
    fn test_target_berthing_deviation_cost() {
        let vessel = Vessel::new(
            VesselId::new(1),
            SpaceLength::new(100),
            TimePoint::new(1622547800),
            TimeDelta::new(3600),
            SpacePosition::new(50),
            Cost::new(10),
            Cost::new(5),
        );
        let deviation = SpaceLength::new(3);
        let cost = vessel.target_berthing_deviation_cost(deviation);
        assert_eq!(cost.value(), 15); // 5 * 3
    }

    #[test]
    fn test_assignment_display() {
        let assignment = Assignment::new(
            VesselId::new(1),
            SpacePosition::new(100),
            TimePoint::new(1622547800),
        );
        assert_eq!(
            format!("{}", assignment),
            "Assignment(vessel_id: VesselId(1), \
            berthing_position: SpacePosition(100), \
            berthing_time: TimePoint(1622547800))"
        );
    }
}
