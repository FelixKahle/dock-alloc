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

#![forbid(unsafe_code)]

//! Unified domain model for the Berthing Allocation Problem (BAP).
//!
//! This module models **vessels** and **maintenance windows** uniformly as
//! *occupants* of the quay in time–space, validates pre-assignments, and
//! detects overlaps with a single sweep-line algorithm using half-open
//! intervals in both time and space.
//!
//! Highlights
//! - Self-documenting types and names (no cryptic `t0`, `x1`, etc.).
//! - Unified `Occupant`, `OccupancyAssignment`, `OccupancyEntry`, `OccupancyRect`.
//! - Clear, hand-written error types (no external derive macros).
//! - Robust validation: quay bounds, arrival-time feasibility, maintenance feasible window.
//! - Half-open semantics: adjacent in time/space is allowed; true overlap is rejected.

use std::fmt::Display;
use std::{
    cmp::Ordering,
    collections::{BTreeSet, HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    iter,
};

use dock_alloc_core::domain::{
    Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use num_traits::{PrimInt, Signed};

/// Identifier for a vessel.
///
/// Newtype around `u64` to avoid accidental mix-ups with other integer IDs.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::VesselId;
/// let vessel_id = VesselId::new(123);
/// assert_eq!(vessel_id.value(), 123);
/// ```
#[repr(transparent)]
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
        Self(id)
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "VesselId({})", self.0)
    }
}

impl From<u64> for VesselId {
    fn from(value: u64) -> Self {
        Self(value)
    }
}

/// Identifier for a maintenance specification/window.
///
/// Newtype around `u64`.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::MaintenanceId;
/// let maintenance_id = MaintenanceId::new(7);
/// assert_eq!(maintenance_id.value(), 7);
/// ```
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MaintenanceId(u64);

impl MaintenanceId {
    /// Creates a new `MaintenanceId` with the given identifier value.
    ///
    /// This function creates a new `MaintenanceId` instance with the specified `u64` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::MaintenanceId;
    ///
    /// let id = MaintenanceId::new(7);
    /// assert_eq!(id.value(), 7);
    /// ```
    #[inline]
    pub const fn new(id: u64) -> Self {
        Self(id)
    }

    /// Returns the underlying `u64` value of the `MaintenanceId`.
    ///
    /// This function retrieves the `u64` value that the `MaintenanceId` wraps.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::MaintenanceId;
    ///
    /// let id = MaintenanceId::new(7);
    /// assert_eq!(id.value(), 7);
    /// ```
    #[inline]
    pub const fn value(&self) -> u64 {
        self.0
    }
}

impl Display for MaintenanceId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MaintenanceId({})", self.0)
    }
}

impl From<u64> for MaintenanceId {
    fn from(value: u64) -> Self {
        Self(value)
    }
}

/// A vessel to be scheduled in the Berthing Allocation Problem.
///
/// Vessels are unique by their [`VesselId`]; equality and hashing
/// are therefore ID-based.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{Vessel, VesselId};
/// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint, TimeInterval};
///
/// let vessel = Vessel::new(
///     VesselId::new(1),
///     SpaceLength::new(120),
///     TimePoint::new(100),
///     TimeDelta::new(20),
///     SpacePosition::new(400),
///     Cost::new(3),
///     Cost::new(1),
///     TimeInterval::new(TimePoint::new(100), TimePoint::new(200)),
///     Cost::new(10000),
/// );
///
/// assert_eq!(vessel.id(), VesselId::new(1));
/// assert_eq!(vessel.length(), SpaceLength::new(120));
/// assert_eq!(vessel.arrival_time(), TimePoint::new(100));
/// assert_eq!(vessel.processing_duration(), TimeDelta::new(20));
/// assert_eq!(vessel.target_berthing_position(), SpacePosition::new(400));
/// assert_eq!(vessel.cost_per_waiting_time().value(), 3);
/// assert_eq!(vessel.cost_per_target_berthing_deviation().value(), 1);
/// assert_eq!(vessel.drop_cost(), Cost::new(10000));
/// ```
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
    feasible_time: TimeInterval<TimeType>,
    drop_cost: Cost<CostType>,
}

impl<TimeType, CostType> PartialEq for Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
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
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.id.cmp(&other.id))
    }
}

impl<TimeType, CostType> Ord for Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.id.cmp(&other.id)
    }
}

impl<TimeType, CostType> Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    /// Creates a new vessel.
    ///
    /// This function constructs a new `Vessel` instance with the specified parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{Vessel, VesselId};
    /// # use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint, TimeInterval};
    /// let vessel = Vessel::new(
    ///     VesselId::new(5),
    ///     SpaceLength::new(90),
    ///     TimePoint::new(10),
    ///     TimeDelta::new(4),
    ///     SpacePosition::new(200),
    ///     Cost::new(2),
    ///     Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(10), TimePoint::new(50)),
    ///     Cost::new(100),
    /// );
    /// assert_eq!(vessel.id(), VesselId::new(5));
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
        // NEW:
        feasible_time: TimeInterval<TimeType>,
        drop_cost: Cost<CostType>,
    ) -> Self {
        Self {
            id,
            length,
            arrival_time,
            processing_duration,
            target_berthing_position,
            cost_per_waiting_time,
            cost_per_target_berthing_deviation,
            // NEW:
            feasible_time,
            drop_cost,
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
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint, TimeInterval};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800),
    ///     TimeDelta::new(3600),
    ///     SpacePosition::new(50),
    ///     Cost::new(10),
    ///     Cost::new(5),
    ///     TimeInterval::new(TimePoint::new(1622547800), TimePoint::new(1622547800 + 7200)),
    ///     Cost::new(1000),
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
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint, TimeInterval};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800),
    ///     TimeDelta::new(3600),
    ///     SpacePosition::new(50),
    ///     Cost::new(10),
    ///     Cost::new(5),
    ///     TimeInterval::new(TimePoint::new(1622547800), TimePoint::new(1622547800 + 7200)),
    ///     Cost::new(1000),
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
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint, TimeInterval};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800),
    ///     TimeDelta::new(3600),
    ///     SpacePosition::new(50),
    ///     Cost::new(10),
    ///     Cost::new(5),
    ///     TimeInterval::new(TimePoint::new(1622547800), TimePoint::new(1622547800 + 7200)),
    ///     Cost::new(1000),
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
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint, TimeInterval};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800),
    ///     TimeDelta::new(3600),
    ///     SpacePosition::new(50),
    ///     Cost::new(10),
    ///     Cost::new(5),
    ///     TimeInterval::new(TimePoint::new(1622547800), TimePoint::new(1622547800 + 7200)),
    ///     Cost::new(1000),
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
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint, TimeInterval};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800),
    ///     TimeDelta::new(3600),
    ///     SpacePosition::new(50),
    ///     Cost::new(10),
    ///     Cost::new(5),
    ///     TimeInterval::new(TimePoint::new(1622547800), TimePoint::new(1622547800 + 7200)),
    ///     Cost::new(1000),
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
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint, TimeInterval};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800),
    ///     TimeDelta::new(3600),
    ///     SpacePosition::new(50),
    ///     Cost::new(10),
    ///     Cost::new(5),
    ///     TimeInterval::new(TimePoint::new(1622547800), TimePoint::new(1622547800 + 7200)),
    ///     Cost::new(1000),
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
    /// use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta , TimePoint, TimeInterval};
    ///
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(1622547800),
    ///     TimeDelta::new(3600),
    ///     SpacePosition::new(50),
    ///     Cost::new(10),
    ///     Cost::new(5),
    ///     TimeInterval::new(TimePoint::new(1622547800), TimePoint::new(1622547800 + 7200)),
    ///     Cost::new(1000),
    /// );
    /// assert_eq!(vessel.cost_per_target_berthing_deviation().value(), 5);
    /// ```
    #[inline]
    pub fn cost_per_target_berthing_deviation(&self) -> Cost<CostType> {
        self.cost_per_target_berthing_deviation
    }

    /// Time window in which the vessel must be processed.
    ///
    /// Returns the `TimeInterval` during which the vessel's processing must occur.
    /// The interval is half-open, `[start, end)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{Vessel, VesselId};
    /// # use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint, TimeInterval};
    /// let feasible_time = TimeInterval::new(TimePoint::new(10), TimePoint::new(50));
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(0),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(0),
    ///     Cost::new(5),
    ///     Cost::new(1),
    ///     feasible_time,
    ///     Cost::new(1000),
    /// );
    /// assert_eq!(vessel.feasible_time(), feasible_time);
    /// ```
    #[inline]
    pub fn feasible_time(&self) -> TimeInterval<TimeType> {
        self.feasible_time
    }

    /// Cost paid if the vessel is dropped (not served).
    ///
    /// Returns the penalty `Cost` incurred if the scheduling algorithm decides
    /// not to assign a berth to this vessel.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{Vessel, VesselId};
    /// # use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint, TimeInterval};
    /// let drop_cost = Cost::new(5000);
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(0),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(0),
    ///     Cost::new(5),
    ///     Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     drop_cost,
    /// );
    /// assert_eq!(vessel.drop_cost(), drop_cost);
    /// ```
    #[inline]
    pub fn drop_cost(&self) -> Cost<CostType> {
        self.drop_cost
    }
}

impl<TimeType, CostType> Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed + TryFrom<TimeType>,
{
    /// Computes the waiting cost for a given waiting duration.
    ///
    /// This multiplies the vessel's `cost_per_waiting_time` by the provided duration.
    ///
    /// # Panics
    ///
    /// Panics if the waiting duration cannot be converted to `CostType`
    /// (overflow/underflow).
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{Vessel, VesselId};
    /// # use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint, TimeInterval};
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(0),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(0),
    ///     Cost::new(5),
    ///     Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     Cost::new(1000),
    /// );
    /// let cost = vessel.waiting_cost(TimeDelta::new(3));
    /// assert_eq!(cost.value(), 15);
    /// ```
    #[inline]
    pub fn waiting_cost(&self, waiting_duration: TimeDelta<TimeType>) -> Cost<CostType> {
        let scalar: CostType = CostType::try_from(waiting_duration.value())
            .ok()
            .expect("waiting duration does not fit in CostType");
        self.cost_per_waiting_time * scalar
    }
}

impl<TimeType, CostType> Vessel<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed + TryFrom<usize>,
{
    /// Computes the cost of deviating from the target berthing position.
    ///
    /// This multiplies the vessel's `cost_per_target_berthing_deviation` by the provided deviation.
    ///
    /// # Panics
    ///
    /// Panics if the deviation length cannot be converted to `CostType`
    /// (overflow/underflow).
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{Vessel, VesselId};
    /// # use dock_alloc_core::domain::{Cost, SpaceLength, SpacePosition, TimeDelta, TimePoint, TimeInterval};
    /// let vessel = Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(0),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(20),
    ///     Cost::new(10),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     Cost::new(1000),
    /// );
    /// let cost = vessel.target_berthing_deviation_cost(SpaceLength::new(7));
    /// assert_eq!(cost.value(), 14);
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Vessel(id: {}, length: {}, arrival_time: {}, processing_duration: {}, target_berthing_position: {}, cost_per_waiting_time: {}, cost_per_target_berthing_deviation: {}, feasible_time: {}, drop_cost: {})",
            self.id,
            self.length,
            self.arrival_time,
            self.processing_duration,
            self.target_berthing_position,
            self.cost_per_waiting_time,
            self.cost_per_target_berthing_deviation,
            self.feasible_time,
            self.drop_cost
        )
    }
}

/// Fixed-position maintenance window specification.
///
/// A maintenance specification *fixes* the quay position and length and
/// the processing duration; only the start time is to be chosen within
/// a feasible time interval.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{MaintenanceId, MaintenanceSpec};
/// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint};
///
/// let spec = MaintenanceSpec::new(
///     MaintenanceId::new(10),
///     SpacePosition::new(300),
///     SpaceLength::new(50),
///     TimeDelta::new(4),
///     TimeInterval::new(TimePoint::new(100), TimePoint::new(200)),
/// );
///
/// assert_eq!(spec.id(), MaintenanceId::new(10));
/// assert_eq!(spec.position(), SpacePosition::new(300));
/// assert_eq!(spec.length(), SpaceLength::new(50));
/// assert_eq!(spec.duration(), TimeDelta::new(4));
/// assert_eq!(spec.feasible_time().start(), TimePoint::new(100));
/// ```
#[derive(Debug, Clone, Copy)]
pub struct MaintenanceSpec<TimeType: PrimInt + Signed> {
    id: MaintenanceId,
    position: SpacePosition,
    length: SpaceLength,
    duration: TimeDelta<TimeType>,
    feasible_time: TimeInterval<TimeType>,
}

impl<TimeType: PrimInt + Signed> MaintenanceSpec<TimeType> {
    /// Creates a new maintenance specification.
    ///
    /// Constructs a `MaintenanceSpec` with a fixed position, length, duration,
    /// and a time window within which it can be scheduled.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MaintenanceId, MaintenanceSpec};
    /// # use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint};
    /// let spec = MaintenanceSpec::new(
    ///     MaintenanceId::new(1),
    ///     SpacePosition::new(100),
    ///     SpaceLength::new(20),
    ///     TimeDelta::new(5),
    ///     TimeInterval::new(TimePoint::new(10), TimePoint::new(30)),
    /// );
    /// assert_eq!(spec.id().value(), 1);
    /// ```
    #[inline]
    pub fn new(
        id: MaintenanceId,
        position: SpacePosition,
        length: SpaceLength,
        duration: TimeDelta<TimeType>,
        feasible_time: TimeInterval<TimeType>,
    ) -> Self {
        Self {
            id,
            position,
            length,
            duration,
            feasible_time,
        }
    }

    /// The maintenance identifier.
    ///
    /// Returns the unique `MaintenanceId` for this specification.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MaintenanceId, MaintenanceSpec};
    /// # use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint};
    /// let spec = MaintenanceSpec::new(MaintenanceId::new(1), SpacePosition::new(0), SpaceLength::new(0), TimeDelta::new(0), TimeInterval::new(TimePoint::new(0), TimePoint::new(1)));
    /// assert_eq!(spec.id(), MaintenanceId::new(1));
    /// ```
    #[inline]
    pub fn id(&self) -> MaintenanceId {
        self.id
    }
    /// Fixed start position along the quay.
    ///
    /// Returns the `SpacePosition` where the maintenance window begins.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MaintenanceId, MaintenanceSpec};
    /// # use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint};
    /// let spec = MaintenanceSpec::new(MaintenanceId::new(1), SpacePosition::new(150), SpaceLength::new(0), TimeDelta::new(0), TimeInterval::new(TimePoint::new(0), TimePoint::new(1)));
    /// assert_eq!(spec.position(), SpacePosition::new(150));
    /// ```
    #[inline]
    pub fn position(&self) -> SpacePosition {
        self.position
    }
    /// Fixed spatial length on the quay.
    ///
    /// Returns the `SpaceLength` occupied by the maintenance.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MaintenanceId, MaintenanceSpec};
    /// # use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint};
    /// let spec = MaintenanceSpec::new(MaintenanceId::new(1), SpacePosition::new(0), SpaceLength::new(75), TimeDelta::new(0), TimeInterval::new(TimePoint::new(0), TimePoint::new(1)));
    /// assert_eq!(spec.length(), SpaceLength::new(75));
    /// ```
    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.length
    }
    /// Fixed processing duration.
    ///
    /// Returns the `TimeDelta` indicating how long the maintenance takes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MaintenanceId, MaintenanceSpec};
    /// # use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint};
    /// let spec = MaintenanceSpec::new(MaintenanceId::new(1), SpacePosition::new(0), SpaceLength::new(0), TimeDelta::new(8), TimeInterval::new(TimePoint::new(0), TimePoint::new(10)));
    /// assert_eq!(spec.duration(), TimeDelta::new(8));
    /// ```
    #[inline]
    pub fn duration(&self) -> TimeDelta<TimeType> {
        self.duration
    }
    /// Feasible time interval for scheduling the maintenance.
    ///
    /// Returns the `TimeInterval` in which the maintenance must be scheduled.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MaintenanceId, MaintenanceSpec};
    /// # use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint};
    /// let interval = TimeInterval::new(TimePoint::new(100), TimePoint::new(200));
    /// let spec = MaintenanceSpec::new(MaintenanceId::new(1), SpacePosition::new(0), SpaceLength::new(0), TimeDelta::new(0), interval);
    /// assert_eq!(spec.feasible_time(), interval);
    /// ```
    #[inline]
    pub fn feasible_time(&self) -> TimeInterval<TimeType> {
        self.feasible_time
    }
}

impl<TimeType: PrimInt + Signed + Display> Display for MaintenanceSpec<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "MaintenanceSpec(id: {}, position: {}, length: {}, duration: {}, feasible_time: {})",
            self.id, self.position, self.length, self.duration, self.feasible_time
        )
    }
}

impl<TimeType: PrimInt + Signed> PartialEq for MaintenanceSpec<TimeType> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<TimeType: PrimInt + Signed> Eq for MaintenanceSpec<TimeType> {}

impl<TimeType: PrimInt + Signed> Hash for MaintenanceSpec<TimeType> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl<TimeType: PrimInt + Signed> PartialOrd for MaintenanceSpec<TimeType> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.id.cmp(&other.id))
    }
}

impl<TimeType: PrimInt + Signed> Ord for MaintenanceSpec<TimeType> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.id.cmp(&other.id)
    }
}

/// A unified occupant of the quay: either a vessel or a maintenance window.
///
/// This enum allows treating both vessels and maintenance tasks uniformly as entities
/// that occupy a time-space rectangle on the quay. This simplifies validation logic,
/// such as overlap detection.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{Occupant, VesselId, MaintenanceId};
/// assert_eq!(format!("{}", Occupant::Vessel(VesselId::new(1))), "Vessel(VesselId(1))");
/// assert_eq!(format!("{}", Occupant::Maintenance(MaintenanceId::new(2))), "Maintenance(MaintenanceId(2))");
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Occupant {
    /// A vessel occupant, identified by its `VesselId`.
    Vessel(VesselId),
    /// A maintenance occupant, identified by its `MaintenanceId`.
    Maintenance(MaintenanceId),
}

impl Display for Occupant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Occupant::Vessel(id) => write!(f, "Vessel({})", id),
            Occupant::Maintenance(id) => write!(f, "Maintenance({})", id),
        }
    }
}

/// A time–space rectangle occupied on the quay by a specific [`Occupant`].
///
/// Rectangles use **half-open** intervals in both time and space:
/// `[start, end)`. This allows adjacency without overlap, simplifying collision checks.
/// For example, one task can end at time `t` and another can start at the same time `t`
/// without being considered an overlap.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{OccupancyRect, Occupant, VesselId};
/// use dock_alloc_core::domain::{SpaceInterval, SpacePosition, TimeInterval, TimePoint};
///
/// let rect = OccupancyRect::new(
///     Occupant::Vessel(VesselId::new(1)),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
///     SpaceInterval::new(SpacePosition::new(100), SpacePosition::new(150)),
/// );
///
/// assert_eq!(rect.occupant(), &Occupant::Vessel(VesselId::new(1)));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OccupancyRect<TimeType: PrimInt + Signed> {
    occupant: Occupant,
    time_interval: TimeInterval<TimeType>,
    space_interval: SpaceInterval,
}

impl<TimeType: PrimInt + Signed> OccupancyRect<TimeType> {
    /// Creates a new occupancy rectangle.
    ///
    /// Constructs an `OccupancyRect` from an occupant and its time and space intervals.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{OccupancyRect, Occupant, VesselId};
    /// # use dock_alloc_core::domain::{SpaceInterval, SpacePosition, TimeInterval, TimePoint};
    /// let rect = OccupancyRect::new(
    ///     Occupant::Vessel(VesselId::new(42)),
    ///     TimeInterval::new(TimePoint::new(10), TimePoint::new(20)),
    ///     SpaceInterval::new(SpacePosition::new(50), SpacePosition::new(150)),
    /// );
    /// assert!(matches!(rect.occupant(), Occupant::Vessel(_)));
    /// ```
    #[inline]
    pub fn new(
        occupant: Occupant,
        time_interval: TimeInterval<TimeType>,
        space_interval: SpaceInterval,
    ) -> Self {
        Self {
            occupant,
            time_interval,
            space_interval,
        }
    }

    /// Returns the occupant.
    ///
    /// Retrieves a reference to the `Occupant` associated with this rectangle.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{OccupancyRect, Occupant, VesselId};
    /// # use dock_alloc_core::domain::{SpaceInterval, SpacePosition, TimeInterval, TimePoint};
    /// let rect = OccupancyRect::new(Occupant::Vessel(VesselId::new(1)), TimeInterval::new(TimePoint::new(0), TimePoint::new(1)), SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(1)));
    /// assert_eq!(*rect.occupant(), Occupant::Vessel(VesselId::new(1)));
    /// ```
    #[inline]
    pub fn occupant(&self) -> &Occupant {
        &self.occupant
    }
    /// Returns the half-open time interval.
    ///
    /// Retrieves a reference to the `TimeInterval` `[start, end)` for this occupancy.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{OccupancyRect, Occupant, VesselId};
    /// # use dock_alloc_core::domain::{SpaceInterval, SpacePosition, TimeInterval, TimePoint};
    /// let interval = TimeInterval::new(TimePoint::new(5), TimePoint::new(15));
    /// let rect = OccupancyRect::new(Occupant::Vessel(VesselId::new(1)), interval, SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(1)));
    /// assert_eq!(*rect.time_interval(), interval);
    /// ```
    #[inline]
    pub fn time_interval(&self) -> &TimeInterval<TimeType> {
        &self.time_interval
    }
    /// Returns the half-open space interval.
    ///
    /// Retrieves a reference to the `SpaceInterval` `[start, end)` for this occupancy.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{OccupancyRect, Occupant, VesselId};
    /// # use dock_alloc_core::domain::{SpaceInterval, SpacePosition, TimeInterval, TimePoint};
    /// let interval = SpaceInterval::new(SpacePosition::new(50), SpacePosition::new(150));
    /// let rect = OccupancyRect::new(Occupant::Vessel(VesselId::new(1)), TimeInterval::new(TimePoint::new(0), TimePoint::new(1)), interval);
    /// assert_eq!(*rect.space_interval(), interval);
    /// ```
    #[inline]
    pub fn space_interval(&self) -> &SpaceInterval {
        &self.space_interval
    }
}

impl<TimeType: PrimInt + Signed + Display> Display for OccupancyRect<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "OccupancyRect(occupant: {}, time_interval: {}, space_interval: {})",
            self.occupant, self.time_interval, self.space_interval
        )
    }
}

/// A unified pre-assignment of an occupant.
///
/// This enum represents a fixed assignment for either a vessel or a maintenance window.
/// - Vessels: provide berthing position and start time.
/// - Maintenance: provide the start time; position/length come from the spec.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{OccupancyAssignment, VesselId, MaintenanceId};
/// use dock_alloc_core::domain::{SpacePosition, TimePoint};
///
/// let v = OccupancyAssignment::Vessel {
///     vessel_id: VesselId::new(3),
///     berthing_position: SpacePosition::new(500),
///     berthing_time: TimePoint::new(20),
/// };
///
/// let m = OccupancyAssignment::Maintenance {
///     id: MaintenanceId::new(7),
///     start_time: TimePoint::new(120),
/// };
///
/// assert!(matches!(v, OccupancyAssignment::Vessel{..}));
/// assert!(matches!(m, OccupancyAssignment::Maintenance{..}));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum OccupancyAssignment<TimeType: PrimInt + Signed> {
    /// Vessel pre-assignment.
    Vessel {
        /// Vessel identifier.
        vessel_id: VesselId,
        /// Quay position where the vessel’s bow (start) is berthed.
        berthing_position: SpacePosition,
        /// Start time of processing.
        berthing_time: TimePoint<TimeType>,
    },
    /// Maintenance pre-assignment.
    Maintenance {
        /// Maintenance identifier (references a spec).
        id: MaintenanceId,
        /// Start time of the maintenance processing.
        start_time: TimePoint<TimeType>,
    },
}

impl<TimeType: PrimInt + Signed + Display> Display for OccupancyAssignment<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Vessel {
                vessel_id,
                berthing_position,
                berthing_time,
            } => write!(
                f,
                "VesselAssignment(vessel_id: {}, position: {}, time: {})",
                vessel_id, berthing_position, berthing_time
            ),
            Self::Maintenance { id, start_time } => {
                write!(
                    f,
                    "MaintenanceAssignment(id: {}, start_time: {})",
                    id, start_time
                )
            }
        }
    }
}

/// Unified problem entry: either an occupant still to be scheduled or a fixed pre-assignment.
///
/// This allows a problem instance to contain a mix of tasks that need scheduling
/// (`Unassigned`) and tasks that have already been placed on the schedule (`PreAssigned`).
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{OccupancyEntry, OccupancyAssignment, Occupant, VesselId, MaintenanceId};
/// use dock_alloc_core::domain::{SpacePosition, TimePoint};
///
/// let unassigned_vessel: OccupancyEntry<i64> = OccupancyEntry::Unassigned(Occupant::Vessel(VesselId::new(1)));
/// let fixed = OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel{
///     vessel_id: VesselId::new(1),
///     berthing_position: SpacePosition::new(100),
///     berthing_time: TimePoint::new(10),
/// });
///
/// assert!(matches!(unassigned_vessel, OccupancyEntry::Unassigned(_)));
/// assert!(matches!(fixed, OccupancyEntry::PreAssigned(_)));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum OccupancyEntry<TimeType: PrimInt + Signed> {
    /// Occupant that is not yet assigned and needs to be scheduled.
    Unassigned(Occupant),
    /// Occupant that already has a fixed assignment on the quay.
    PreAssigned(OccupancyAssignment<TimeType>),
}

impl<TimeType: PrimInt + Signed + Display> Display for OccupancyEntry<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unassigned(o) => write!(f, "Unassigned({})", o),
            Self::PreAssigned(a) => write!(f, "PreAssigned({})", a),
        }
    }
}

/* ---------------------------- Error Types ----------------------------- */

/// Error: a referenced vessel is missing from the problem’s vessel set.
///
/// This error occurs during problem validation if a pre-assignment or other
/// entry refers to a `VesselId` that does not correspond to any vessel
/// defined in the problem's set of vessels.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{MissingVesselError, VesselId};
/// let err = MissingVesselError::new(VesselId::new(9));
/// assert_eq!(err.vessel_id(), VesselId::new(9));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MissingVesselError(VesselId);

impl MissingVesselError {
    /// Creates a new error for the given vessel id.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MissingVesselError, VesselId};
    /// let err = MissingVesselError::new(VesselId::new(99));
    /// assert_eq!(err.vessel_id().value(), 99);
    /// ```
    #[inline]
    pub fn new(vessel_id: VesselId) -> Self {
        Self(vessel_id)
    }
    /// Returns the missing vessel id.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MissingVesselError, VesselId};
    /// let err = MissingVesselError::new(VesselId::new(99));
    /// assert_eq!(err.vessel_id(), VesselId::new(99));
    /// ```
    #[inline]
    pub fn vessel_id(&self) -> VesselId {
        self.0
    }
}

impl Display for MissingVesselError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Missing vessel with ID: {}", self.0)
    }
}

impl std::error::Error for MissingVesselError {}

impl From<VesselId> for MissingVesselError {
    fn from(value: VesselId) -> Self {
        Self(value)
    }
}

/// Error: a pre-assigned vessel is scheduled outside its feasible time window.
///
/// This error occurs if a vessel's processing interval `[start, end)` is not
/// fully contained within its defined `feasible_time` interval.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{VesselId, VesselOutsideFeasibleTimeError};
/// use dock_alloc_core::domain::{TimeInterval, TimePoint};
///
/// let err = VesselOutsideFeasibleTimeError::new(
///     VesselId::new(1),
///     TimePoint::new(5),
///     TimePoint::new(15),
///     TimeInterval::new(TimePoint::new(10), TimePoint::new(20)),
/// );
/// assert_eq!(err.vessel_id(), VesselId::new(1));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VesselOutsideFeasibleTimeError<TimeType: PrimInt + Signed> {
    vessel_id: VesselId,
    assigned_start_time: TimePoint<TimeType>,
    assigned_end_time: TimePoint<TimeType>,
    feasible_time: TimeInterval<TimeType>,
}

impl<TimeType: PrimInt + Signed> VesselOutsideFeasibleTimeError<TimeType> {
    /// Creates a new `VesselOutsideFeasibleTimeError`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{VesselId, VesselOutsideFeasibleTimeError};
    /// # use dock_alloc_core::domain::{TimeInterval, TimePoint};
    /// let error = VesselOutsideFeasibleTimeError::new(
    ///     VesselId::new(1),
    ///     TimePoint::new(0),
    ///     TimePoint::new(10),
    ///     TimeInterval::new(TimePoint::new(5), TimePoint::new(15)),
    /// );
    /// assert_eq!(error.vessel_id().value(), 1);
    /// ```
    #[inline]
    pub fn new(
        vessel_id: VesselId,
        assigned_start_time: TimePoint<TimeType>,
        assigned_end_time: TimePoint<TimeType>,
        feasible_time: TimeInterval<TimeType>,
    ) -> Self {
        Self {
            vessel_id,
            assigned_start_time,
            assigned_end_time,
            feasible_time,
        }
    }
    /// The ID of the vessel that was assigned out of its feasible time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{VesselId, VesselOutsideFeasibleTimeError};
    /// # use dock_alloc_core::domain::{TimeInterval, TimePoint};
    /// let error = VesselOutsideFeasibleTimeError::new(VesselId::new(5), TimePoint::new(0), TimePoint::new(10), TimeInterval::new(TimePoint::new(5), TimePoint::new(15)));
    /// assert_eq!(error.vessel_id(), VesselId::new(5));
    /// ```
    #[inline]
    pub fn vessel_id(&self) -> VesselId {
        self.vessel_id
    }
    /// The assigned start time of the vessel's processing.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{VesselId, VesselOutsideFeasibleTimeError};
    /// # use dock_alloc_core::domain::{TimeInterval, TimePoint};
    /// let error = VesselOutsideFeasibleTimeError::new(VesselId::new(1), TimePoint::new(0), TimePoint::new(10), TimeInterval::new(TimePoint::new(5), TimePoint::new(15)));
    /// assert_eq!(error.assigned_start_time(), TimePoint::new(0));
    /// ```
    #[inline]
    pub fn assigned_start_time(&self) -> TimePoint<TimeType> {
        self.assigned_start_time
    }
    /// The calculated end time of the vessel's processing.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{VesselId, VesselOutsideFeasibleTimeError};
    /// # use dock_alloc_core::domain::{TimeInterval, TimePoint};
    /// let error = VesselOutsideFeasibleTimeError::new(VesselId::new(1), TimePoint::new(0), TimePoint::new(10), TimeInterval::new(TimePoint::new(5), TimePoint::new(15)));
    /// assert_eq!(error.assigned_end_time(), TimePoint::new(10));
    /// ```
    #[inline]
    pub fn assigned_end_time(&self) -> TimePoint<TimeType> {
        self.assigned_end_time
    }
    /// The feasible time window for the vessel.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{VesselId, VesselOutsideFeasibleTimeError};
    /// # use dock_alloc_core::domain::{TimeInterval, TimePoint};
    /// let feasible = TimeInterval::new(TimePoint::new(5), TimePoint::new(15));
    /// let error = VesselOutsideFeasibleTimeError::new(VesselId::new(1), TimePoint::new(0), TimePoint::new(10), feasible);
    /// assert_eq!(error.feasible_time(), feasible);
    /// ```
    #[inline]
    pub fn feasible_time(&self) -> TimeInterval<TimeType> {
        self.feasible_time
    }
}

impl<TimeType: PrimInt + Signed + Display> Display for VesselOutsideFeasibleTimeError<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Vessel {} assigned [{}, {}) outside feasible {}",
            self.vessel_id, self.assigned_start_time, self.assigned_end_time, self.feasible_time
        )
    }
}

impl<TimeType: PrimInt + Signed + Display + Debug> std::error::Error
    for VesselOutsideFeasibleTimeError<TimeType>
{
}

/// Error: a referenced maintenance specification is missing.
///
/// This error occurs if a pre-assignment refers to a `MaintenanceId` that
/// does not correspond to any defined `MaintenanceSpec`.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{MissingMaintenanceError, MaintenanceId};
/// let err = MissingMaintenanceError::new(MaintenanceId::new(2));
/// assert_eq!(err.maintenance_id(), MaintenanceId::new(2));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MissingMaintenanceError(MaintenanceId);

impl MissingMaintenanceError {
    /// Creates a new error for the given maintenance id.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MissingMaintenanceError, MaintenanceId};
    /// let err = MissingMaintenanceError::new(MaintenanceId::new(42));
    /// assert_eq!(err.maintenance_id().value(), 42);
    /// ```
    #[inline]
    pub fn new(maintenance_id: MaintenanceId) -> Self {
        Self(maintenance_id)
    }
    /// Returns the missing maintenance id.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MissingMaintenanceError, MaintenanceId};
    /// let err = MissingMaintenanceError::new(MaintenanceId::new(42));
    /// assert_eq!(err.maintenance_id(), MaintenanceId::new(42));
    /// ```
    #[inline]
    pub fn maintenance_id(&self) -> MaintenanceId {
        self.0
    }
}

impl Display for MissingMaintenanceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Missing maintenance spec with ID: {}", self.0)
    }
}

impl std::error::Error for MissingMaintenanceError {}

/// Error: an occupant would extend beyond the end of the quay.
///
/// This validation error occurs if an occupant's placement results in its
/// end position exceeding the total length of the quay.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{Occupant, OccupantOutOfBoundsError, VesselId};
/// use dock_alloc_core::domain::{SpaceLength, SpacePosition};
///
/// let err = OccupantOutOfBoundsError::new(
///     Occupant::Vessel(VesselId::new(1)),
///     SpacePosition::new(1200),
///     SpaceLength::new(1000),
/// );
/// assert_eq!(err.quay_length(), SpaceLength::new(1000));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OccupantOutOfBoundsError {
    occupant: Occupant,
    end_position: SpacePosition,
    quay_length: SpaceLength,
}

impl OccupantOutOfBoundsError {
    /// Creates a new out-of-bounds error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{Occupant, OccupantOutOfBoundsError, VesselId};
    /// # use dock_alloc_core::domain::{SpaceLength, SpacePosition};
    /// let err = OccupantOutOfBoundsError::new(Occupant::Vessel(VesselId::new(1)), SpacePosition::new(1001), SpaceLength::new(1000));
    /// assert_eq!(err.occupant(), Occupant::Vessel(VesselId::new(1)));
    /// ```
    #[inline]
    pub fn new(occupant: Occupant, end_position: SpacePosition, quay_length: SpaceLength) -> Self {
        Self {
            occupant,
            end_position,
            quay_length,
        }
    }
    /// The offending occupant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{Occupant, OccupantOutOfBoundsError, VesselId};
    /// # use dock_alloc_core::domain::{SpaceLength, SpacePosition};
    /// let occupant = Occupant::Vessel(VesselId::new(1));
    /// let err = OccupantOutOfBoundsError::new(occupant, SpacePosition::new(1001), SpaceLength::new(1000));
    /// assert_eq!(err.occupant(), occupant);
    /// ```
    #[inline]
    pub fn occupant(&self) -> Occupant {
        self.occupant
    }
    /// The computed end position that exceeded the quay.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{Occupant, OccupantOutOfBoundsError, VesselId};
    /// # use dock_alloc_core::domain::{SpaceLength, SpacePosition};
    /// let err = OccupantOutOfBoundsError::new(Occupant::Vessel(VesselId::new(1)), SpacePosition::new(1001), SpaceLength::new(1000));
    /// assert_eq!(err.end_position(), SpacePosition::new(1001));
    /// ```
    #[inline]
    pub fn end_position(&self) -> SpacePosition {
        self.end_position
    }
    /// The quay length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{Occupant, OccupantOutOfBoundsError, VesselId};
    /// # use dock_alloc_core::domain::{SpaceLength, SpacePosition};
    /// let err = OccupantOutOfBoundsError::new(Occupant::Vessel(VesselId::new(1)), SpacePosition::new(1001), SpaceLength::new(1000));
    /// assert_eq!(err.quay_length(), SpaceLength::new(1000));
    /// ```
    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }
}

impl Display for OccupantOutOfBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} is out of bounds: end position {} exceeds quay length {}",
            self.occupant, self.end_position, self.quay_length
        )
    }
}

impl std::error::Error for OccupantOutOfBoundsError {}

/// Error: an early vessel assignment (before arrival).
///
/// This error occurs if a vessel is assigned a berthing time that is earlier
/// than its specified arrival time.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{VesselAssignedBeforeArrivalError, VesselId};
/// use dock_alloc_core::domain::TimePoint;
///
/// let err = VesselAssignedBeforeArrivalError::new(
///     VesselId::new(1),
///     TimePoint::new(5),
///     TimePoint::new(10),
/// );
/// assert_eq!(err.vessel_id(), VesselId::new(1));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VesselAssignedBeforeArrivalError<TimeType: PrimInt + Signed> {
    vessel_id: VesselId,
    assigned_start_time: TimePoint<TimeType>,
    arrival_time: TimePoint<TimeType>,
}

impl<TimeType: PrimInt + Signed> VesselAssignedBeforeArrivalError<TimeType> {
    /// Creates a new error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{VesselAssignedBeforeArrivalError, VesselId};
    /// # use dock_alloc_core::domain::TimePoint;
    /// let err = VesselAssignedBeforeArrivalError::new(VesselId::new(1), TimePoint::new(5), TimePoint::new(10));
    /// assert_eq!(err.vessel_id().value(), 1);
    /// ```
    #[inline]
    pub fn new(
        vessel_id: VesselId,
        assigned_start_time: TimePoint<TimeType>,
        arrival_time: TimePoint<TimeType>,
    ) -> Self {
        Self {
            vessel_id,
            assigned_start_time,
            arrival_time,
        }
    }
    /// The vessel id.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{VesselAssignedBeforeArrivalError, VesselId};
    /// # use dock_alloc_core::domain::TimePoint;
    /// let err = VesselAssignedBeforeArrivalError::new(VesselId::new(1), TimePoint::new(5), TimePoint::new(10));
    /// assert_eq!(err.vessel_id(), VesselId::new(1));
    /// ```
    #[inline]
    pub fn vessel_id(&self) -> VesselId {
        self.vessel_id
    }
    /// The invalid assigned start time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{VesselAssignedBeforeArrivalError, VesselId};
    /// # use dock_alloc_core::domain::TimePoint;
    /// let err = VesselAssignedBeforeArrivalError::new(VesselId::new(1), TimePoint::new(5), TimePoint::new(10));
    /// assert_eq!(err.assigned_start_time(), TimePoint::new(5));
    /// ```
    #[inline]
    pub fn assigned_start_time(&self) -> TimePoint<TimeType> {
        self.assigned_start_time
    }
    /// The required minimum (arrival) time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{VesselAssignedBeforeArrivalError, VesselId};
    /// # use dock_alloc_core::domain::TimePoint;
    /// let err = VesselAssignedBeforeArrivalError::new(VesselId::new(1), TimePoint::new(5), TimePoint::new(10));
    /// assert_eq!(err.arrival_time(), TimePoint::new(10));
    /// ```
    #[inline]
    pub fn arrival_time(&self) -> TimePoint<TimeType> {
        self.arrival_time
    }
}

impl<TimeType: PrimInt + Signed + Display> Display for VesselAssignedBeforeArrivalError<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Vessel {} assigned at {}, earlier than its arrival {}",
            self.vessel_id, self.assigned_start_time, self.arrival_time
        )
    }
}

impl<TimeType: PrimInt + Signed + Display + Debug> std::error::Error
    for VesselAssignedBeforeArrivalError<TimeType>
{
}

/// Error: a maintenance assignment outside its feasible window.
///
/// This error occurs if a maintenance task's assigned time interval `[start, end)`
/// is not fully contained within its `feasible_time` window.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{MaintenanceOutsideFeasibleTimeError, MaintenanceId};
/// use dock_alloc_core::domain::{TimeInterval, TimePoint};
///
/// let err = MaintenanceOutsideFeasibleTimeError::new(
///     MaintenanceId::new(7),
///     TimePoint::new(0),
///     TimePoint::new(5),
///     TimeInterval::new(TimePoint::new(10), TimePoint::new(20)),
/// );
/// assert_eq!(err.maintenance_id(), MaintenanceId::new(7));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MaintenanceOutsideFeasibleTimeError<TimeType: PrimInt + Signed> {
    maintenance_id: MaintenanceId,
    assigned_start_time: TimePoint<TimeType>,
    assigned_end_time: TimePoint<TimeType>,
    feasible_time: TimeInterval<TimeType>,
}

impl<TimeType: PrimInt + Signed> MaintenanceOutsideFeasibleTimeError<TimeType> {
    /// Creates a new error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MaintenanceOutsideFeasibleTimeError, MaintenanceId};
    /// # use dock_alloc_core::domain::{TimeInterval, TimePoint};
    /// let err = MaintenanceOutsideFeasibleTimeError::new(MaintenanceId::new(1), TimePoint::new(5), TimePoint::new(15), TimeInterval::new(TimePoint::new(10), TimePoint::new(20)));
    /// assert_eq!(err.maintenance_id().value(), 1);
    /// ```
    #[inline]
    pub fn new(
        maintenance_id: MaintenanceId,
        assigned_start_time: TimePoint<TimeType>,
        assigned_end_time: TimePoint<TimeType>,
        feasible_time: TimeInterval<TimeType>,
    ) -> Self {
        Self {
            maintenance_id,
            assigned_start_time,
            assigned_end_time,
            feasible_time,
        }
    }
    /// The maintenance id.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MaintenanceOutsideFeasibleTimeError, MaintenanceId};
    /// # use dock_alloc_core::domain::{TimeInterval, TimePoint};
    /// let err = MaintenanceOutsideFeasibleTimeError::new(MaintenanceId::new(1), TimePoint::new(5), TimePoint::new(15), TimeInterval::new(TimePoint::new(10), TimePoint::new(20)));
    /// assert_eq!(err.maintenance_id(), MaintenanceId::new(1));
    /// ```
    #[inline]
    pub fn maintenance_id(&self) -> MaintenanceId {
        self.maintenance_id
    }
    /// Assigned start time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MaintenanceOutsideFeasibleTimeError, MaintenanceId};
    /// # use dock_alloc_core::domain::{TimeInterval, TimePoint};
    /// let err = MaintenanceOutsideFeasibleTimeError::new(MaintenanceId::new(1), TimePoint::new(5), TimePoint::new(15), TimeInterval::new(TimePoint::new(10), TimePoint::new(20)));
    /// assert_eq!(err.assigned_start_time(), TimePoint::new(5));
    /// ```
    #[inline]
    pub fn assigned_start_time(&self) -> TimePoint<TimeType> {
        self.assigned_start_time
    }
    /// Assigned end time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MaintenanceOutsideFeasibleTimeError, MaintenanceId};
    /// # use dock_alloc_core::domain::{TimeInterval, TimePoint};
    /// let err = MaintenanceOutsideFeasibleTimeError::new(MaintenanceId::new(1), TimePoint::new(5), TimePoint::new(15), TimeInterval::new(TimePoint::new(10), TimePoint::new(20)));
    /// assert_eq!(err.assigned_end_time(), TimePoint::new(15));
    /// ```
    #[inline]
    pub fn assigned_end_time(&self) -> TimePoint<TimeType> {
        self.assigned_end_time
    }
    /// Allowed feasible time interval.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{MaintenanceOutsideFeasibleTimeError, MaintenanceId};
    /// # use dock_alloc_core::domain::{TimeInterval, TimePoint};
    /// let interval = TimeInterval::new(TimePoint::new(10), TimePoint::new(20));
    /// let err = MaintenanceOutsideFeasibleTimeError::new(MaintenanceId::new(1), TimePoint::new(5), TimePoint::new(15), interval);
    /// assert_eq!(err.feasible_time(), interval);
    /// ```
    #[inline]
    pub fn feasible_time(&self) -> TimeInterval<TimeType> {
        self.feasible_time
    }
}

impl<TimeType: PrimInt + Signed + Display> Display
    for MaintenanceOutsideFeasibleTimeError<TimeType>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Maintenance {} assigned [{}, {}) outside feasible {}",
            self.maintenance_id,
            self.assigned_start_time,
            self.assigned_end_time,
            self.feasible_time
        )
    }
}

impl<TimeType: PrimInt + Signed + Display + Debug> std::error::Error
    for MaintenanceOutsideFeasibleTimeError<TimeType>
{
}

/// Error: overlap between two occupancy rectangles.
///
/// This error signals that two pre-assigned occupants have time and space
/// intervals that overlap, which is not allowed. Adjacency is permitted due
/// to half-open interval semantics.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{OccupancyRect, Occupant, OccupancyOverlapError, VesselId};
/// use dock_alloc_core::domain::{SpaceInterval, SpacePosition, TimeInterval, TimePoint};
///
/// let a = OccupancyRect::new(
///     Occupant::Vessel(VesselId::new(1)),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50)),
/// );
/// let b = OccupancyRect::new(
///     Occupant::Vessel(VesselId::new(2)),
///     TimeInterval::new(TimePoint::new(5), TimePoint::new(15)),
///     SpaceInterval::new(SpacePosition::new(25), SpacePosition::new(75)),
/// );
/// let err = OccupancyOverlapError::new(a, b);
/// assert_eq!(format!("{}", err).contains("overlap"), true);
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OccupancyOverlapError<TimeType: PrimInt + Signed> {
    rect_a: OccupancyRect<TimeType>,
    rect_b: OccupancyRect<TimeType>,
}

impl<TimeType: PrimInt + Signed> OccupancyOverlapError<TimeType> {
    /// Creates a new overlap error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{OccupancyRect, Occupant, OccupancyOverlapError, VesselId};
    /// # use dock_alloc_core::domain::{SpaceInterval, SpacePosition, TimeInterval, TimePoint};
    /// let a = OccupancyRect::new(Occupant::Vessel(VesselId::new(1)), TimeInterval::new(TimePoint::new(0), TimePoint::new(10)), SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10)));
    /// let b = OccupancyRect::new(Occupant::Vessel(VesselId::new(2)), TimeInterval::new(TimePoint::new(5), TimePoint::new(15)), SpaceInterval::new(SpacePosition::new(5), SpacePosition::new(15)));
    /// let err = OccupancyOverlapError::new(a, b);
    /// assert_eq!(*err.a(), a);
    /// assert_eq!(*err.b(), b);
    /// ```
    #[inline]
    pub fn new(rect_a: OccupancyRect<TimeType>, rect_b: OccupancyRect<TimeType>) -> Self {
        Self { rect_a, rect_b }
    }
    /// First rectangle involved.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{OccupancyRect, Occupant, OccupancyOverlapError, VesselId};
    /// # use dock_alloc_core::domain::{SpaceInterval, SpacePosition, TimeInterval, TimePoint};
    /// let a = OccupancyRect::new(Occupant::Vessel(VesselId::new(1)), TimeInterval::new(TimePoint::new(0), TimePoint::new(10)), SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10)));
    /// let b = OccupancyRect::new(Occupant::Vessel(VesselId::new(2)), TimeInterval::new(TimePoint::new(5), TimePoint::new(15)), SpaceInterval::new(SpacePosition::new(5), SpacePosition::new(15)));
    /// let err = OccupancyOverlapError::new(a, b);
    /// assert_eq!(*err.a(), a);
    /// ```
    #[inline]
    pub fn a(&self) -> &OccupancyRect<TimeType> {
        &self.rect_a
    }
    /// Second rectangle involved.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dock_alloc_model::{OccupancyRect, Occupant, OccupancyOverlapError, VesselId};
    /// # use dock_alloc_core::domain::{SpaceInterval, SpacePosition, TimeInterval, TimePoint};
    /// let a = OccupancyRect::new(Occupant::Vessel(VesselId::new(1)), TimeInterval::new(TimePoint::new(0), TimePoint::new(10)), SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10)));
    /// let b = OccupancyRect::new(Occupant::Vessel(VesselId::new(2)), TimeInterval::new(TimePoint::new(5), TimePoint::new(15)), SpaceInterval::new(SpacePosition::new(5), SpacePosition::new(15)));
    /// let err = OccupancyOverlapError::new(a, b);
    /// assert_eq!(*err.b(), b);
    /// ```
    #[inline]
    pub fn b(&self) -> &OccupancyRect<TimeType> {
        &self.rect_b
    }
}

impl<TimeType: PrimInt + Signed + Display> Display for OccupancyOverlapError<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Occupancy overlap between {} and {}",
            self.rect_a, self.rect_b
        )
    }
}

impl<TimeType: PrimInt + Signed + Display + Debug> std::error::Error
    for OccupancyOverlapError<TimeType>
{
}

/// Errors that can occur when constructing a [`Problem`].
///
/// This enum aggregates all possible validation errors that can arise from
/// creating a `Problem` instance, providing a single, comprehensive error type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProblemError<TimeType: PrimInt + Signed> {
    /// Pre-assignment referenced a vessel not present in `vessels`.
    MissingVessel(MissingVesselError),
    /// Pre-assignment referenced a maintenance spec not present in `maintenance_specs`.
    MissingMaintenance(MissingMaintenanceError),
    /// An occupant would exceed the quay bounds.
    OccupantOutOfBounds(OccupantOutOfBoundsError),
    /// Two pre-assigned rectangles overlap in time *and* space.
    OccupancyOverlap(OccupancyOverlapError<TimeType>),
    /// Vessel assigned before its arrival.
    VesselAssignedBeforeArrival(VesselAssignedBeforeArrivalError<TimeType>),
    /// Maintenance assigned outside its feasible time interval.
    MaintenanceOutsideFeasibleTime(MaintenanceOutsideFeasibleTimeError<TimeType>),
    /// Vessel assigned outside its feasible time interval.
    VesselOutsideFeasibleTime(VesselOutsideFeasibleTimeError<TimeType>),
}

impl<TimeType: PrimInt + Signed + Display> Display for ProblemError<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingVessel(e) => write!(f, "{}", e),
            Self::MissingMaintenance(e) => write!(f, "{}", e),
            Self::OccupantOutOfBounds(e) => write!(f, "{}", e),
            Self::OccupancyOverlap(e) => write!(f, "{}", e),
            Self::VesselAssignedBeforeArrival(e) => write!(f, "{}", e),
            Self::MaintenanceOutsideFeasibleTime(e) => write!(f, "{}", e),
            Self::VesselOutsideFeasibleTime(e) => write!(f, "{}", e),
        }
    }
}

impl<TimeType: PrimInt + Signed + Display + Debug> std::error::Error for ProblemError<TimeType> {}

/* ------------------------------ Problem ------------------------------- */

/// The Berthing Allocation Problem instance.
///
/// Holds the set of vessels, maintenance specifications, and problem entries
/// (unassigned occupants or fixed pre-assignments), along with the quay length.
///
/// Construction validates all pre-assignments and rejects invalid instances with
/// a [`ProblemError`].
///
/// # Examples
///
/// ```
/// use std::collections::HashSet;
/// use dock_alloc_model::*;
/// use dock_alloc_core::domain::*;
///
/// // Inputs
/// let vessels: HashSet<_> = [
///     Vessel::new(
///         VesselId::new(1),
///         SpaceLength::new(100),
///         TimePoint::new(0),
///         TimeDelta::new(10),
///         SpacePosition::new(50),
///         Cost::new(1),
///         Cost::new(1),
///         TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
///         Cost::new(1000),
///     ),
/// ]
/// .into_iter()
/// .collect();
///
/// let maintenance_specs: HashSet<_> = [
///     MaintenanceSpec::new(
///         MaintenanceId::new(9),
///         SpacePosition::new(300),
///         SpaceLength::new(50),
///         TimeDelta::new(5),
///         TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
///     ),
/// ]
/// .into_iter()
/// .collect();
///
/// // Pre-assign one vessel; keep maintenance unassigned:
/// let entries: HashSet<_> = [
///     OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel{
///         vessel_id: VesselId::new(1),
///         berthing_position: SpacePosition::new(100),
///         berthing_time: TimePoint::new(0),
///     }),
///     OccupancyEntry::Unassigned(Occupant::Maintenance(MaintenanceId::new(9))),
/// ]
/// .into_iter()
/// .collect();
///
/// let problem = Problem::<i64, i64>::new(vessels, maintenance_specs, entries, SpaceLength::new(1_000)).unwrap();
/// assert_eq!(problem.quay_length(), SpaceLength::new(1_000));
/// assert_eq!(problem.vessel_len(), 1);
/// assert_eq!(problem.maintenance_len(), 1);
/// ```
#[derive(Debug, Clone)]
pub struct Problem<TimeType = i64, CostType = i64>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    vessels: HashSet<Vessel<TimeType, CostType>>,
    maintenance_specs: HashSet<MaintenanceSpec<TimeType>>,
    entries: HashSet<OccupancyEntry<TimeType>>,
    quay_length: SpaceLength,
}

impl<TimeType, CostType> Problem<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    /// Constructs a validated problem.
    ///
    /// This validates all **pre-assigned** entries and ensures that
    /// - referenced vessels/specs exist,
    /// - vessels are not scheduled before arrival,
    /// - maintenance is within its feasible interval,
    /// - spatial end positions do not exceed the quay length,
    /// - there is **no overlap** in time *and* space across all pre-assignments.
    ///
    /// Half-open semantics are used throughout: `[start, end)`.
    ///
    /// # Errors
    /// Returns a [`ProblemError`] if any validation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::HashSet;
    /// # use dock_alloc_model::*;
    /// # use dock_alloc_core::domain::*;
    /// let vessels: HashSet<_> = [Vessel::new(
    ///     VesselId::new(1),
    ///     SpaceLength::new(100),
    ///     TimePoint::new(0),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(1),
    ///     Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     Cost::new(1000),
    /// )].into_iter().collect();
    ///
    /// let maintenance_specs: HashSet<_> = [].into_iter().collect();
    ///
    /// let entries: HashSet<_> = [OccupancyEntry::PreAssigned(
    ///     OccupancyAssignment::Vessel{
    ///         vessel_id: VesselId::new(1),
    ///         berthing_position: SpacePosition::new(100),
    ///         berthing_time: TimePoint::new(0),
    ///     }
    /// )].into_iter().collect();
    ///
    /// let problem = Problem::<i64, i64>::new(vessels, maintenance_specs, entries, SpaceLength::new(1_000));
    /// assert!(problem.is_ok());
    /// ```
    pub fn new(
        vessels: HashSet<Vessel<TimeType, CostType>>,
        maintenance_specs: HashSet<MaintenanceSpec<TimeType>>,
        entries: HashSet<OccupancyEntry<TimeType>>,
        quay_length: SpaceLength,
    ) -> Result<Self, ProblemError<TimeType>> {
        // Build lookup maps for fast validation.
        let vessel_by_id: HashMap<VesselId, &Vessel<TimeType, CostType>> =
            vessels.iter().map(|v| (v.id(), v)).collect();
        let maintenance_by_id: HashMap<MaintenanceId, &MaintenanceSpec<TimeType>> =
            maintenance_specs.iter().map(|m| (m.id(), m)).collect();

        let quay_end_position: SpacePosition = SpacePosition::new(quay_length.value());

        // Build occupancy rectangles from pre-assigned entries.
        let mut occupancy_rectangles: Vec<OccupancyRect<TimeType>> = Vec::new();

        for entry in entries.iter() {
            if let OccupancyEntry::PreAssigned(assignment) = entry {
                match assignment {
                    OccupancyAssignment::Vessel {
                        vessel_id,
                        berthing_position,
                        berthing_time,
                    } => {
                        let vessel = *vessel_by_id.get(vessel_id).ok_or_else(|| {
                            ProblemError::MissingVessel(MissingVesselError::new(*vessel_id))
                        })?;

                        // Enforce "not before arrival".
                        if *berthing_time < vessel.arrival_time() {
                            return Err(ProblemError::VesselAssignedBeforeArrival(
                                VesselAssignedBeforeArrivalError::new(
                                    *vessel_id,
                                    *berthing_time,
                                    vessel.arrival_time(),
                                ),
                            ));
                        }

                        let processing_start_time: TimePoint<TimeType> = *berthing_time;
                        let processing_end_time: TimePoint<TimeType> =
                            processing_start_time + vessel.processing_duration();

                        let vessel_feasible = vessel.feasible_time();
                        if processing_start_time < vessel_feasible.start()
                            || processing_end_time > vessel_feasible.end()
                        {
                            return Err(ProblemError::VesselOutsideFeasibleTime(
                                VesselOutsideFeasibleTimeError::new(
                                    *vessel_id,
                                    processing_start_time,
                                    processing_end_time,
                                    vessel_feasible,
                                ),
                            ));
                        }

                        let start_position: SpacePosition = *berthing_position;
                        let end_position: SpacePosition = start_position + vessel.length();

                        if end_position > quay_end_position {
                            return Err(ProblemError::OccupantOutOfBounds(
                                OccupantOutOfBoundsError::new(
                                    Occupant::Vessel(*vessel_id),
                                    end_position,
                                    quay_length,
                                ),
                            ));
                        }

                        occupancy_rectangles.push(OccupancyRect::new(
                            Occupant::Vessel(*vessel_id),
                            TimeInterval::new(processing_start_time, processing_end_time),
                            SpaceInterval::new(start_position, end_position),
                        ));
                    }
                    OccupancyAssignment::Maintenance { id, start_time } => {
                        let spec = *maintenance_by_id.get(id).ok_or_else(|| {
                            ProblemError::MissingMaintenance(MissingMaintenanceError::new(*id))
                        })?;

                        let processing_start_time: TimePoint<TimeType> = *start_time;
                        let processing_end_time: TimePoint<TimeType> =
                            processing_start_time + spec.duration();

                        // Must fit entirely in feasible interval.
                        let feasible = spec.feasible_time();
                        if processing_start_time < feasible.start()
                            || processing_end_time > feasible.end()
                        {
                            return Err(ProblemError::MaintenanceOutsideFeasibleTime(
                                MaintenanceOutsideFeasibleTimeError::new(
                                    *id,
                                    processing_start_time,
                                    processing_end_time,
                                    feasible,
                                ),
                            ));
                        }

                        let start_position: SpacePosition = spec.position();
                        let end_position: SpacePosition = start_position + spec.length();
                        if end_position > quay_end_position {
                            return Err(ProblemError::OccupantOutOfBounds(
                                OccupantOutOfBoundsError::new(
                                    Occupant::Maintenance(*id),
                                    end_position,
                                    quay_length,
                                ),
                            ));
                        }

                        occupancy_rectangles.push(OccupancyRect::new(
                            Occupant::Maintenance(*id),
                            TimeInterval::new(processing_start_time, processing_end_time),
                            SpaceInterval::new(start_position, end_position),
                        ));
                    }
                }
            }
        }

        // If there are no rectangles, overlap sweep is unnecessary.
        if occupancy_rectangles.is_empty() {
            return Ok(Self {
                vessels,
                maintenance_specs,
                entries,
                quay_length,
            });
        }

        // Sweep-line over time with active set ordered by space start.
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum BoundaryKind {
            Start,
            End,
        }

        #[derive(Clone, Copy)]
        struct TimeBoundary<T: PrimInt + Signed> {
            time: TimePoint<T>,
            kind: BoundaryKind,
            rectangle_index: usize,
        }

        let mut time_boundaries: Vec<TimeBoundary<TimeType>> = occupancy_rectangles
            .iter()
            .enumerate()
            .flat_map(|(idx, rect)| {
                iter::once(TimeBoundary {
                    time: rect.time_interval().start(),
                    kind: BoundaryKind::Start,
                    rectangle_index: idx,
                })
                .chain(iter::once(TimeBoundary {
                    time: rect.time_interval().end(),
                    kind: BoundaryKind::End,
                    rectangle_index: idx,
                }))
            })
            .collect();

        // Sort time boundaries; at equal time, process End before Start (half-open).
        time_boundaries.sort_by(|a, b| {
            a.time.cmp(&b.time).then_with(|| match (a.kind, b.kind) {
                (BoundaryKind::End, BoundaryKind::Start) => Ordering::Less,
                (BoundaryKind::Start, BoundaryKind::End) => Ordering::Greater,
                _ => Ordering::Equal,
            })
        });

        let mut active_by_space_start: BTreeSet<(SpacePosition, usize)> = BTreeSet::new();

        #[inline]
        fn half_open_intervals_overlap(a: &SpaceInterval, b: &SpaceInterval) -> bool {
            a.start() < b.end() && b.start() < a.end()
        }

        for boundary in time_boundaries {
            let rect = occupancy_rectangles[boundary.rectangle_index];
            match boundary.kind {
                BoundaryKind::Start => {
                    let key = (rect.space_interval().start(), boundary.rectangle_index);

                    // Check previous neighbor in space order, if any.
                    if let Some(&(_, prev_idx)) = active_by_space_start.range(..key).next_back() {
                        let prev_rect = occupancy_rectangles[prev_idx];
                        if half_open_intervals_overlap(
                            prev_rect.space_interval(),
                            rect.space_interval(),
                        ) {
                            return Err(ProblemError::OccupancyOverlap(
                                OccupancyOverlapError::new(prev_rect, rect),
                            ));
                        }
                    }

                    // Check next neighbor in space order, if any.
                    if let Some(&(_, next_idx)) = active_by_space_start.range(key..).next() {
                        let next_rect = occupancy_rectangles[next_idx];
                        if half_open_intervals_overlap(
                            next_rect.space_interval(),
                            rect.space_interval(),
                        ) {
                            return Err(ProblemError::OccupancyOverlap(
                                OccupancyOverlapError::new(next_rect, rect),
                            ));
                        }
                    }

                    active_by_space_start.insert(key);
                }
                BoundaryKind::End => {
                    active_by_space_start
                        .remove(&(rect.space_interval().start(), boundary.rectangle_index));
                }
            }
        }

        Ok(Self {
            vessels,
            maintenance_specs,
            entries,
            quay_length,
        })
    }

    /// Returns the quay length.
    ///
    /// This is the total available space along the quay.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::HashSet;
    /// # use dock_alloc_model::*;
    /// # use dock_alloc_core::domain::*;
    /// let problem = Problem::<i64, i64>::new(HashSet::new(), HashSet::new(), HashSet::new(), SpaceLength::new(1200)).unwrap();
    /// assert_eq!(problem.quay_length(), SpaceLength::new(1200));
    /// ```
    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    /// Returns all vessels.
    ///
    /// Provides a reference to the `HashSet` of all `Vessel`s in the problem.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::HashSet;
    /// # use dock_alloc_model::*;
    /// # use dock_alloc_core::domain::*;
    /// let vessels = HashSet::from([Vessel::new(VesselId::new(1), SpaceLength::new(100), TimePoint::new(0), TimeDelta::new(10), SpacePosition::new(0), Cost::new(1), Cost::new(1), TimeInterval::new(TimePoint::new(0), TimePoint::new(100)), Cost::new(1000))]);
    /// let problem = Problem::new(vessels.clone(), HashSet::new(), HashSet::new(), SpaceLength::new(1000)).unwrap();
    /// assert_eq!(*problem.vessels(), vessels);
    /// ```
    #[inline]
    pub fn vessels(&self) -> &HashSet<Vessel<TimeType, CostType>> {
        &self.vessels
    }

    /// Returns all maintenance specifications.
    ///
    /// Provides a reference to the `HashSet` of all `MaintenanceSpec`s in the problem.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::HashSet;
    /// # use dock_alloc_model::*;
    /// # use dock_alloc_core::domain::*;
    /// let specs = HashSet::from([MaintenanceSpec::new(MaintenanceId::new(1), SpacePosition::new(0), SpaceLength::new(50), TimeDelta::new(5), TimeInterval::new(TimePoint::new(0), TimePoint::new(100)))]);
    /// let problem: Problem<i64, i64> = Problem::new(HashSet::new(), specs.clone(), HashSet::new(), SpaceLength::new(1000)).unwrap();
    /// assert_eq!(*problem.maintenance_specs(), specs);
    /// ```
    #[inline]
    pub fn maintenance_specs(&self) -> &HashSet<MaintenanceSpec<TimeType>> {
        &self.maintenance_specs
    }

    /// Returns all entries (unassigned or pre-assigned occupants).
    ///
    /// Provides a reference to the `HashSet` of all `OccupancyEntry`s, which represent
    /// both schedulable tasks and fixed assignments.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::HashSet;
    /// # use dock_alloc_model::*;
    /// # use dock_alloc_core::domain::*;
    /// let entries = HashSet::from([OccupancyEntry::Unassigned(Occupant::Vessel(VesselId::new(1)))]);
    /// let vessels = HashSet::from([Vessel::new(VesselId::new(1), SpaceLength::new(100), TimePoint::new(0), TimeDelta::new(10), SpacePosition::new(0), Cost::new(1), Cost::new(1), TimeInterval::new(TimePoint::new(0), TimePoint::new(100)), Cost::new(1000))]);
    /// let problem = Problem::new(vessels, HashSet::new(), entries.clone(), SpaceLength::new(1000)).unwrap();
    /// assert_eq!(*problem.entries(), entries);
    /// ```
    #[inline]
    pub fn entries(&self) -> &HashSet<OccupancyEntry<TimeType>> {
        &self.entries
    }

    /// Number of vessels.
    ///
    /// Returns the total count of vessels defined in the problem.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::HashSet;
    /// # use dock_alloc_model::*;
    /// # use dock_alloc_core::domain::*;
    /// let vessels = HashSet::from([Vessel::new(VesselId::new(1), SpaceLength::new(100), TimePoint::new(0), TimeDelta::new(10), SpacePosition::new(0), Cost::new(1), Cost::new(1), TimeInterval::new(TimePoint::new(0), TimePoint::new(100)), Cost::new(1000))]);
    /// let problem = Problem::new(vessels, HashSet::new(), HashSet::new(), SpaceLength::new(1000)).unwrap();
    /// assert_eq!(problem.vessel_len(), 1);
    /// ```
    #[inline]
    pub fn vessel_len(&self) -> usize {
        self.vessels.len()
    }

    /// Number of maintenance specifications.
    ///
    /// Returns the total count of maintenance specifications defined in the problem.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::HashSet;
    /// # use dock_alloc_model::*;
    /// # use dock_alloc_core::domain::*;
    /// let specs = HashSet::from([MaintenanceSpec::new(MaintenanceId::new(1), SpacePosition::new(0), SpaceLength::new(50), TimeDelta::new(5), TimeInterval::new(TimePoint::new(0), TimePoint::new(100)))]);
    /// let problem: Problem<i64, i64> = Problem::new(HashSet::new(), specs, HashSet::new(), SpaceLength::new(1000)).unwrap();
    /// assert_eq!(problem.maintenance_len(), 1);
    /// ```
    #[inline]
    pub fn maintenance_len(&self) -> usize {
        self.maintenance_specs.len()
    }
}

/// Convenient type alias for the common `i64` time/cost instantiation.
///
/// This simplifies type signatures when working with the most common
/// integer types for time and cost values in the problem domain.
pub type BerthAllocationProblem = Problem<i64, i64>;

/* ------------------------------- Tests -------------------------------- */

#[cfg(test)]
mod tests {
    use super::*;

    fn vessel<T: PrimInt + Signed>(
        id: u64,
        length: usize,
        processing: T,
        arrival: T,
        target_pos: usize,
        feasible_interval: TimeInterval<T>,
    ) -> Vessel<T, i64> {
        Vessel::new(
            VesselId::new(id),
            SpaceLength::new(length),
            TimePoint::new(arrival),
            TimeDelta::new(processing),
            SpacePosition::new(target_pos),
            Cost::new(1),
            Cost::new(1),
            feasible_interval,
            Cost::new(1),
        )
    }

    fn window<T: PrimInt + Signed>(start: T, end: T) -> TimeInterval<T> {
        TimeInterval::new(TimePoint::new(start), TimePoint::new(end))
    }

    fn hs<T>(items: impl IntoIterator<Item = T>) -> HashSet<T>
    where
        T: Eq + Hash,
    {
        items.into_iter().collect()
    }

    #[test]
    fn test_ok_no_preassignments() {
        let vessels = hs([vessel::<i64>(1, 100, 10, 0, 0, window(0, 1_000))]);
        let maints: HashSet<MaintenanceSpec<i64>> = HashSet::new();
        let entries = HashSet::new();
        let p = Problem::new(vessels, maints, entries, SpaceLength::new(1_000));
        assert!(p.is_ok());
    }

    #[test]
    fn test_ok_single_vessel_preassignment_in_bounds() {
        let vessels = hs([vessel::<i64>(1, 100, 10, 0, 0, window(0, 1_000))]);
        let maints: HashSet<MaintenanceSpec<i64>> = HashSet::new();
        let entries = hs([OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
            vessel_id: VesselId::new(1),
            berthing_position: SpacePosition::new(50),
            berthing_time: TimePoint::new(0),
        })]);
        let quay = SpaceLength::new(1_000);
        assert!(Problem::new(vessels, maints, entries, quay).is_ok());
    }

    #[test]
    fn test_err_missing_vessel() {
        let vessels = hs([vessel::<i64>(1, 100, 10, 0, 0, window(0, 1_000))]);
        let maints: HashSet<MaintenanceSpec<i64>> = HashSet::new();
        let entries = hs([OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
            vessel_id: VesselId::new(2), // not present
            berthing_position: SpacePosition::new(50),
            berthing_time: TimePoint::new(0),
        })]);
        let quay = SpaceLength::new(1_000);
        let err = Problem::new(vessels, maints, entries, quay).unwrap_err();
        matches!(err, ProblemError::MissingVessel(_));
    }

    #[test]
    fn test_err_vessel_out_of_bounds() {
        let vessels = hs([vessel::<i64>(1, 200, 10, 0, 0, window(0, 1_000))]);
        let maints: HashSet<MaintenanceSpec<i64>> = HashSet::new();
        let entries = hs([OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
            vessel_id: VesselId::new(1),
            berthing_position: SpacePosition::new(900),
            berthing_time: TimePoint::new(0),
        })]);
        let quay = SpaceLength::new(1_000);
        let err = Problem::new(vessels, maints, entries, quay).unwrap_err();
        matches!(err, ProblemError::OccupantOutOfBounds(_));
    }

    #[test]
    fn test_ok_touching_in_time_same_space() {
        let vessels = hs([
            vessel::<i64>(1, 100, 10, 0, 0, window(0, 1_000)),
            vessel::<i64>(2, 100, 10, 0, 0, window(0, 1_000)),
        ]);
        let maints: HashSet<MaintenanceSpec<i64>> = HashSet::new();
        let entries = hs([
            OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
                vessel_id: VesselId::new(1),
                berthing_position: SpacePosition::new(100),
                berthing_time: TimePoint::new(0),
            }),
            OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
                vessel_id: VesselId::new(2),
                berthing_position: SpacePosition::new(100),
                berthing_time: TimePoint::new(10),
            }),
        ]);
        let quay = SpaceLength::new(1_000);
        assert!(Problem::new(vessels, maints, entries, quay).is_ok());
    }

    #[test]
    fn test_ok_touching_in_space_same_time() {
        let vessels = hs([
            vessel::<i64>(1, 100, 10, 0, 0, window(0, 1_000)),
            vessel::<i64>(2, 100, 10, 0, 0, window(0, 1_000)),
        ]);
        let maints: HashSet<MaintenanceSpec<i64>> = HashSet::new();
        let entries = hs([
            OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
                vessel_id: VesselId::new(1),
                berthing_position: SpacePosition::new(100),
                berthing_time: TimePoint::new(0),
            }),
            OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
                vessel_id: VesselId::new(2),
                berthing_position: SpacePosition::new(200),
                berthing_time: TimePoint::new(0),
            }),
        ]);
        let quay = SpaceLength::new(1_000);
        assert!(Problem::new(vessels, maints, entries, quay).is_ok());
    }

    #[test]
    fn test_err_overlap_in_time_and_space() {
        let vessels = hs([
            vessel::<i64>(1, 150, 10, 0, 0, window(0, 1_000)),
            vessel::<i64>(2, 150, 10, 0, 0, window(0, 1_000)),
        ]);
        let maints: HashSet<MaintenanceSpec<i64>> = HashSet::new();
        let entries = hs([
            OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
                vessel_id: VesselId::new(1),
                berthing_position: SpacePosition::new(100),
                berthing_time: TimePoint::new(0),
            }),
            OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
                vessel_id: VesselId::new(2),
                berthing_position: SpacePosition::new(200),
                berthing_time: TimePoint::new(0),
            }),
        ]);
        let quay = SpaceLength::new(1_000);
        let err = Problem::new(vessels, maints, entries, quay).unwrap_err();
        matches!(err, ProblemError::OccupancyOverlap(_));
    }

    #[test]
    fn test_ok_overlap_in_time_only() {
        let vessels = hs([
            vessel::<i64>(1, 100, 10, 0, 0, window(0, 1_000)),
            vessel::<i64>(2, 100, 10, 0, 0, window(0, 1_000)),
        ]);
        let maints: HashSet<MaintenanceSpec<i64>> = HashSet::new();
        let entries = hs([
            OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
                vessel_id: VesselId::new(1),
                berthing_position: SpacePosition::new(100),
                berthing_time: TimePoint::new(0),
            }),
            OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
                vessel_id: VesselId::new(2),
                berthing_position: SpacePosition::new(400),
                berthing_time: TimePoint::new(5),
            }),
        ]);
        let quay = SpaceLength::new(1_000);
        assert!(Problem::new(vessels, maints, entries, quay).is_ok());
    }

    #[test]
    fn test_ok_overlap_in_space_only() {
        let vessels = hs([
            vessel::<i64>(1, 100, 10, 0, 0, window(0, 1_000)),
            vessel::<i64>(2, 100, 10, 0, 0, window(0, 1_000)),
        ]);
        let maints: HashSet<MaintenanceSpec<i64>> = HashSet::new();
        let entries = hs([
            OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
                vessel_id: VesselId::new(1),
                berthing_position: SpacePosition::new(100),
                berthing_time: TimePoint::new(0),
            }),
            OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
                vessel_id: VesselId::new(2),
                berthing_position: SpacePosition::new(100),
                berthing_time: TimePoint::new(10),
            }),
        ]);
        let quay = SpaceLength::new(1_000);
        assert!(Problem::new(vessels, maints, entries, quay).is_ok());
    }

    #[test]
    fn test_ok_maintenance_within_feasible_window() {
        let vessels = hs([vessel::<i64>(1, 80, 10, 0, 0, window(0, 1_000))]);
        let maints = hs([MaintenanceSpec::new(
            MaintenanceId::new(9),
            SpacePosition::new(500),
            SpaceLength::new(50),
            TimeDelta::new(4),
            TimeInterval::new(TimePoint::new(0), TimePoint::new(20)),
        )]);
        let entries = hs([OccupancyEntry::PreAssigned(
            OccupancyAssignment::Maintenance {
                id: MaintenanceId::new(9),
                start_time: TimePoint::new(10), // ends at 14, within [0,20)
            },
        )]);
        let quay = SpaceLength::new(1_000);
        assert!(Problem::new(vessels, maints, entries, quay).is_ok());
    }

    #[test]
    fn test_err_maintenance_outside_feasible_window() {
        let vessels = hs([vessel::<i64>(1, 80, 10, 0, 0, window(0, 1_000))]);
        let maints = hs([MaintenanceSpec::new(
            MaintenanceId::new(9),
            SpacePosition::new(500),
            SpaceLength::new(50),
            TimeDelta::new(4),
            TimeInterval::new(TimePoint::new(0), TimePoint::new(12)),
        )]);
        let entries = hs([OccupancyEntry::PreAssigned(
            OccupancyAssignment::Maintenance {
                id: MaintenanceId::new(9),
                start_time: TimePoint::new(10), // would end at 14 > 12
            },
        )]);
        let quay = SpaceLength::new(1_000);
        let err = Problem::new(vessels, maints, entries, quay).unwrap_err();
        matches!(err, ProblemError::MaintenanceOutsideFeasibleTime(_));
    }

    #[test]
    fn test_err_vessel_assigned_before_arrival() {
        let vessels = hs([vessel::<i64>(1, 100, 10, 5, 0, window(0, 1_000))]);
        let maints: HashSet<MaintenanceSpec<i64>> = HashSet::new();
        let entries = hs([OccupancyEntry::PreAssigned(OccupancyAssignment::Vessel {
            vessel_id: VesselId::new(1),
            berthing_position: SpacePosition::new(100),
            berthing_time: TimePoint::new(3), // before arrival
        })]);
        let quay = SpaceLength::new(1_000);
        let err = Problem::new(vessels, maints, entries, quay).unwrap_err();
        matches!(err, ProblemError::VesselAssignedBeforeArrival(_));
    }
}
