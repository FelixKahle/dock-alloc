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

#![allow(dead_code)]

use dock_alloc_core::domain::{
    Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use num_traits::{PrimInt, Signed, Zero};
use std::fmt::Display;
use std::{
    cmp::Ordering,
    collections::{BTreeSet, HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
};

/// A unique identifier for a berthing request.
///
/// This struct wraps a `u64` to provide type safety, ensuring that request IDs are not
/// accidentally mixed with other numeric types throughout the API.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RequestId(u64);

impl RequestId {
    /// Creates a new `RequestId`.
    ///
    /// This constructor takes a `u64` value and wraps it in the `RequestId` type.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::RequestId;
    ///
    /// let request_id = RequestId::new(42);
    /// assert_eq!(request_id.value(), 42);
    /// ```
    #[inline]
    pub const fn new(id: u64) -> Self {
        RequestId(id)
    }

    /// Returns the underlying `u64` value of the ID.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::RequestId;
    ///
    /// let request_id = RequestId::new(123);
    /// assert_eq!(request_id.value(), 123);
    /// ```
    #[inline]
    pub const fn value(&self) -> u64 {
        self.0
    }
}

impl Display for RequestId {
    /// Formats the `RequestId` for display.
    ///
    /// The format is `RequestId(value)`, which is useful for logging and debugging.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::RequestId;
    ///
    /// let request_id = RequestId::new(101);
    /// assert_eq!(format!("{}", request_id), "RequestId(101)");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RequestId({})", self.0)
    }
}

impl From<u64> for RequestId {
    /// Converts a `u64` into a `RequestId`.
    ///
    /// This allows for more ergonomic creation of `RequestId` instances from primitive integers.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::RequestId;
    ///
    /// let id_from_u64: RequestId = 42.into();
    /// assert_eq!(id_from_u64.value(), 42);
    /// ```
    fn from(value: u64) -> Self {
        RequestId(value)
    }
}

/// Represents a request for a berthing space at a quay.
///
/// A `Request` encapsulates all constraints and cost parameters associated with a single
/// request's berthing needs, such as its physical length, required processing time,
/// target position, and feasible time/space windows.
#[derive(Debug, Clone, Copy)]
pub struct Request<TimeType = i64, CostType = i64>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    id: RequestId,
    length: SpaceLength,
    processing_duration: TimeDelta<TimeType>,
    target_position: SpacePosition,
    cost_per_delay: Cost<CostType>,
    cost_per_position_deviation: Cost<CostType>,
    feasible_time_window: TimeInterval<TimeType>,
    feasible_space_window: SpaceInterval,
    drop_penalty: Option<Cost<CostType>>,
}

impl<TimeType, CostType> PartialEq for Request<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<TimeType, CostType> Eq for Request<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
}

impl<TimeType, CostType> Hash for Request<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl<TimeType, CostType> PartialOrd for Request<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<TimeType, CostType> Ord for Request<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

/// An error indicating a request's feasible time window is too short.
///
/// This error occurs during `Request` creation if the duration of the `feasible_time_window`
/// is less than the required `processing_duration`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RequestTimeWindowTooShortError<TimeType: PrimInt + Signed> {
    feasible_time_window: TimeInterval<TimeType>,
    processing_duration: TimeDelta<TimeType>,
}

impl<TimeType: PrimInt + Signed> RequestTimeWindowTooShortError<TimeType> {
    /// Creates a new `RequestTimeWindowTooShortError`.
    pub fn new(
        feasible_time_window: TimeInterval<TimeType>,
        processing_duration: TimeDelta<TimeType>,
    ) -> Self {
        Self {
            feasible_time_window,
            processing_duration,
        }
    }

    /// Returns the feasible time window that was too short.
    pub fn feasible_time_window(&self) -> TimeInterval<TimeType> {
        self.feasible_time_window
    }

    /// Returns the processing duration that did not fit.
    pub fn processing_duration(&self) -> TimeDelta<TimeType> {
        self.processing_duration
    }
}
impl<TimeType: PrimInt + Signed + Display> Display for RequestTimeWindowTooShortError<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Request time window too short: feasible_time_window = {}, processing_duration = {}",
            self.feasible_time_window, self.processing_duration
        )
    }
}

/// An error indicating a request's feasible space window is too short.
///
/// This error occurs during `Request` creation if the length of the `feasible_space_window`
/// is less than the required `length` of the request.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RequestSpaceWindowTooShortError {
    feasible_space_window: SpaceInterval,
    length: SpaceLength,
}

impl RequestSpaceWindowTooShortError {
    /// Creates a new `RequestSpaceWindowTooShortError`.
    pub fn new(feasible_space_window: SpaceInterval, length: SpaceLength) -> Self {
        Self {
            feasible_space_window,
            length,
        }
    }

    /// Returns the feasible space window that was too short.
    pub fn feasible_space_window(&self) -> SpaceInterval {
        self.feasible_space_window
    }

    /// Returns the request length that did not fit.
    pub fn length(&self) -> SpaceLength {
        self.length
    }
}
impl Display for RequestSpaceWindowTooShortError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Request space window too short: feasible_space_window = {}, length = {}",
            self.feasible_space_window, self.length
        )
    }
}

/// An error that can occur during the creation of a `Request`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RequestCreationError<TimeType: PrimInt + Signed> {
    /// The feasible time window is shorter than the processing duration.
    TimeWindowTooShort(RequestTimeWindowTooShortError<TimeType>),
    /// The feasible space window is shorter than the request's length.
    SpaceWindowTooShort(RequestSpaceWindowTooShortError),
}

impl<TimeType: PrimInt + Signed + Display> Display for RequestCreationError<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TimeWindowTooShort(e) => write!(f, "{}", e),
            Self::SpaceWindowTooShort(e) => write!(f, "{}", e),
        }
    }
}

impl<TimeType: PrimInt + Signed + Display + Debug> std::error::Error
    for RequestCreationError<TimeType>
{
}

impl<TimeType, CostType> Request<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    /// Creates a new `Request` after validating its parameters.
    ///
    /// This function constructs a `Request` from its constituent parts. It performs
    /// critical validation to ensure the request is logically consistent before creation.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the request parameters are invalid:
    /// - `RequestCreationError::TimeWindowTooShort`: If the `feasible_time_window`'s
    ///   duration is less than the `processing_duration`.
    /// - `RequestCreationError::SpaceWindowTooShort`: If the `feasible_space_window`'s
    ///   length is less than the request's `length`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, TimeDelta, SpacePosition, Cost, TimeInterval, TimePoint, SpaceInterval};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let request = Request::<i64, i64>::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(3600),
    ///     SpacePosition::new(50),
    ///     Cost::new(10),
    ///     Cost::new(5),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(7200)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    ///     Some(Cost::new(1000)),
    /// );
    ///
    /// assert!(request.is_ok());
    ///
    /// // Example of a time window that is too short
    /// let bad_request = Request::<i64, i64>::new(
    ///     RequestId::new(2),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(3600),
    ///     SpacePosition::new(50),
    ///     Cost::new(10),
    ///     Cost::new(5),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(3000)), // Duration < 3600
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    ///     None,
    /// );
    ///
    /// assert!(bad_request.is_err());
    /// ```
    #[allow(clippy::too_many_arguments)]
    #[inline]
    pub fn new(
        id: RequestId,
        length: SpaceLength,
        processing_duration: TimeDelta<TimeType>,
        target_position: SpacePosition,
        cost_per_delay: Cost<CostType>,
        cost_per_position_deviation: Cost<CostType>,
        feasible_time_window: TimeInterval<TimeType>,
        feasible_space_window: SpaceInterval,
        drop_penalty: Option<Cost<CostType>>,
    ) -> Result<Self, RequestCreationError<TimeType>> {
        if feasible_time_window.duration() < processing_duration {
            return Err(RequestCreationError::TimeWindowTooShort(
                RequestTimeWindowTooShortError::new(feasible_time_window, processing_duration),
            ));
        }
        if feasible_space_window.start() + length > feasible_space_window.end() {
            return Err(RequestCreationError::SpaceWindowTooShort(
                RequestSpaceWindowTooShortError::new(feasible_space_window, length),
            ));
        }

        Ok(Request {
            id,
            length,
            processing_duration,
            target_position,
            cost_per_delay,
            cost_per_position_deviation,
            feasible_time_window,
            feasible_space_window,
            drop_penalty,
        })
    }

    /// Returns the unique identifier of the request.
    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    /// Returns the physical length of the request for this request.
    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.length
    }

    /// Returns the earliest time the request can arrive.
    ///
    /// This is defined as the start of the `feasible_time_window`.
    #[inline]
    pub fn arrival_time(&self) -> TimePoint<TimeType> {
        self.feasible_time_window.start()
    }

    /// Returns the required time for processing (berthing duration).
    #[inline]
    pub fn processing_duration(&self) -> TimeDelta<TimeType> {
        self.processing_duration
    }

    /// Returns the preferred berthing position for the request.
    #[inline]
    pub fn target_position(&self) -> SpacePosition {
        self.target_position
    }

    /// Returns the cost incurred for each unit of time the request waits after arrival.
    #[inline]
    pub fn cost_per_delay(&self) -> Cost<CostType> {
        self.cost_per_delay
    }

    /// Returns the cost incurred for each unit of distance from the target position.
    #[inline]
    pub fn cost_per_position_deviation(&self) -> Cost<CostType> {
        self.cost_per_position_deviation
    }

    /// Returns the time interval within which the request must be processed.
    #[inline]
    pub fn feasible_time_window(&self) -> TimeInterval<TimeType> {
        self.feasible_time_window
    }

    /// Returns the space interval along the quay where the request can be berthed.
    #[inline]
    pub fn feasible_space_window(&self) -> SpaceInterval {
        self.feasible_space_window
    }

    /// Returns the penalty cost if this request is not assigned (dropped), if applicable.
    #[inline]
    pub fn drop_penalty(&self) -> Option<Cost<CostType>> {
        self.drop_penalty
    }

    /// Returns `true` if the request can be dropped (i.e., has a drop penalty).
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, TimeDelta, SpacePosition, Cost, TimeInterval, TimePoint, SpaceInterval};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let droppable_request = Request::<i64, i64>::new(RequestId::new(1), SpaceLength::new(100), TimeDelta::new(10), SpacePosition::new(0), Cost::new(1), Cost::new(1), TimeInterval::new(TimePoint::new(0), TimePoint::new(100)), SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)), Some(Cost::new(1000))).unwrap();
    /// let mandatory_request = Request::<i64, i64>::new(RequestId::new(2), SpaceLength::new(100), TimeDelta::new(10), SpacePosition::new(0), Cost::new(1), Cost::new(1), TimeInterval::new(TimePoint::new(0), TimePoint::new(100)), SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)), None).unwrap();
    ///
    /// assert!(droppable_request.is_droppable());
    /// assert!(!mandatory_request.is_droppable());
    /// ```
    #[inline]
    pub fn is_droppable(&self) -> bool {
        self.drop_penalty.is_some()
    }
}

impl<TimeType, CostType> Request<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed + TryFrom<TimeType>,
{
    /// Calculates the total cost for a given waiting time.
    ///
    /// The cost is calculated as `waiting_time` * `cost_per_delay`.
    ///
    /// # Panics
    ///
    /// Panics if the numeric value of `waiting_time` cannot be converted into `CostType`.
    /// This may happen if `TimeType` is a larger integer type than `CostType`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, TimeDelta, SpacePosition, Cost, TimeInterval, TimePoint, SpaceInterval};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let request = Request::<i64, i64>::new(RequestId::new(1), SpaceLength::new(100), TimeDelta::new(3600), SpacePosition::new(50), Cost::new(10), Cost::new(5), TimeInterval::new(TimePoint::new(0), TimePoint::new(7200)), SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)), None).unwrap();
    /// let waiting_time = TimeDelta::new(15); // 15 time units of waiting
    ///
    /// // Cost = 15 * 10 = 150
    /// assert_eq!(request.waiting_cost(waiting_time), Cost::new(150));
    /// ```
    #[inline]
    pub fn waiting_cost(&self, waiting_time: TimeDelta<TimeType>) -> Cost<CostType> {
        let scalar: CostType = CostType::try_from(waiting_time.value())
            .ok()
            .expect("waiting time does not fit in CostType");
        self.cost_per_delay * scalar
    }
}

impl<TimeType, CostType> Request<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed + TryFrom<usize>,
{
    /// Calculates the total cost for a given deviation from the target position.
    ///
    /// The cost is calculated as `deviation` * `cost_per_position_deviation`.
    ///
    /// # Panics
    ///
    /// Panics if the numeric value of the `deviation` `SpaceLength` cannot be
    /// converted into `CostType`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, TimeDelta, SpacePosition, Cost, TimeInterval, TimePoint, SpaceInterval};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let request = Request::<i64, i64>::new(RequestId::new(1), SpaceLength::new(100), TimeDelta::new(3600), SpacePosition::new(50), Cost::new(10), Cost::new(5), TimeInterval::new(TimePoint::new(0), TimePoint::new(7200)), SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)), None).unwrap();
    /// let deviation = SpaceLength::new(20); // 20 units of distance from target
    ///
    /// // Cost = 20 * 5 = 100
    /// assert_eq!(request.target_position_deviation_cost(deviation), Cost::new(100));
    /// ```
    #[inline]
    pub fn target_position_deviation_cost(&self, deviation: SpaceLength) -> Cost<CostType> {
        let scalar: CostType = CostType::try_from(deviation.value())
            .ok()
            .expect("deviation does not fit in CostType");
        self.cost_per_position_deviation * scalar
    }
}

impl<TimeType, CostType> Display for Request<TimeType, CostType>
where
    TimeType: PrimInt + Signed + Display,
    CostType: PrimInt + Signed + Display,
{
    /// Formats the `Request` for display.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Request(id: {}, length: {}, arrival_time: {}, processing_duration: {}, target_position: {}, cost_per_delay: {}, cost_per_position_deviation: {})",
            self.id,
            self.length,
            self.arrival_time(),
            self.processing_duration,
            self.target_position,
            self.cost_per_delay,
            self.cost_per_position_deviation
        )
    }
}

/// Represents a concrete assignment of a request to a time and place.
///
/// An `Assignment` links a `RequestId` to a specific `berthing_time` and `berthing_position`,
/// representing a fixed allocation on the quay.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Assignment<TimeType = i64>
where
    TimeType: PrimInt + Signed,
{
    request_id: RequestId,
    berthing_position: SpacePosition,
    berthing_time: TimePoint<TimeType>,
}

impl<TimeType> Assignment<TimeType>
where
    TimeType: PrimInt + Signed,
{
    /// Creates a new `Assignment`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, TimePoint};
    /// use dock_alloc_model::{Assignment, RequestId};
    ///
    /// let assignment = Assignment::new(
    ///     RequestId::new(1),
    ///     SpacePosition::new(100),
    ///     TimePoint::new(1622547800i64)
    /// );
    ///
    /// assert_eq!(assignment.request_id().value(), 1);
    /// assert_eq!(assignment.berthing_position().value(), 100);
    /// ```
    #[inline]
    pub fn new(
        request_id: RequestId,
        berthing_position: SpacePosition,
        berthing_time: TimePoint<TimeType>,
    ) -> Self {
        Self {
            request_id,
            berthing_position,
            berthing_time,
        }
    }

    /// Returns the ID of the request being assigned.
    #[inline]
    pub fn request_id(&self) -> RequestId {
        self.request_id
    }

    /// Returns the assigned starting position on the quay.
    #[inline]
    pub fn berthing_position(&self) -> SpacePosition {
        self.berthing_position
    }

    /// Returns the assigned start time for berthing.
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment(request_id: {}, berthing_position: {}, berthing_time: {})",
            self.request_id, self.berthing_position, self.berthing_time
        )
    }
}

/// Represents the status of a request within a `Problem` definition.
///
/// A request can either be `Unassigned`, meaning a solver is free to find an
/// assignment for it, or `PreAssigned`, meaning it has a fixed assignment
/// that the solver must respect.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProblemEntry<TimeType = i64>
where
    TimeType: PrimInt + Signed,
{
    /// The request needs to be scheduled by a solver.
    Unassigned(RequestId),
    /// The request has a fixed, mandatory assignment.
    PreAssigned(Assignment<TimeType>),
}

impl<TimeType> Display for ProblemEntry<TimeType>
where
    TimeType: PrimInt + Signed + Display,
{
    /// Formats the `ProblemEntry` for display.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProblemEntry::Unassigned(request_id) => {
                write!(f, "Unassigned(request_id: {})", request_id)
            }
            ProblemEntry::PreAssigned(assignment) => write!(f, "PreAssigned({})", assignment),
        }
    }
}

/// An error indicating that a `ProblemEntry` refers to a non-existent `RequestId`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MissingRequestError(RequestId);
impl Display for MissingRequestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Missing request with ID: {}", self.0)
    }
}

impl std::error::Error for MissingRequestError {}

impl From<RequestId> for MissingRequestError {
    #[inline]
    fn from(request_id: RequestId) -> Self {
        MissingRequestError(request_id)
    }
}

impl MissingRequestError {
    /// Creates a new `MissingRequestError`.
    #[inline]
    pub fn new(request_id: RequestId) -> Self {
        MissingRequestError(request_id)
    }

    /// Returns the ID of the request that was missing.
    #[inline]
    pub fn request_id(&self) -> RequestId {
        self.0
    }
}

/// An error indicating that a pre-assignment places a request outside the quay's boundaries.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RequestOutOfBoundsError {
    request_id: RequestId,
    end_pos: SpacePosition,
    quay_length: SpaceLength,
}

impl Display for RequestOutOfBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Request with ID {} is out of bounds: end position {} exceeds quay length {}",
            self.request_id, self.end_pos, self.quay_length
        )
    }
}

impl std::error::Error for RequestOutOfBoundsError {}

impl RequestOutOfBoundsError {
    /// Creates a new `RequestOutOfBoundsError`.
    #[inline]
    pub fn new(request_id: RequestId, end_pos: SpacePosition, quay_length: SpaceLength) -> Self {
        Self {
            request_id,
            end_pos,
            quay_length,
        }
    }

    /// Returns the ID of the out-of-bounds request.
    pub fn request_id(&self) -> RequestId {
        self.request_id
    }

    /// Returns the calculated end position that was out of bounds.
    pub fn end_pos(&self) -> SpacePosition {
        self.end_pos
    }

    /// Returns the total length of the quay.
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }
}

/// A rectangle representing an assigned request in time and space.
///
/// This is a utility struct used for overlap detection, representing the time-space
/// area occupied by an assigned request.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RequestRect<TimeType: PrimInt + Signed> {
    id: RequestId,
    time_interval: TimeInterval<TimeType>,
    space_interval: SpaceInterval,
}

impl<TimeType: PrimInt + Signed> RequestRect<TimeType> {
    /// Creates a new `RequestRect`.
    pub fn new(
        id: RequestId,
        time_interval: TimeInterval<TimeType>,
        space_interval: SpaceInterval,
    ) -> Self {
        Self {
            id,
            time_interval,
            space_interval,
        }
    }

    /// Returns the ID of the request associated with this rectangle.
    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    /// Returns the time interval occupied by the request.
    pub fn time_interval(&self) -> &TimeInterval<TimeType> {
        &self.time_interval
    }

    /// Returns the space interval occupied by the request.
    pub fn space_interval(&self) -> &SpaceInterval {
        &self.space_interval
    }
}

impl<TimeType: PrimInt + Signed + Display> Display for RequestRect<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "RequestRect(id: {}, time_interval: {}, space_interval: {})",
            self.id, self.time_interval, self.space_interval
        )
    }
}

/// An error indicating that two assigned requests overlap in both time and space.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RequestOverlapError<TimeType: PrimInt + Signed> {
    a: RequestRect<TimeType>,
    b: RequestRect<TimeType>,
}

impl<TimeType: PrimInt + Signed + Display> Display for RequestOverlapError<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RequestOverlapError between {} and {}", self.a, self.b)
    }
}

impl<TimeType: PrimInt + Signed> RequestOverlapError<TimeType> {
    /// Creates a new `RequestOverlapError`.
    #[inline]
    pub fn new(a: RequestRect<TimeType>, b: RequestRect<TimeType>) -> Self {
        Self { a, b }
    }

    /// Returns the first of the two overlapping requests.
    pub fn a(&self) -> &RequestRect<TimeType> {
        &self.a
    }

    /// Returns the second of the two overlapping requests.
    pub fn b(&self) -> &RequestRect<TimeType> {
        &self.b
    }
}

/// An error indicating an assignment violates the request's feasible time window.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AssignmentViolatesTimeWindow<TimeType: PrimInt + Signed> {
    request_id: RequestId,
    assigned: TimeInterval<TimeType>,
    feasible: TimeInterval<TimeType>,
}

impl<TimeType: PrimInt + Signed + Display> Display for AssignmentViolatesTimeWindow<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Pre-assignment for request {} has time {} outside feasible {}",
            self.request_id, self.assigned, self.feasible
        )
    }
}

impl<TimeType: PrimInt + Signed> AssignmentViolatesTimeWindow<TimeType> {
    /// Creates a new `AssignmentViolatesTimeWindow` error.
    pub fn new(
        request_id: RequestId,
        assigned: TimeInterval<TimeType>,
        feasible: TimeInterval<TimeType>,
    ) -> Self {
        Self {
            request_id,
            assigned,
            feasible,
        }
    }
}

/// An error indicating an assignment violates the request's feasible space window.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AssignmentViolatesSpaceWindow {
    request_id: RequestId,
    assigned: SpaceInterval,
    feasible: SpaceInterval,
}

impl Display for AssignmentViolatesSpaceWindow {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Pre-assignment for request {} has space {} outside feasible {}",
            self.request_id, self.assigned, self.feasible
        )
    }
}

impl AssignmentViolatesSpaceWindow {
    /// Creates a new `AssignmentViolatesSpaceWindow` error.
    pub fn new(request_id: RequestId, assigned: SpaceInterval, feasible: SpaceInterval) -> Self {
        Self {
            request_id,
            assigned,
            feasible,
        }
    }
}

/// An error that can occur during the creation of a `Problem`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProblemError<TimeType: PrimInt + Signed> {
    /// An entry refers to a `RequestId` not present in the set of requests.
    MissingRequest(MissingRequestError),
    /// A pre-assigned request is placed outside the quay's physical boundaries.
    RequestOutOfBounds(RequestOutOfBoundsError),
    /// Two or more pre-assigned requests overlap in time and space.
    RequestOverlap(RequestOverlapError<TimeType>),
    /// A pre-assigned request's time interval is outside its own feasible time window.
    AssignmentViolatesTimeWindow(AssignmentViolatesTimeWindow<TimeType>),
    /// A pre-assigned request's space interval is outside its own feasible space window.
    AssignmentViolatesSpaceWindow(AssignmentViolatesSpaceWindow),
}

impl<TimeType: PrimInt + Signed + Display> Display for ProblemError<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProblemError::MissingRequest(err) => write!(f, "{}", err),
            ProblemError::RequestOutOfBounds(err) => write!(f, "{}", err),
            ProblemError::RequestOverlap(err) => write!(f, "{}", err),
            ProblemError::AssignmentViolatesTimeWindow(err) => write!(f, "{}", err),
            ProblemError::AssignmentViolatesSpaceWindow(err) => write!(f, "{}", err),
        }
    }
}

impl<TimeType: PrimInt + Signed + Display + Debug> std::error::Error for ProblemError<TimeType> {}

#[inline]
fn check_space_overlaps<T: PrimInt + Signed>(
    rects: &[RequestRect<T>],
) -> Result<(), RequestOverlapError<T>> {
    if rects.is_empty() {
        return Ok(());
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum EventKind {
        Start,
        End,
    }
    #[derive(Clone, Copy)]
    struct Event<U: PrimInt + Signed> {
        time: TimePoint<U>,
        kind: EventKind,
        rect_index: usize,
    }

    let mut events: Vec<Event<T>> = Vec::with_capacity(rects.len() * 2);
    for (i, r) in rects.iter().enumerate() {
        events.push(Event {
            time: r.time_interval().start(),
            kind: EventKind::Start,
            rect_index: i,
        });
        events.push(Event {
            time: r.time_interval().end(),
            kind: EventKind::End,
            rect_index: i,
        });
    }

    // Sort by time; on ties, process End before Start so touching-in-time is allowed.
    events.sort_by(|a, b| {
        a.time.cmp(&b.time).then_with(|| match (a.kind, b.kind) {
            (EventKind::End, EventKind::Start) => Ordering::Less,
            (EventKind::Start, EventKind::End) => Ordering::Greater,
            _ => Ordering::Equal,
        })
    });

    let mut active: BTreeSet<(SpacePosition, usize)> = BTreeSet::new();

    #[inline]
    fn intervals_overlap(a: &SpaceInterval, b: &SpaceInterval) -> bool {
        // Half-open [start, end): touching in space is allowed.
        a.start() < b.end() && b.start() < a.end()
    }

    for e in events {
        let rect = rects[e.rect_index];
        match e.kind {
            EventKind::Start => {
                let key = (rect.space_interval().start(), e.rect_index);

                // Check predecessor in space order.
                if let Some(&(_, pred_idx)) = active.range(..key).next_back() {
                    let pred = rects[pred_idx];
                    if intervals_overlap(pred.space_interval(), rect.space_interval()) {
                        return Err(RequestOverlapError::new(pred, rect));
                    }
                }
                // Check successor in space order.
                if let Some(&(_, succ_idx)) = active.range(key..).next() {
                    let succ = rects[succ_idx];
                    if intervals_overlap(succ.space_interval(), rect.space_interval()) {
                        return Err(RequestOverlapError::new(succ, rect));
                    }
                }
                active.insert(key);
            }
            EventKind::End => {
                active.remove(&(rect.space_interval().start(), e.rect_index));
            }
        }
    }

    Ok(())
}

/// Defines a complete, validated berth allocation problem instance.
///
/// A `Problem` consists of a set of `Request`s, their status as `ProblemEntry`s
/// (either unassigned or pre-assigned), and the total `quay_length`. This struct
/// is the primary input for a solver.
#[derive(Debug, Clone)]
pub struct Problem<TimeType = i64, CostType = i64>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    requests: HashSet<Request<TimeType, CostType>>,
    entries: HashSet<ProblemEntry<TimeType>>,
    quay_length: SpaceLength,
}

impl<TimeType, CostType> Problem<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    /// Creates a new `Problem` after performing comprehensive validation.
    ///
    /// This constructor is the safe way to new a `Problem`. It ensures that all
    /// pre-assignments are valid and do not conflict with each other or with the
    /// problem's constraints. It uses a sweep-line algorithm to efficiently check for
    /// overlaps among pre-assigned requests.
    ///
    /// # Errors
    ///
    /// This function returns an error if the problem definition is invalid in any way:
    /// - `ProblemError::MissingRequest`: If an entry in `entries` refers to a `RequestId` that
    ///   is not found in the `requests` set.
    /// - `ProblemError::AssignmentViolatesTimeWindow`: If a pre-assignment's time allocation
    ///   falls outside the request's own `feasible_time_window`.
    /// - `ProblemError::AssignmentViolatesSpaceWindow`: If a pre-assignment's space allocation
    ///   falls outside the request's own `feasible_space_window`.
    /// - `ProblemError::RequestOutOfBounds`: If a pre-assignment would cause a request to
    ///   extend beyond the `quay_length`.
    /// - `ProblemError::RequestOverlap`: If any two pre-assignments overlap in both time
    ///   and space, which is physically impossible.
    pub fn new(
        requests: HashSet<Request<TimeType, CostType>>,
        entries: HashSet<ProblemEntry<TimeType>>,
        quay_length: SpaceLength,
    ) -> Result<Self, ProblemError<TimeType>> {
        let request_map: HashMap<RequestId, &Request<TimeType, CostType>> = requests
            .iter()
            .map(|request| (request.id(), request))
            .collect();

        // Validate that all Unassigned IDs exist in `requests`.
        for entry in &entries {
            if let ProblemEntry::Unassigned(id) = *entry
                && !request_map.contains_key(&id)
            {
                return Err(ProblemError::MissingRequest(MissingRequestError::new(id)));
            }
        }

        let quay_end_position: SpacePosition = SpacePosition::new(quay_length.value());

        // Build and validate rectangles for all pre-assigned entries.
        let pre_assigned_rects: Vec<RequestRect<TimeType>> = entries
            .iter()
            .filter_map(|entry| match entry {
                ProblemEntry::PreAssigned(assignment) => Some(assignment),
                _ => None,
            })
            .map(|assignment| {
                let request_id = assignment.request_id();
                let request = *request_map.get(&request_id).ok_or_else(|| {
                    ProblemError::MissingRequest(MissingRequestError::new(request_id))
                })?;

                // Time-window validation
                let berthing_time = assignment.berthing_time();
                let departure_time = berthing_time + request.processing_duration();
                let assigned_time_interval = TimeInterval::new(berthing_time, departure_time);
                let feasible_time = request.feasible_time_window();
                if !(berthing_time >= feasible_time.start()
                    && departure_time <= feasible_time.end())
                {
                    return Err(ProblemError::AssignmentViolatesTimeWindow(
                        AssignmentViolatesTimeWindow::new(
                            request_id,
                            assigned_time_interval,
                            feasible_time,
                        ),
                    ));
                }

                // Space/window and quay-bound validation
                let berthing_position = assignment.berthing_position();
                let end_position = berthing_position + request.length();
                if end_position > quay_end_position {
                    return Err(ProblemError::RequestOutOfBounds(
                        RequestOutOfBoundsError::new(request_id, end_position, quay_length),
                    ));
                }
                let assigned_space_interval = SpaceInterval::new(berthing_position, end_position);
                let feasible_space = request.feasible_space_window();
                if !(berthing_position >= feasible_space.start()
                    && end_position <= feasible_space.end())
                {
                    return Err(ProblemError::AssignmentViolatesSpaceWindow(
                        AssignmentViolatesSpaceWindow::new(
                            request_id,
                            assigned_space_interval,
                            feasible_space,
                        ),
                    ));
                }

                Ok(RequestRect::new(
                    request_id,
                    assigned_time_interval,
                    assigned_space_interval,
                ))
            })
            .collect::<Result<_, ProblemError<TimeType>>>()?;

        // Check overlaps among pre-assigned rectangles (time-sweep + space-neighbor check).
        if !pre_assigned_rects.is_empty() {
            check_space_overlaps(&pre_assigned_rects).map_err(ProblemError::RequestOverlap)?;
        }

        Ok(Problem {
            requests,
            entries,
            quay_length,
        })
    }

    /// Returns the total physical length of the quay.
    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    /// Returns a reference to the set of all requests in the problem.
    #[inline]
    pub fn requests(&self) -> &HashSet<Request<TimeType, CostType>> {
        &self.requests
    }

    /// Returns a reference to the set of all problem entries.
    #[inline]
    pub fn entries(&self) -> &HashSet<ProblemEntry<TimeType>> {
        &self.entries
    }

    /// Returns the total number of requests in the problem.
    #[inline]
    pub fn request_len(&self) -> usize {
        self.requests.len()
    }
}

/// A type alias for the most common problem definition using `i64` for time and cost.
pub type BerthAllocationProblem = Problem<i64, i64>;

/// Represents a solver's decision for a single request.
///
/// A decision can either be to `Assign` the request to a specific time and place,
/// or to `Drop` it if the request is droppable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Decision<TimeType = i64>
where
    TimeType: PrimInt + Signed,
{
    /// Assign the request to a specific time and position.
    Assign(Assignment<TimeType>),
    /// Drop the request (only valid for droppable requests).
    Drop(RequestId),
}

impl<T: PrimInt + Signed> From<Assignment<T>> for Decision<T> {
    fn from(a: Assignment<T>) -> Self {
        Decision::Assign(a)
    }
}

impl<TimeType> Decision<TimeType>
where
    TimeType: PrimInt + Signed,
{
    /// Returns the `RequestId` associated with this decision.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpacePosition, TimePoint};
    /// use dock_alloc_model::{Decision, Assignment, RequestId};
    ///
    /// let assign_decision: Decision<i64> = Decision::Assign(Assignment::new(
    ///     RequestId::new(1),
    ///     SpacePosition::new(100),
    ///     TimePoint::new(1000i64)
    /// ));
    /// let drop_decision: Decision<i64> = Decision::Drop(RequestId::new(2));
    ///
    /// assert_eq!(assign_decision.request_id(), RequestId::new(1));
    /// assert_eq!(drop_decision.request_id(), RequestId::new(2));
    /// ```
    #[inline]
    pub fn request_id(&self) -> RequestId {
        match *self {
            Decision::Assign(assignment) => assignment.request_id(),
            Decision::Drop(request_id) => request_id,
        }
    }
}

/// An error indicating that a solver's decision for a pre-assigned request differs from its fixed assignment.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PreassignedChangedError<TimeType: PrimInt + Signed> {
    request_id: RequestId,
    expected: (TimePoint<TimeType>, SpacePosition),
    actual: (TimePoint<TimeType>, SpacePosition),
}

impl<TimeType: PrimInt + Signed> PreassignedChangedError<TimeType> {
    /// Creates a new `PreassignedChangedError`.
    pub fn new(
        request_id: RequestId,
        expected: (TimePoint<TimeType>, SpacePosition),
        actual: (TimePoint<TimeType>, SpacePosition),
    ) -> Self {
        Self {
            request_id,
            expected,
            actual,
        }
    }

    /// Returns the ID of the request whose pre-assignment was changed.
    pub fn request_id(&self) -> RequestId {
        self.request_id
    }

    /// Returns the expected (time, position) tuple.
    pub fn expected(&self) -> &(TimePoint<TimeType>, SpacePosition) {
        &self.expected
    }

    /// Returns the actual (time, position) tuple provided by the solver.
    pub fn actual(&self) -> &(TimePoint<TimeType>, SpacePosition) {
        &self.actual
    }
}

impl<TimeType: PrimInt + Signed + Display> Display for PreassignedChangedError<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Pre-assignment for request {} changed: expected position {} at time {}, got position {} at time {}",
            self.request_id, self.expected.1, self.expected.0, self.actual.1, self.actual.0
        )
    }
}

/// An error that can occur during the validation and newing of a `Solution`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolutionError<TimeType: PrimInt + Signed> {
    /// A decision was made for a `RequestId` that does not exist in the problem.
    UnknownRequest(RequestId),
    /// More than one decision was made for the same `RequestId`.
    DuplicateDecision(RequestId),
    /// An unassigned request in the problem did not have a corresponding decision.
    MissingDecision(RequestId),
    /// A solver's decision for a pre-assigned request was different from its fixed assignment.
    PreassignmentChanged(PreassignedChangedError<TimeType>),
    /// A solver's decision was to drop a request that was pre-assigned.
    PreassignedDropped(RequestId),
    /// A solver's decision was to drop a request that was not marked as droppable.
    DroppedNotDroppable(RequestId),
    /// An assignment resulted in a berthing time earlier than the request's arrival time.
    NegativeWaitingTime(RequestId),
    /// An assignment's time interval violates the request's feasible time window.
    AssignmentViolatesTimeWindow(AssignmentViolatesTimeWindow<TimeType>),
    /// An assignment's space interval violates the request's feasible space window.
    AssignmentViolatesSpaceWindow(AssignmentViolatesSpaceWindow),
    /// An assignment places a request outside the physical quay boundaries.
    RequestOutOfBounds(RequestOutOfBoundsError),
    /// Two assignments in the final solution overlap in both time and space.
    RequestOverlap(RequestOverlapError<TimeType>),
}

impl<TimeType: PrimInt + Signed + Display> Display for SolutionError<TimeType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use SolutionError::*;
        match self {
            UnknownRequest(id) => write!(f, "Decision references unknown request {}", id),
            DuplicateDecision(id) => write!(f, "Duplicate decision for request {}", id),
            MissingDecision(id) => write!(f, "Missing decision for unassigned request {}", id),
            PreassignmentChanged(err) => write!(f, "{}", err),
            PreassignedDropped(id) => write!(f, "Pre-assigned request {} cannot be dropped", id),
            DroppedNotDroppable(id) => write!(f, "Request {} is not droppable", id),
            NegativeWaitingTime(id) => write!(f, "Waiting time would be negative for {}", id),
            AssignmentViolatesTimeWindow(err) => write!(f, "{}", err),
            AssignmentViolatesSpaceWindow(err) => write!(f, "{}", err),
            RequestOutOfBounds(err) => write!(f, "{}", err),
            RequestOverlap(err) => write!(f, "{}", err),
        }
    }
}

impl<TimeType: PrimInt + Signed + Display + Debug> std::error::Error for SolutionError<TimeType> {}

/// Contains aggregated statistics about a `Solution`.
///
/// This includes the total cost and other key performance indicators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SolutionStats<TimeType = i64, CostType = i64>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    total_cost: Cost<CostType>,
    total_waiting_time: TimeDelta<TimeType>,
    total_target_position_deviation: SpaceLength,
    total_dropped_requests: usize,
}

impl<TimeType, CostType> SolutionStats<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    /// Returns the total cost of the solution.
    ///
    /// This cost is the sum of all waiting costs, position deviation costs, and drop penalties.
    #[inline]
    pub fn total_cost(&self) -> Cost<CostType> {
        self.total_cost
    }

    /// Returns the sum of waiting times for all assigned requests.
    #[inline]
    pub fn total_waiting_time(&self) -> TimeDelta<TimeType> {
        self.total_waiting_time
    }

    /// Returns the sum of absolute deviations from target positions for all assigned requests.
    #[inline]
    pub fn total_target_position_deviation(&self) -> SpaceLength {
        self.total_target_position_deviation
    }

    /// Returns the total number of requests that were dropped.
    #[inline]
    pub fn total_dropped_requests(&self) -> usize {
        self.total_dropped_requests
    }
}

/// Represents a complete, validated solution to a `Problem`.
///
/// A `Solution` contains the set of `Decision`s for each request and the calculated
/// `SolutionStats`. It can only be constructed via the `new` function, which
/// ensures the solution is valid and consistent with the problem definition.
#[derive(Debug, Clone)]
pub struct Solution<TimeType = i64, CostType = i64>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed,
{
    decisions: HashMap<RequestId, Decision<TimeType>>,
    stats: SolutionStats<TimeType, CostType>,
}

impl<TimeType, CostType> Solution<TimeType, CostType>
where
    TimeType: PrimInt + Signed,
    CostType: PrimInt + Signed + TryFrom<TimeType> + TryFrom<usize>,
{
    /// Validates a set of `Decision`s against a `Problem` and news a `Solution`.
    ///
    /// This is the primary way to create a `Solution`. It performs an exhaustive set of
    /// checks to ensure that the provided decisions constitute a feasible and valid solution
    /// to the given problem. If validation succeeds, it calculates solution statistics and
    /// returns the `Solution`.
    ///
    /// # Errors
    ///
    /// Returns `Err` if any of the validation checks fail. See `SolutionError` for a
    /// complete list of possible failures.
    pub fn new(
        problem: &Problem<TimeType, CostType>,
        decisions: impl IntoIterator<Item = Decision<TimeType>>,
    ) -> Result<Self, SolutionError<TimeType>> {
        let request_map: HashMap<RequestId, &Request<TimeType, CostType>> = problem
            .requests()
            .iter()
            .map(|req| (req.id(), req))
            .collect();

        // Partition problem entries.
        let mut preassigned_map: HashMap<RequestId, Assignment<TimeType>> = HashMap::new();
        let mut unassigned_set: HashSet<RequestId> = HashSet::new();
        for entry in problem.entries() {
            match *entry {
                ProblemEntry::PreAssigned(a) => {
                    preassigned_map.insert(a.request_id(), a);
                }
                ProblemEntry::Unassigned(id) => {
                    unassigned_set.insert(id);
                }
            }
        }

        let mut seen_ids: HashSet<RequestId> = HashSet::new();
        let mut decisions_map: HashMap<RequestId, Decision<TimeType>> = HashMap::new();

        // Validate incoming decisions and normalize into a map.
        for decision in decisions {
            let request_id = decision.request_id();
            if !request_map.contains_key(&request_id) {
                return Err(SolutionError::UnknownRequest(request_id));
            }
            if !seen_ids.insert(request_id) {
                return Err(SolutionError::DuplicateDecision(request_id));
            }

            match decision {
                Decision::Assign(a) => {
                    if let Some(exp) = preassigned_map.get(&request_id)
                        && (exp.berthing_position() != a.berthing_position()
                            || exp.berthing_time() != a.berthing_time())
                    {
                        return Err(SolutionError::PreassignmentChanged(
                            PreassignedChangedError::new(
                                request_id,
                                (exp.berthing_time(), exp.berthing_position()),
                                (a.berthing_time(), a.berthing_position()),
                            ),
                        ));
                    }
                    decisions_map.insert(request_id, Decision::Assign(a));
                }
                Decision::Drop(id) => {
                    if preassigned_map.contains_key(&id) {
                        return Err(SolutionError::PreassignedDropped(id));
                    }
                    let req = request_map[&id];
                    if !req.is_droppable() {
                        return Err(SolutionError::DroppedNotDroppable(id));
                    }
                    decisions_map.insert(request_id, Decision::Drop(id));
                }
            }
        }

        // Ensure all Unassigned have a decision.
        for &id in &unassigned_set {
            if !seen_ids.contains(&id) {
                return Err(SolutionError::MissingDecision(id));
            }
        }

        // Ensure pre-assigned are present, even if not explicitly provided.
        for (&id, &assign) in &preassigned_map {
            decisions_map.entry(id).or_insert(Decision::Assign(assign));
        }

        // Collect final assignments for validation/costing.
        let mut final_assignments: HashMap<RequestId, Assignment<TimeType>> = HashMap::new();
        for (&id, decision) in &decisions_map {
            if let Decision::Assign(a) = decision {
                final_assignments.insert(id, *a);
            }
        }

        let quay_end = SpacePosition::new(problem.quay_length().value());
        let mut assigned_rects: Vec<RequestRect<TimeType>> = Vec::new();
        let mut total_cost: Cost<CostType> = Cost::zero();
        let mut total_waiting_time: TimeDelta<TimeType> = TimeDelta::new(TimeType::zero());
        let mut total_position_deviation: SpaceLength = SpaceLength::new(0);

        for (&request_id, &assignment) in &final_assignments {
            let request = request_map[&request_id];

            // Time-window validation.
            let berthing_time = assignment.berthing_time();
            let departure_time = berthing_time + request.processing_duration();
            let assigned_time = TimeInterval::new(berthing_time, departure_time);
            let feasible_time = request.feasible_time_window();
            if !(berthing_time >= feasible_time.start() && departure_time <= feasible_time.end()) {
                return Err(SolutionError::AssignmentViolatesTimeWindow(
                    AssignmentViolatesTimeWindow::new(request_id, assigned_time, feasible_time),
                ));
            }

            // Space and quay-bound validation.
            let berthing_position = assignment.berthing_position();
            let end_position = berthing_position + request.length();
            if end_position > quay_end {
                return Err(SolutionError::RequestOutOfBounds(
                    RequestOutOfBoundsError::new(request_id, end_position, problem.quay_length()),
                ));
            }
            let assigned_space = SpaceInterval::new(berthing_position, end_position);
            let feasible_space = request.feasible_space_window();
            if !(berthing_position >= feasible_space.start()
                && end_position <= feasible_space.end())
            {
                return Err(SolutionError::AssignmentViolatesSpaceWindow(
                    AssignmentViolatesSpaceWindow::new(request_id, assigned_space, feasible_space),
                ));
            }

            // Logical validation and costs.
            let waiting_time = berthing_time - request.arrival_time();
            if waiting_time.value() < TimeType::zero() {
                return Err(SolutionError::NegativeWaitingTime(request_id));
            }

            // Use typed absolute distance (requires SpacePosition::distance_to).
            let position_deviation = berthing_position - request.target_position();

            total_cost = total_cost
                + request.waiting_cost(waiting_time)
                + request.target_position_deviation_cost(position_deviation);
            total_waiting_time += waiting_time;
            total_position_deviation += position_deviation;

            assigned_rects.push(RequestRect::new(request_id, assigned_time, assigned_space));
        }

        // Add drop penalties.
        let mut dropped_count = 0usize;
        for (&request_id, decision) in &decisions_map {
            if let Decision::Drop(_) = decision {
                dropped_count += 1;
                if let Some(penalty) = request_map[&request_id].drop_penalty() {
                    total_cost += penalty;
                }
            }
        }

        // Overlap check for all assignments.
        if !assigned_rects.is_empty() {
            check_space_overlaps(&assigned_rects).map_err(SolutionError::RequestOverlap)?;
        }

        let stats = SolutionStats {
            total_cost,
            total_waiting_time,
            total_target_position_deviation: total_position_deviation,
            total_dropped_requests: dropped_count,
        };

        Ok(Solution {
            decisions: decisions_map,
            stats,
        })
    }

    /// Returns a reference to the solution's statistics.
    #[inline]
    pub fn stats(&self) -> &SolutionStats<TimeType, CostType> {
        &self.stats
    }

    /// Returns a map of all decisions made for the requests.
    #[inline]
    pub fn decisions(&self) -> &HashMap<RequestId, Decision<TimeType>> {
        &self.decisions
    }

    /// Returns an iterator over all assigned requests and their assignments.
    pub fn assigned(&self) -> impl Iterator<Item = (&RequestId, &Assignment<TimeType>)> {
        self.decisions
            .iter()
            .filter_map(|(id, decision)| match decision {
                Decision::Assign(assignment) => Some((id, assignment)),
                _ => None,
            })
    }

    /// Returns an iterator over all dropped request IDs.
    pub fn dropped(&self) -> impl Iterator<Item = RequestId> {
        self.decisions
            .iter()
            .filter_map(|(_, decision)| match decision {
                Decision::Drop(request_id) => Some(*request_id),
                _ => None,
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_request_id_creation() {
        let id = RequestId::new(42);
        assert_eq!(id.value(), 42);
    }
    #[test]
    fn test_request_id_display() {
        let id = RequestId::new(42);
        assert_eq!(format!("{}", id), "RequestId(42)");
    }
    #[test]
    fn test_request_id_equality() {
        let id1 = RequestId::new(42);
        let id2 = RequestId::new(42);
        assert_eq!(id1, id2);
    }
    #[test]
    fn test_request_id_from_u64() {
        let id: RequestId = 42.into();
        assert_eq!(id.value(), 42);
    }

    #[test]
    fn test_request_display() {
        let start = TimePoint::new(1_622_547_800_i64);
        let proc = TimeDelta::new(3600_i64);
        let tw = TimeInterval::new(start, start + proc); // exactly fits
        let sw = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10_000));

        let request = Request::new(
            RequestId::new(1),
            SpaceLength::new(100),
            proc,
            SpacePosition::new(50),
            Cost::new(10),
            Cost::new(5),
            tw,
            sw,
            None,
        )
        .unwrap();

        assert_eq!(
            format!("{}", request),
            "Request(id: RequestId(1), \
            length: SpaceLength(100), \
            arrival_time: TimePoint(1622547800), \
            processing_duration: TimeDelta(3600), \
            target_position: SpacePosition(50), \
            cost_per_delay: Cost(10), \
            cost_per_position_deviation: Cost(5))"
        );
    }

    #[test]
    fn test_waiting_cost() {
        let request = create_test_request::<i64>(1, 100, 3600, 0, 50);
        let waiting_time = TimeDelta::new(2);
        let cost = request.waiting_cost(waiting_time);
        assert_eq!(cost.value(), 2); // helper sets cost per unit = 1
    }

    #[test]
    fn test_target_position_deviation_cost() {
        let request = create_test_request::<i64>(1, 100, 3600, 0, 50);
        let deviation = SpaceLength::new(3);
        let cost = request.target_position_deviation_cost(deviation);
        assert_eq!(cost.value(), 3);
    }

    #[test]
    fn test_assignment_display() {
        let assignment = Assignment::new(
            RequestId::new(1),
            SpacePosition::new(100),
            TimePoint::new(1622547800),
        );
        assert_eq!(
            format!("{}", assignment),
            "Assignment(request_id: RequestId(1), \
            berthing_position: SpacePosition(100), \
            berthing_time: TimePoint(1622547800))"
        );
    }

    fn create_test_request<T: PrimInt + Signed + Debug>(
        id: u64,
        len: usize,
        proc: T,
        arr: T,
        tgt: usize,
    ) -> Request<T, i64> {
        // Feasible time window: [arr, arr+proc+100) so it always fits
        let tw = TimeInterval::new(
            TimePoint::new(arr),
            TimePoint::new(arr + proc + T::from(100).unwrap()),
        );
        // Wide feasible space window
        let sw = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10_000));
        Request::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimeDelta::new(proc),
            SpacePosition::new(tgt),
            Cost::new(1),
            Cost::new(1),
            tw,
            sw,
            None,
        )
        .unwrap()
    }

    fn create_test_pre_assignment_entry<T: PrimInt + Signed>(
        id: u64,
        x0: usize,
        t0: T,
    ) -> ProblemEntry<T> {
        ProblemEntry::PreAssigned(Assignment::new(
            RequestId::new(id),
            SpacePosition::new(x0),
            TimePoint::new(t0),
        ))
    }

    fn to_hashset<T>(items: impl IntoIterator<Item = T>) -> HashSet<T>
    where
        T: Eq + Hash,
    {
        items.into_iter().collect()
    }

    #[test]
    fn test_request_new_err_time_window_too_short() {
        let tw = TimeInterval::new(TimePoint::new(0_i64), TimePoint::new(5_i64));
        let sw = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(1_000));
        let err = Request::<i64, i64>::new(
            RequestId::new(1),
            SpaceLength::new(10),
            TimeDelta::new(10),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            tw,
            sw,
            None,
        )
        .unwrap_err();
        assert!(matches!(
            err,
            super::RequestCreationError::TimeWindowTooShort(_)
        ));
    }

    #[test]
    fn test_request_new_err_space_window_too_short() {
        let tw = TimeInterval::new(TimePoint::new(0_i64), TimePoint::new(100_i64));
        let sw = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50));
        let err = Request::<i64, i64>::new(
            RequestId::new(1),
            SpaceLength::new(60),
            TimeDelta::new(10),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            tw,
            sw,
            None,
        )
        .unwrap_err();
        assert!(matches!(
            err,
            super::RequestCreationError::SpaceWindowTooShort(_)
        ));
    }

    #[test]
    fn test_new_ok_no_entries() {
        let requests = to_hashset([create_test_request::<i64>(1, 100, 10, 0, 0)]);
        let entries = HashSet::new();
        let quay = SpaceLength::new(1_000);
        let p = Problem::new(requests, entries, quay);
        assert!(p.is_ok());
    }

    #[test]
    fn new_ok_single_preassignment_in_bounds() {
        let requests = to_hashset([create_test_request::<i64>(1, 100, 10, 0, 0)]);
        let entries = to_hashset([create_test_pre_assignment_entry::<i64>(1, 50, 5)]);
        let quay = SpaceLength::new(1_000);
        let p = Problem::new(requests, entries, quay);
        assert!(p.is_ok());
    }

    #[test]
    fn test_new_err_missing_request() {
        let requests = to_hashset([create_test_request::<i64>(1, 100, 10, 0, 0)]);
        let entries = to_hashset([create_test_pre_assignment_entry::<i64>(2, 50, 5)]); // request 2 does not exist
        let quay = SpaceLength::new(1_000);
        let err = Problem::new(requests, entries, quay).unwrap_err();
        assert!(matches!(err, ProblemError::MissingRequest(_)));
    }

    #[test]
    fn test_new_err_out_of_bounds() {
        let requests = to_hashset([create_test_request::<i64>(1, 200, 10, 0, 0)]);
        let entries = to_hashset([create_test_pre_assignment_entry::<i64>(1, 900, 0)]);
        let quay = SpaceLength::new(1_000);
        let err = Problem::new(requests, entries, quay).unwrap_err();
        assert!(matches!(err, ProblemError::RequestOutOfBounds(_)));
    }

    #[test]
    fn test_new_ok_touching_in_time_same_space() {
        let requests = to_hashset([
            create_test_request::<i64>(1, 100, 10, 0, 0),
            create_test_request::<i64>(2, 100, 10, 0, 0),
        ]);
        let entries = to_hashset([
            create_test_pre_assignment_entry::<i64>(1, 100, 0),
            create_test_pre_assignment_entry::<i64>(2, 100, 10),
        ]);
        let quay = SpaceLength::new(1_000);
        let p = Problem::new(requests, entries, quay);
        assert!(p.is_ok());
    }

    #[test]
    fn test_new_ok_touching_in_space_same_time() {
        let requests = to_hashset([
            create_test_request::<i64>(1, 100, 10, 0, 0),
            create_test_request::<i64>(2, 100, 10, 0, 0),
        ]);
        let entries = to_hashset([
            create_test_pre_assignment_entry::<i64>(1, 100, 0),
            create_test_pre_assignment_entry::<i64>(2, 200, 0),
        ]);
        let quay = SpaceLength::new(1_000);
        let p = Problem::new(requests, entries, quay);
        assert!(p.is_ok());
    }

    #[test]
    fn test_new_err_overlap_in_time_and_space() {
        let requests = to_hashset([
            create_test_request::<i64>(1, 150, 10, 0, 0),
            create_test_request::<i64>(2, 150, 10, 0, 0),
        ]);
        let entries = to_hashset([
            create_test_pre_assignment_entry::<i64>(1, 100, 0),
            create_test_pre_assignment_entry::<i64>(2, 200, 0),
        ]);
        let quay = SpaceLength::new(1_000);
        let err = Problem::new(requests, entries, quay).unwrap_err();
        assert!(matches!(err, ProblemError::RequestOverlap(_)));
    }

    #[test]
    fn test_new_ok_overlap_time_only() {
        let requests = to_hashset([
            create_test_request::<i64>(1, 100, 10, 0, 0),
            create_test_request::<i64>(2, 100, 10, 0, 0),
        ]);
        let entries = to_hashset([
            create_test_pre_assignment_entry::<i64>(1, 100, 0),
            create_test_pre_assignment_entry::<i64>(2, 300, 5),
        ]);
        let quay = SpaceLength::new(1_000);
        let p = Problem::new(requests, entries, quay);
        assert!(p.is_ok());
    }

    #[test]
    fn test_new_ok_overlap_space_only() {
        let requests = to_hashset([
            create_test_request::<i64>(1, 100, 10, 0, 0),
            create_test_request::<i64>(2, 100, 10, 0, 0),
        ]);
        let entries = to_hashset([
            create_test_pre_assignment_entry::<i64>(1, 100, 0),
            create_test_pre_assignment_entry::<i64>(2, 100, 10),
        ]);
        let quay = SpaceLength::new(1_000);
        let p = Problem::new(requests, entries, quay);
        assert!(p.is_ok());
    }

    #[test]
    fn new_ok_end_before_start_tie() {
        let requests = to_hashset([
            create_test_request::<i64>(1, 100, 10, 0, 0),
            create_test_request::<i64>(2, 100, 10, 0, 0),
        ]);
        let entries = to_hashset([
            create_test_pre_assignment_entry::<i64>(1, 500, 0),
            create_test_pre_assignment_entry::<i64>(2, 500, 10),
        ]);
        let quay = SpaceLength::new(1_000);
        let p = Problem::new(requests, entries, quay);
        assert!(p.is_ok());
    }

    #[test]
    fn test_new_ok_non_overlapping_middle_insert() {
        let requests = to_hashset([
            create_test_request::<i64>(1, 50, 10, 0, 0),
            create_test_request::<i64>(2, 50, 10, 0, 0),
            create_test_request::<i64>(3, 50, 10, 0, 0),
        ]);
        let entries = to_hashset([
            create_test_pre_assignment_entry::<i64>(1, 100, 0),
            create_test_pre_assignment_entry::<i64>(2, 150, 0),
            create_test_pre_assignment_entry::<i64>(3, 200, 0),
        ]);
        let quay = SpaceLength::new(1_000);
        let p = Problem::new(requests, entries, quay);
        assert!(p.is_ok());
    }

    #[test]
    fn test_new_err_equal_x0_overlapping_time() {
        let requests = to_hashset([
            create_test_request::<i64>(1, 80, 10, 0, 0),
            create_test_request::<i64>(2, 80, 10, 0, 0),
        ]);
        let entries = to_hashset([
            create_test_pre_assignment_entry::<i64>(1, 300, 0),
            create_test_pre_assignment_entry::<i64>(2, 300, 5),
        ]);
        let quay = SpaceLength::new(1_000);
        let err = Problem::new(requests, entries, quay).unwrap_err();
        assert!(matches!(err, ProblemError::RequestOverlap(_)));
    }

    #[test]
    fn test_new_ok_many_nonoverlapping_shuffled() {
        let requests = to_hashset([
            create_test_request::<i64>(1, 60, 7, 0, 0),
            create_test_request::<i64>(2, 60, 7, 0, 0),
            create_test_request::<i64>(3, 60, 7, 0, 0),
            create_test_request::<i64>(4, 60, 7, 0, 0),
        ]);
        let entries = to_hashset([
            create_test_pre_assignment_entry::<i64>(1, 0, 0),
            create_test_pre_assignment_entry::<i64>(2, 120, 5),
            create_test_pre_assignment_entry::<i64>(3, 0, 12),
            create_test_pre_assignment_entry::<i64>(4, 180, 10),
        ]);
        let quay = SpaceLength::new(1_000);
        let p = Problem::new(requests, entries, quay);
        assert!(p.is_ok());
    }

    #[test]
    fn new_err_assignment_violates_time_window() {
        let v1 = {
            let tw = TimeInterval::new(TimePoint::new(0_i64), TimePoint::new(10_i64));
            let sw = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(1_000));
            Request::new(
                RequestId::new(1),
                SpaceLength::new(100),
                TimeDelta::new(5),
                SpacePosition::new(0),
                Cost::new(1),
                Cost::new(1),
                tw,
                sw,
                None,
            )
            .unwrap()
        };
        let entries = to_hashset([create_test_pre_assignment_entry::<i64>(1, 0, 7)]);
        let quay = SpaceLength::new(1_000);
        let err = Problem::new(to_hashset([v1]), entries, quay).unwrap_err();
        assert!(matches!(err, ProblemError::AssignmentViolatesTimeWindow(_)));
    }

    #[test]
    fn test_new_err_assignment_violates_space_window() {
        let v1 = {
            let tw = TimeInterval::new(TimePoint::new(0_i64), TimePoint::new(100_i64));
            let sw = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(150));
            Request::new(
                RequestId::new(1),
                SpaceLength::new(100),
                TimeDelta::new(5),
                SpacePosition::new(0),
                Cost::new(1),
                Cost::new(1),
                tw,
                sw,
                None,
            )
            .unwrap()
        };
        let entries = to_hashset([create_test_pre_assignment_entry::<i64>(1, 100, 0)]);
        let quay = SpaceLength::new(1_000);
        let err = Problem::new(to_hashset([v1]), entries, quay).unwrap_err();
        assert!(matches!(
            err,
            ProblemError::AssignmentViolatesSpaceWindow(_)
        ));
    }

    fn mk_request<T: PrimInt + Signed + Debug>(
        id: u64,
        len: usize,
        proc: T,
        arr: T,
        tgt: usize,
        droppable: bool,
    ) -> Request<T, i64> {
        let tw = TimeInterval::new(
            TimePoint::new(arr),
            TimePoint::new(arr + proc + T::from(100).unwrap()),
        );
        let sw = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10_000));
        Request::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimeDelta::new(proc),
            SpacePosition::new(tgt),
            Cost::new(1),
            Cost::new(1),
            tw,
            sw,
            if droppable { Some(Cost::new(7)) } else { None },
        )
        .unwrap()
    }

    fn hs<T>(it: impl IntoIterator<Item = T>) -> HashSet<T>
    where
        T: Eq + Hash,
    {
        it.into_iter().collect()
    }

    #[test]
    fn solution_new_ok_assign_and_drop() {
        let v1 = mk_request::<i64>(1, 100, 10, 0, 0, false);
        let v2 = mk_request::<i64>(2, 100, 10, 0, 0, true);
        let p = Problem::new(
            hs([v1, v2]),
            hs([
                ProblemEntry::Unassigned(RequestId::new(1)),
                ProblemEntry::Unassigned(RequestId::new(2)),
            ]),
            SpaceLength::new(1_000),
        )
        .unwrap();

        let sol = Solution::<i64, i64>::new(
            &p,
            [
                Decision::Assign(Assignment::new(
                    RequestId::new(1),
                    SpacePosition::new(100),
                    TimePoint::new(5),
                )),
                Decision::Drop(RequestId::new(2)),
            ],
        )
        .unwrap();

        match sol.decisions().get(&RequestId::new(1)).copied().unwrap() {
            Decision::Assign(a) => {
                assert_eq!(a.berthing_position(), SpacePosition::new(100));
                assert_eq!(a.berthing_time(), TimePoint::new(5));
            }
            _ => panic!("v1 should be assigned"),
        }

        match sol.decisions().get(&RequestId::new(2)).copied().unwrap() {
            Decision::Drop(id) => assert_eq!(id, RequestId::new(2)),
            _ => panic!("v2 should be dropped"),
        }

        let stats = sol.stats();
        assert_eq!(stats.total_waiting_time().value(), 5);
        assert_eq!(stats.total_target_position_deviation().value(), 100);
        assert_eq!(stats.total_dropped_requests(), 1);
        assert_eq!(stats.total_cost().value(), 5 + 100 + 7);
    }

    #[test]
    fn solution_new_err_overlap() {
        let v1 = mk_request::<i64>(1, 200, 10, 0, 0, false);
        let v2 = mk_request::<i64>(2, 200, 10, 0, 0, false);
        let p = Problem::new(
            hs([v1, v2]),
            hs([
                ProblemEntry::Unassigned(RequestId::new(1)),
                ProblemEntry::Unassigned(RequestId::new(2)),
            ]),
            SpaceLength::new(600),
        )
        .unwrap();

        let err = Solution::<i64, i64>::new(
            &p,
            [
                Decision::Assign(Assignment::new(
                    1.into(),
                    SpacePosition::new(100),
                    TimePoint::new(0),
                )),
                Decision::Assign(Assignment::new(
                    2.into(),
                    SpacePosition::new(150),
                    TimePoint::new(5),
                )),
            ],
        )
        .unwrap_err();

        assert!(matches!(err, SolutionError::RequestOverlap(_)));
    }

    #[test]
    fn solution_new_err_missing_decision() {
        let v1 = mk_request::<i64>(1, 100, 10, 0, 0, false);
        let p = Problem::new(
            hs([v1]),
            hs([ProblemEntry::Unassigned(1.into())]),
            SpaceLength::new(1_000),
        )
        .unwrap();

        let err = Solution::<i64, i64>::new(&p, []).unwrap_err();
        assert!(matches!(err, SolutionError::MissingDecision(_)));
    }

    #[test]
    fn solution_new_err_preassigned_changed() {
        let v1 = mk_request::<i64>(1, 100, 10, 0, 100, false);
        let a = Assignment::new(1.into(), SpacePosition::new(200), TimePoint::new(5));
        let p = Problem::new(
            hs([v1]),
            hs([ProblemEntry::PreAssigned(a)]),
            SpaceLength::new(1_000),
        )
        .unwrap();

        let err = Solution::<i64, i64>::new(
            &p,
            [Decision::Assign(Assignment::new(
                1.into(),
                SpacePosition::new(220),
                TimePoint::new(5),
            ))],
        )
        .unwrap_err();

        assert!(matches!(err, SolutionError::PreassignmentChanged { .. }));
    }

    #[test]
    fn solution_new_err_drop_not_droppable() {
        let v1 = mk_request::<i64>(1, 100, 10, 0, 0, false);
        let p = Problem::new(
            hs([v1]),
            hs([ProblemEntry::Unassigned(1.into())]),
            SpaceLength::new(1_000),
        )
        .unwrap();

        let err = Solution::<i64, i64>::new(&p, [Decision::Drop(1.into())]).unwrap_err();

        assert!(matches!(err, SolutionError::DroppedNotDroppable(_)));
    }
}
