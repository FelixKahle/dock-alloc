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

//! # Dock Allocation Model (`dock-alloc-model`)
//!
//! This crate provides a high-level data model for representing the **Berth Allocation Problem (BAP)**.
//! It builds upon the foundational, type-safe primitives defined in the `dock-alloc-core` crate
//! to create structured representations of requests, assignments, problems, and solutions.
//!
//! The primary goal of `dock-alloc-model` is to offer a clear and robust API for defining
//! BAP instances and interpreting their solutions, ensuring domain-specific logic and constraints
//! are encapsulated effectively.
//!
//! ## Key Data Structures
//!
//! - **`RequestId`**: A unique identifier for an allocation request, typically representing a single ship.
//!
//! - **`Request<T, C>`**: Encapsulates all the necessary information for a single allocation request. This includes:
//!   - The ship's `length` and required `processing_duration`.
//!   - `feasible_time_window` and `feasible_space_window` defining when and where the ship can be berthed.
//!   - `cost_per_delay` and `cost_per_position_deviation` to quantify the economic impact of non-ideal assignments.
//!
//! - **`Assignment<T, C>`**: Represents a concrete decision, assigning a `Request` to a specific `start_time`
//!   and `start_position` on the quay.
//!
//! - **`Problem<T, C>`**: Defines a complete BAP instance. It contains a collection of `ProblemEntry` items
//!   (which can be unassigned requests or pre-assigned assignments that must be respected) and the total `quay_length`.
//!
//! - **`Solution<T, C>`**: Represents a complete solution to a `Problem`. It holds a map of `RequestId`s to their
//!   final `Assignment`s and includes `SolutionStats` to provide a quick overview of the solution's quality,
//!   including total cost, waiting time, and position deviation.
//!
//! ## Genericity
//!
//! The core structs like `Request`, `Assignment`, `Problem`, and `Solution` are generic over the underlying numeric types
//! for time (`T`) and cost (`C`). This allows users to choose the precision and range required for their specific
//! problem domain (e.g., `i64` for general use, or larger types for more complex scenarios).

#![allow(dead_code)]

use dock_alloc_core::domain::{
    Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use num_traits::{PrimInt, Signed};
use std::fmt::Display;
use std::{collections::HashMap, fmt::Debug, hash::Hash};

/// Unique identifier for a request.
///
/// A `Request` is a request for a berth allocation, which is a ship most likely.
/// However, the model does not enforce this, so it could be any other entity that
/// requires a berth allocation, like a maintenance operation or similar.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::RequestId;
///
/// let id = RequestId::new(42);
/// assert_eq!(id.value(), 42);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RequestId(u64);

impl RequestId {
    /// Creates a new `RequestId` with the given identifier.
    ///
    /// The identifier should be unique within the context of a problem instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::RequestId;
    ///
    /// let id = RequestId::new(1);
    /// assert_eq!(id.value(), 1);
    /// ```
    #[inline]
    pub const fn new(id: u64) -> Self {
        RequestId(id)
    }

    /// Returns the underlying identifier value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::RequestId;
    ///
    /// let id = RequestId::new(100);
    /// assert_eq!(id.value(), 100);
    /// ```
    #[inline]
    pub const fn value(&self) -> u64 {
        self.0
    }
}

impl Display for RequestId {
    /// Formats the `RequestId` for display purposes.
    ///
    /// Formats the `RequestId` in the form `"RequestId(id)"` where `id` is the underlying identifier value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::RequestId;
    ///
    /// let id = RequestId::new(7);
    /// assert_eq!(format!("{}", id), "RequestId(7)");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RequestId({})", self.0)
    }
}

impl From<u64> for RequestId {
    /// Converts a `u64` value into a `RequestId`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::RequestId;
    ///
    /// let id: RequestId = 10u64.into();
    /// assert_eq!(id.value(), 10);
    /// ```
    fn from(value: u64) -> Self {
        RequestId(value)
    }
}

/// An error indicating that a request's processing duration exceeds its feasible time window.
///
/// This error occurs when attempting to create a `Request` where the `processing_duration`
/// is larger than the duration of the `feasible_time_window`, making it impossible for
/// the request to be completed within its allowed time constraints.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{RequestId, TimeWindowTooShortError};
/// use dock_alloc_core::domain::{TimeDelta, TimeInterval, TimePoint};
///
/// let id = RequestId::new(1);
/// let processing = TimeDelta::new(10);
/// let window = TimeInterval::new(TimePoint::new(0), TimePoint::new(5)); // Only 5 units long
///
/// let error = TimeWindowTooShortError::new(id, processing, window);
/// assert_eq!(error.id(), id);
/// assert_eq!(error.processing_duration(), processing);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TimeWindowTooShortError<T: PrimInt + Signed> {
    id: RequestId,
    processing: TimeDelta<T>,
    window: TimeInterval<T>,
}

impl<T: PrimInt + Signed> TimeWindowTooShortError<T> {
    /// Creates a new `TimeWindowTooShortError`.
    ///
    /// # Arguments
    ///
    /// * `id` - The identifier of the request that caused the error
    /// * `processing` - The processing duration that doesn't fit
    /// * `window` - The time window that is too short
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, TimeWindowTooShortError};
    /// use dock_alloc_core::domain::{TimeDelta, TimeInterval, TimePoint};
    ///
    /// let error = TimeWindowTooShortError::new(
    ///     RequestId::new(42),
    ///     TimeDelta::new(8),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(5))
    /// );
    /// ```
    pub fn new(
        id: RequestId,
        processing: TimeDelta<T>,
        window: TimeInterval<T>,
    ) -> TimeWindowTooShortError<T> {
        TimeWindowTooShortError {
            id,
            processing,
            window,
        }
    }

    /// Returns the identifier of the request that caused this error.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, TimeWindowTooShortError};
    /// use dock_alloc_core::domain::{TimeDelta, TimeInterval, TimePoint};
    ///
    /// let id = RequestId::new(123);
    /// let error = TimeWindowTooShortError::new(
    ///     id,
    ///     TimeDelta::new(10),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(5))
    /// );
    /// assert_eq!(error.id(), id);
    /// ```
    pub fn id(&self) -> RequestId {
        self.id
    }

    /// Returns the processing duration that doesn't fit in the time window.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, TimeWindowTooShortError};
    /// use dock_alloc_core::domain::{TimeDelta, TimeInterval, TimePoint};
    ///
    /// let processing = TimeDelta::new(15);
    /// let error = TimeWindowTooShortError::new(
    ///     RequestId::new(1),
    ///     processing,
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10))
    /// );
    /// assert_eq!(error.processing_duration(), processing);
    /// ```
    pub fn processing_duration(&self) -> TimeDelta<T> {
        self.processing
    }

    /// Returns a reference to the time window that is too short.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, TimeWindowTooShortError};
    /// use dock_alloc_core::domain::{TimeDelta, TimeInterval, TimePoint};
    ///
    /// let window = TimeInterval::new(TimePoint::new(5), TimePoint::new(8));
    /// let error = TimeWindowTooShortError::new(
    ///     RequestId::new(1),
    ///     TimeDelta::new(10),
    ///     window
    /// );
    /// assert_eq!(error.time_window(), window);
    /// ```
    pub fn time_window(&self) -> TimeInterval<T> {
        self.window
    }
}

impl<T: PrimInt + Signed + Display> Display for TimeWindowTooShortError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Request {} has a processing duration of {} which does not fit into its time window {}",
            self.id, self.processing, self.window
        )
    }
}

impl<T: PrimInt + Signed + Debug + Display> std::error::Error for TimeWindowTooShortError<T> {}

/// An error indicating that a request's length exceeds its feasible space window.
///
/// This error occurs when attempting to create a `Request` where the `length`
/// is larger than the measure of the `feasible_space_window`, making it impossible
/// for the request to fit within its allowed space constraints.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{RequestId, SpaceWindowTooShortError};
/// use dock_alloc_core::domain::{SpaceLength, SpaceInterval, SpacePosition};
///
/// let id = RequestId::new(1);
/// let length = SpaceLength::new(15);
/// let window = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10)); // Only 10 units long
///
/// let error = SpaceWindowTooShortError::new(id, length, window);
/// assert_eq!(error.id(), id);
/// assert_eq!(error.length(), length);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpaceWindowTooShortError {
    id: RequestId,
    length: SpaceLength,
    window: SpaceInterval,
}

impl SpaceWindowTooShortError {
    /// Creates a new `SpaceWindowTooShortError`.
    ///
    /// # Arguments
    ///
    /// * `id` - The identifier of the request that caused the error
    /// * `length` - The length that doesn't fit
    /// * `window` - The space window that is too short
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, SpaceWindowTooShortError};
    /// use dock_alloc_core::domain::{SpaceLength, SpaceInterval, SpacePosition};
    ///
    /// let error = SpaceWindowTooShortError::new(
    ///     RequestId::new(42),
    ///     SpaceLength::new(20),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(15))
    /// );
    /// ```
    pub fn new(id: RequestId, length: SpaceLength, window: SpaceInterval) -> Self {
        SpaceWindowTooShortError { id, length, window }
    }

    /// Returns the identifier of the request that caused this error.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, SpaceWindowTooShortError};
    /// use dock_alloc_core::domain::{SpaceLength, SpaceInterval, SpacePosition};
    ///
    /// let id = RequestId::new(123);
    /// let error = SpaceWindowTooShortError::new(
    ///     id,
    ///     SpaceLength::new(25),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(20))
    /// );
    /// assert_eq!(error.id(), id);
    /// ```
    pub fn id(&self) -> RequestId {
        self.id
    }

    /// Returns the length that doesn't fit in the space window.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, SpaceWindowTooShortError};
    /// use dock_alloc_core::domain::{SpaceLength, SpaceInterval, SpacePosition};
    ///
    /// let length = SpaceLength::new(30);
    /// let error = SpaceWindowTooShortError::new(
    ///     RequestId::new(1),
    ///     length,
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(25))
    /// );
    /// assert_eq!(error.length(), length);
    /// ```
    pub fn length(&self) -> SpaceLength {
        self.length
    }

    /// Returns a reference to the space window that is too short.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, SpaceWindowTooShortError};
    /// use dock_alloc_core::domain::{SpaceLength, SpaceInterval, SpacePosition};
    ///
    /// let window = SpaceInterval::new(SpacePosition::new(5), SpacePosition::new(15));
    /// let error = SpaceWindowTooShortError::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(20),
    ///     window
    /// );
    /// assert_eq!(error.space_window(), window);
    /// ```
    pub fn space_window(&self) -> SpaceInterval {
        self.window
    }
}

impl Display for SpaceWindowTooShortError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Request {} has a length of {} which does not fit into its space window {}",
            self.id, self.length, self.window
        )
    }
}

impl std::error::Error for SpaceWindowTooShortError {}

/// An error that can occur when creating a `Request`.
///
/// This enum represents the different validation errors that can occur
/// when attempting to create a new request with invalid parameters.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{Request, RequestId, RequestError};
/// use dock_alloc_core::domain::*;
///
/// // Attempting to create a request with a processing duration longer than the time window
/// let result = Request::new(
///     RequestId::new(1),
///     SpaceLength::new(10),
///     TimeDelta::new(20), // Processing duration
///     SpacePosition::new(0),
///     Cost::new(1),
///     Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)), // Only 10 units available
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
/// );
///
/// match result {
///     Err(RequestError::TimeWindowTooShort(_)) => println!("Time window too short!"),
///     Err(RequestError::SpaceWindowTooShort(_)) => println!("Space window too short!"),
///     Ok(_) => println!("Request created successfully"),
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RequestError<T: PrimInt + Signed> {
    /// The request's processing duration exceeds its feasible time window.
    TimeWindowTooShort(TimeWindowTooShortError<T>),
    /// The request's length exceeds its feasible space window.
    SpaceWindowTooShort(SpaceWindowTooShortError),
}

impl<T: PrimInt + Signed + Display + Debug> Display for RequestError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RequestError::TimeWindowTooShort(e) => write!(f, "{}", e),
            RequestError::SpaceWindowTooShort(e) => write!(f, "{}", e),
        }
    }
}

impl<T: PrimInt + Signed + Display + Debug> std::error::Error for RequestError<T> {}

/// A request for a berth allocation.
///
/// This struct encapsulates all necessary information about a request, including its
/// unique identifier, length, processing duration, target position, costs, and feasible
/// time and space windows.
/// Most of the times a `Request` represents a ship that needs to be allocated a berth.
/// However, the model does not enforce this, so it could be any other entity that
/// requires a berth allocation, like a maintenance operation or similar.
#[derive(Debug, Clone, Copy)]
pub struct Request<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    id: RequestId,
    length: SpaceLength,
    processing_duration: TimeDelta<T>,
    target_position: SpacePosition,
    cost_per_delay: Cost<C>,
    cost_per_position_deviation: Cost<C>,
    feasible_time_window: TimeInterval<T>,
    feasible_space_window: SpaceInterval,
}

impl<T, C> PartialEq for Request<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<T, C> Eq for Request<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
}

impl<T, C> Hash for Request<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl<T, C> PartialOrd for Request<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T, C> Ord for Request<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl<T, C> Request<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    /// Creates a new `Request` with the specified parameters.
    ///
    /// # Arguments
    ///
    /// * `id` - Unique identifier for this request
    /// * `length` - The length of space required by this request
    /// * `processing_duration` - How long this request takes to process
    /// * `target_position` - The preferred position along the quay
    /// * `cost_per_delay` - Cost coefficient for waiting time beyond arrival
    /// * `cost_per_position_deviation` - Cost coefficient for deviation from target position
    /// * `feasible_time_window` - Time interval during which this request can be processed
    /// * `feasible_space_window` - Space interval where this request can be placed
    ///
    /// # Errors
    ///
    /// Returns `RequestError::TimeWindowTooShort` if the processing duration exceeds
    /// the time window duration.
    ///
    /// Returns `RequestError::SpaceWindowTooShort` if the required length exceeds
    /// the space window measure.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let request = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(10),
    ///     TimeDelta::new(5),
    ///     SpacePosition::new(20),
    ///     Cost::new(2),
    ///     Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// ).expect("Valid request parameters");
    ///
    /// assert_eq!(request.id(), RequestId::new(1));
    /// assert_eq!(request.length(), SpaceLength::new(10));
    /// ```
    #[allow(clippy::too_many_arguments)]
    #[inline]
    pub fn new(
        id: RequestId,
        length: SpaceLength,
        processing_duration: TimeDelta<T>,
        target_position: SpacePosition,
        cost_per_delay: Cost<C>,
        cost_per_position_deviation: Cost<C>,
        feasible_time_window: TimeInterval<T>,
        feasible_space_window: SpaceInterval,
    ) -> Result<Self, RequestError<T>> {
        if feasible_time_window.duration() < processing_duration {
            return Err(RequestError::TimeWindowTooShort(
                TimeWindowTooShortError::new(id, processing_duration, feasible_time_window),
            ));
        }

        if feasible_space_window.measure() < length {
            return Err(RequestError::SpaceWindowTooShort(
                SpaceWindowTooShortError::new(id, length, feasible_space_window),
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
        })
    }

    /// Returns the unique identifier of this request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(42), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// assert_eq!(request.id(), RequestId::new(42));
    /// ```
    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    /// Returns the length of space required by this request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(15), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// assert_eq!(request.length(), SpaceLength::new(15));
    /// ```
    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.length
    }

    /// Returns the arrival time of this request.
    ///
    /// This is the start of the feasible time window, representing the earliest
    /// time this request can begin processing.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(100), TimePoint::new(200)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// assert_eq!(request.arrival_time(), TimePoint::new(100));
    /// ```
    #[inline]
    pub fn arrival_time(&self) -> TimePoint<T> {
        self.feasible_time_window.start()
    }

    /// Returns the processing duration required by this request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(8),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(20)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// assert_eq!(request.processing_duration(), TimeDelta::new(8));
    /// ```
    #[inline]
    pub fn processing_duration(&self) -> TimeDelta<T> {
        self.processing_duration
    }

    /// Returns the target position for this request.
    ///
    /// This represents the preferred position along the quay where the request
    /// would ideally be placed to minimize position deviation costs.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(25), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// assert_eq!(request.target_position(), SpacePosition::new(25));
    /// ```
    #[inline]
    pub fn target_position(&self) -> SpacePosition {
        self.target_position
    }

    /// Returns the cost coefficient for delay (waiting time).
    ///
    /// This value is multiplied by the waiting time to calculate the delay cost.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(3), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// assert_eq!(request.cost_per_delay(), Cost::new(3));
    /// ```
    #[inline]
    pub fn cost_per_delay(&self) -> Cost<C> {
        self.cost_per_delay
    }

    /// Returns the cost coefficient for position deviation.
    ///
    /// This value is multiplied by the distance from the target position
    /// to calculate the position deviation cost.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(4),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// assert_eq!(request.cost_per_position_deviation(), Cost::new(4));
    /// ```
    #[inline]
    pub fn cost_per_position_deviation(&self) -> Cost<C> {
        self.cost_per_position_deviation
    }

    /// Returns a reference to the feasible time window for this request.
    ///
    /// This interval defines when the request can be processed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let window = TimeInterval::new(TimePoint::new(5), TimePoint::new(15));
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     window, SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// assert_eq!(request.feasible_time_window(), window);
    /// ```
    #[inline]
    pub fn feasible_time_window(&self) -> TimeInterval<T> {
        self.feasible_time_window
    }

    /// Returns a reference to the feasible space window for this request.
    ///
    /// This interval defines where along the quay the request can be placed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let window = SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(40));
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)), window
    /// # ).unwrap();
    ///
    /// assert_eq!(request.feasible_space_window(), window);
    /// ```
    #[inline]
    pub fn feasible_space_window(&self) -> SpaceInterval {
        self.feasible_space_window
    }
}

impl<T, C> Request<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T>,
{
    /// Calculates the cost incurred by waiting for the given duration.
    ///
    /// The cost is computed as `cost_per_delay * waiting_time`.
    ///
    /// # Arguments
    ///
    /// * `waiting_time` - The duration of waiting time
    ///
    /// # Panics
    ///
    /// Panics if the waiting time value cannot be converted to the cost type `C`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(3), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// let wait_cost = request.waiting_cost(TimeDelta::new(4));
    /// assert_eq!(wait_cost, Cost::new(12)); // 3 * 4
    /// ```
    #[inline]
    pub fn waiting_cost(&self, waiting_time: TimeDelta<T>) -> Cost<C> {
        let scalar: C = C::try_from(waiting_time.value())
            .ok()
            .expect("waiting time does not fit in C");
        self.cost_per_delay * scalar
    }
}

impl<T, C> Request<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<usize>,
{
    /// Calculates the cost incurred by deviating from the target position.
    ///
    /// The cost is computed as `cost_per_position_deviation * deviation`.
    ///
    /// # Arguments
    ///
    /// * `deviation` - The distance from the target position
    ///
    /// # Panics
    ///
    /// Panics if the deviation value cannot be converted to the cost type `C`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(5),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// let deviation_cost = request.target_position_deviation_cost(SpaceLength::new(3));
    /// assert_eq!(deviation_cost, Cost::new(15)); // 5 * 3
    /// ```
    #[inline]
    pub fn target_position_deviation_cost(&self, deviation: SpaceLength) -> Cost<C> {
        let scalar: C = C::try_from(deviation.value())
            .ok()
            .expect("deviation does not fit in C");
        self.cost_per_position_deviation * scalar
    }
}

impl<T, C> Display for Request<T, C>
where
    T: PrimInt + Signed + Display,
    C: PrimInt + Signed + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Request(id: {}, \
            length: {}, \
            processing_duration: {}, \
            target_position: {}, \
            cost_per_delay: {}, \
            cost_per_position_deviation: {}, \
            feasible_time_window: {}, \
            feasible_space_window: {})",
            self.id,
            self.length,
            self.processing_duration,
            self.target_position,
            self.cost_per_delay,
            self.cost_per_position_deviation,
            self.feasible_time_window,
            self.feasible_space_window
        )
    }
}

/// An assignment of a request to a specific start position and start time.
///
/// This struct encapsulates the details of an assignment, including the request being assigned,
/// the start position along the quay, and the start time of the assignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Assignment<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    request: Request<T, C>,
    start_position: SpacePosition,
    start_time: TimePoint<T>,
}

impl<T, C> Assignment<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    /// Creates a new assignment for the given request.
    ///
    /// # Arguments
    ///
    /// * `request` - The request being assigned
    /// * `start_position` - The position along the quay where the assignment starts
    /// * `start_time` - The time when the assignment starts
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// let assignment = Assignment::new(
    ///     request,
    ///     SpacePosition::new(15),
    ///     TimePoint::new(2)
    /// );
    /// assert_eq!(assignment.start_position(), SpacePosition::new(15));
    /// assert_eq!(assignment.start_time(), TimePoint::new(2));
    /// ```
    #[inline]
    pub fn new(
        request: Request<T, C>,
        start_position: SpacePosition,
        start_time: TimePoint<T>,
    ) -> Self {
        Assignment {
            request,
            start_position,
            start_time,
        }
    }

    /// Returns a reference to the request being assigned.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(42), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    /// # let assignment = Assignment::new(request, SpacePosition::new(15), TimePoint::new(2));
    ///
    /// assert_eq!(assignment.request().id(), RequestId::new(42));
    /// ```
    #[inline]
    pub fn request(&self) -> &Request<T, C> {
        &self.request
    }

    /// Returns the start position of this assignment along the quay.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    /// # let assignment = Assignment::new(request, SpacePosition::new(25), TimePoint::new(3));
    ///
    /// assert_eq!(assignment.start_position(), SpacePosition::new(25));
    /// ```
    #[inline]
    pub fn start_position(&self) -> SpacePosition {
        self.start_position
    }

    /// Returns the start time of this assignment.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    /// # let assignment = Assignment::new(request, SpacePosition::new(15), TimePoint::new(7));
    ///
    /// assert_eq!(assignment.start_time(), TimePoint::new(7));
    /// ```
    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }
}

impl<T> Display for Assignment<T>
where
    T: PrimInt + Signed + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment(request_id: {}, start_position: {}, start_time: {})",
            self.request.id(),
            self.start_position,
            self.start_time
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FixedRequest<'a, T = i64, C = i64>(&'a Request<T, C>)
where
    T: PrimInt + Signed,
    C: PrimInt + Signed;

impl<'a, T, C> FixedRequest<'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn new(r: &'a Request<T, C>) -> Self {
        Self(r)
    }

    pub fn request(&self) -> &'a Request<T, C> {
        &self.0
    }
}

impl<'a, T, C> Display for FixedRequest<'a, T, C>
where
    T: PrimInt + Signed + Display,
    C: PrimInt + Signed + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FixedRequest({})", self.0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MoveableRequest<T = i64, C = i64>(Request<T, C>)
where
    T: PrimInt + Signed,
    C: PrimInt + Signed;

impl<T, C> MoveableRequest<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn new(r: Request<T, C>) -> Self {
        Self(r)
    }

    pub fn request(&self) -> &Request<T, C> {
        &self.0
    }
}

impl<T, C> Display for MoveableRequest<T, C>
where
    T: PrimInt + Signed + Display,
    C: PrimInt + Signed + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MoveableRequest({})", self.0)
    }
}

/// A wrapper around an `Assignment` indicating that it is fixed (preassigned).
///
/// FixedAssignment assignments represent requests that have already been assigned and cannot
/// be changed during optimization. They must be respected by any solution.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{FixedAssignment, Assignment, Request, RequestId};
/// use dock_alloc_core::domain::*;
/// # let request = Request::new(
/// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
/// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
/// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
/// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
/// # ).unwrap();
///
/// let assignment = Assignment::new(request, SpacePosition::new(15), TimePoint::new(2));
/// let fixed = FixedAssignment::new(assignment);
/// assert_eq!(fixed.assignment().start_position(), SpacePosition::new(15));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FixedAssignment<T = i64, C = i64>(Assignment<T, C>)
where
    T: PrimInt + Signed,
    C: PrimInt + Signed;

impl<T, C> FixedAssignment<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    /// Creates a new fixed assignment from the given assignment.
    ///
    /// # Arguments
    ///
    /// * `a` - The assignment to mark as fixed
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{FixedAssignment, Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    ///
    /// let assignment = Assignment::new(request, SpacePosition::new(10), TimePoint::new(1));
    /// let fixed = FixedAssignment::new(assignment);
    /// ```
    pub fn new(a: Assignment<T, C>) -> Self {
        Self(a)
    }

    /// Returns a reference to the underlying assignment.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{FixedAssignment, Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    /// # let assignment = Assignment::new(request, SpacePosition::new(10), TimePoint::new(1));
    /// # let fixed = FixedAssignment::new(assignment);
    ///
    /// assert_eq!(fixed.assignment().start_position(), SpacePosition::new(10));
    /// ```
    pub fn assignment(&self) -> &Assignment<T, C> {
        &self.0
    }
}

/// An error indicating that an assignment is outside its feasible time window.
///
/// This error occurs when an assignment's time interval extends beyond
/// the request's feasible time window, violating temporal constraints.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{RequestId, AssignmentOutsideTimeWindowError};
/// use dock_alloc_core::domain::{TimeInterval, TimePoint};
///
/// let error = AssignmentOutsideTimeWindowError::new(
///     RequestId::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)), // Feasible window
///     TimeInterval::new(TimePoint::new(8), TimePoint::new(15))  // Assignment extends to 15
/// );
/// assert_eq!(error.id(), RequestId::new(1));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentOutsideTimeWindowError<T: PrimInt + Signed> {
    id: RequestId,
    time_window: TimeInterval<T>,
    assigned_interval: TimeInterval<T>,
}

impl<T: PrimInt + Signed> AssignmentOutsideTimeWindowError<T> {
    /// Creates a new `AssignmentOutsideTimeWindowError`.
    ///
    /// # Arguments
    ///
    /// * `id` - The identifier of the request with the invalid assignment
    /// * `time_window` - The feasible time window for the request
    /// * `assigned_interval` - The time interval of the invalid assignment
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentOutsideTimeWindowError};
    /// use dock_alloc_core::domain::{TimeInterval, TimePoint};
    ///
    /// let error = AssignmentOutsideTimeWindowError::new(
    ///     RequestId::new(42),
    ///     TimeInterval::new(TimePoint::new(5), TimePoint::new(20)),
    ///     TimeInterval::new(TimePoint::new(18), TimePoint::new(25))
    /// );
    /// ```
    pub fn new(
        id: RequestId,
        time_window: TimeInterval<T>,
        assigned_interval: TimeInterval<T>,
    ) -> Self {
        AssignmentOutsideTimeWindowError {
            id,
            time_window,
            assigned_interval,
        }
    }

    /// Returns the identifier of the request that caused this error.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentOutsideTimeWindowError};
    /// use dock_alloc_core::domain::{TimeInterval, TimePoint};
    ///
    /// let error = AssignmentOutsideTimeWindowError::new(
    ///     RequestId::new(123),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    ///     TimeInterval::new(TimePoint::new(8), TimePoint::new(15))
    /// );
    /// assert_eq!(error.id(), RequestId::new(123));
    /// ```
    pub fn id(&self) -> RequestId {
        self.id
    }

    /// Returns a reference to the feasible time window.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentOutsideTimeWindowError};
    /// use dock_alloc_core::domain::{TimeInterval, TimePoint};
    ///
    /// let window = TimeInterval::new(TimePoint::new(0), TimePoint::new(10));
    /// let error = AssignmentOutsideTimeWindowError::new(
    ///     RequestId::new(1),
    ///     window,
    ///     TimeInterval::new(TimePoint::new(8), TimePoint::new(15))
    /// );
    /// assert_eq!(error.time_window(), window);
    /// ```
    pub fn time_window(&self) -> TimeInterval<T> {
        self.time_window
    }

    /// Returns a reference to the assigned time interval that caused the error.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentOutsideTimeWindowError};
    /// use dock_alloc_core::domain::{TimeInterval, TimePoint};
    ///
    /// let assigned = TimeInterval::new(TimePoint::new(8), TimePoint::new(15));
    /// let error = AssignmentOutsideTimeWindowError::new(
    ///     RequestId::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    ///     assigned
    /// );
    /// assert_eq!(error.assigned_interval(), assigned);
    /// ```
    pub fn assigned_interval(&self) -> TimeInterval<T> {
        self.assigned_interval
    }
}

impl<T: PrimInt + Signed + Display> Display for AssignmentOutsideTimeWindowError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment for request {} is outside its time window: assigned interval {} not in time window {}",
            self.id, self.assigned_interval, self.time_window
        )
    }
}

impl<T: PrimInt + Signed + Debug + Display> std::error::Error
    for AssignmentOutsideTimeWindowError<T>
{
}

/// An error indicating that an assignment is outside its feasible space window.
///
/// This error occurs when an assignment's space interval extends beyond
/// the request's feasible space window, violating spatial constraints.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{RequestId, AssignmentOutsideSpaceWindowError};
/// use dock_alloc_core::domain::{SpaceInterval, SpacePosition};
///
/// let error = AssignmentOutsideSpaceWindowError::new(
///     RequestId::new(1),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(30)), // Feasible window
///     SpaceInterval::new(SpacePosition::new(25), SpacePosition::new(35)) // Assignment extends to 35
/// );
/// assert_eq!(error.id(), RequestId::new(1));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentOutsideSpaceWindowError {
    id: RequestId,
    space_window: SpaceInterval,
    assigned_interval: SpaceInterval,
}

impl AssignmentOutsideSpaceWindowError {
    /// Creates a new `AssignmentOutsideSpaceWindowError`.
    ///
    /// # Arguments
    ///
    /// * `id` - The identifier of the request with the invalid assignment
    /// * `space_window` - The feasible space window for the request
    /// * `assigned_interval` - The space interval of the invalid assignment
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentOutsideSpaceWindowError};
    /// use dock_alloc_core::domain::{SpaceInterval, SpacePosition};
    ///
    /// let error = AssignmentOutsideSpaceWindowError::new(
    ///     RequestId::new(42),
    ///     SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(50)),
    ///     SpaceInterval::new(SpacePosition::new(45), SpacePosition::new(55))
    /// );
    /// ```
    pub fn new(
        id: RequestId,
        space_window: SpaceInterval,
        assigned_interval: SpaceInterval,
    ) -> Self {
        AssignmentOutsideSpaceWindowError {
            id,
            space_window,
            assigned_interval,
        }
    }

    /// Returns the identifier of the request that caused this error.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentOutsideSpaceWindowError};
    /// use dock_alloc_core::domain::{SpaceInterval, SpacePosition};
    ///
    /// let error = AssignmentOutsideSpaceWindowError::new(
    ///     RequestId::new(123),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(30)),
    ///     SpaceInterval::new(SpacePosition::new(25), SpacePosition::new(35))
    /// );
    /// assert_eq!(error.id(), RequestId::new(123));
    /// ```
    pub fn id(&self) -> RequestId {
        self.id
    }

    /// Returns a reference to the feasible space window.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentOutsideSpaceWindowError};
    /// use dock_alloc_core::domain::{SpaceInterval, SpacePosition};
    ///
    /// let window = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(30));
    /// let error = AssignmentOutsideSpaceWindowError::new(
    ///     RequestId::new(1),
    ///     window,
    ///     SpaceInterval::new(SpacePosition::new(25), SpacePosition::new(35))
    /// );
    /// assert_eq!(error.space_window(), window);
    /// ```
    pub fn space_window(&self) -> SpaceInterval {
        self.space_window
    }

    /// Returns a reference to the assigned space interval that caused the error.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentOutsideSpaceWindowError};
    /// use dock_alloc_core::domain::{SpaceInterval, SpacePosition};
    ///
    /// let assigned = SpaceInterval::new(SpacePosition::new(25), SpacePosition::new(35));
    /// let error = AssignmentOutsideSpaceWindowError::new(
    ///     RequestId::new(1),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(30)),
    ///     assigned
    /// );
    /// assert_eq!(error.assigned_interval(), assigned);
    /// ```
    pub fn assigned_interval(&self) -> SpaceInterval {
        self.assigned_interval
    }
}

impl Display for AssignmentOutsideSpaceWindowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment for request {} is outside its space window: assigned interval {} not in space window {}",
            self.id, self.assigned_interval, self.space_window
        )
    }
}

impl std::error::Error for AssignmentOutsideSpaceWindowError {}

/// An error indicating that an assignment extends beyond the quay length.
///
/// This error occurs when an assignment's space interval extends past
/// the end of the quay, violating the physical constraints of the dock.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{RequestId, AssignmentExceedsQuayError};
/// use dock_alloc_core::domain::{SpaceLength, SpaceInterval, SpacePosition};
///
/// let error = AssignmentExceedsQuayError::new(
///     RequestId::new(1),
///     SpaceLength::new(100), // Quay is 100 units long
///     SpaceInterval::new(SpacePosition::new(90), SpacePosition::new(110)) // Assignment goes to 110
/// );
/// assert_eq!(error.quay_length(), SpaceLength::new(100));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentExceedsQuayError {
    id: RequestId,
    quay_length: SpaceLength,
    assigned_interval: SpaceInterval,
}

impl AssignmentExceedsQuayError {
    /// Creates a new `AssignmentExceedsQuayError`.
    ///
    /// # Arguments
    ///
    /// * `id` - The identifier of the request with the invalid assignment
    /// * `quay_length` - The total length of the quay
    /// * `assigned_interval` - The space interval that exceeds the quay
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentExceedsQuayError};
    /// use dock_alloc_core::domain::{SpaceLength, SpaceInterval, SpacePosition};
    ///
    /// let error = AssignmentExceedsQuayError::new(
    ///     RequestId::new(42),
    ///     SpaceLength::new(200),
    ///     SpaceInterval::new(SpacePosition::new(180), SpacePosition::new(220))
    /// );
    /// ```
    pub fn new(id: RequestId, quay_length: SpaceLength, assigned_interval: SpaceInterval) -> Self {
        AssignmentExceedsQuayError {
            id,
            quay_length,
            assigned_interval,
        }
    }

    /// Returns the identifier of the request that caused this error.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentExceedsQuayError};
    /// use dock_alloc_core::domain::{SpaceLength, SpaceInterval, SpacePosition};
    ///
    /// let error = AssignmentExceedsQuayError::new(
    ///     RequestId::new(123),
    ///     SpaceLength::new(100),
    ///     SpaceInterval::new(SpacePosition::new(90), SpacePosition::new(110))
    /// );
    /// assert_eq!(error.id(), RequestId::new(123));
    /// ```
    pub fn id(&self) -> RequestId {
        self.id
    }

    /// Returns the total length of the quay.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentExceedsQuayError};
    /// use dock_alloc_core::domain::{SpaceLength, SpaceInterval, SpacePosition};
    ///
    /// let error = AssignmentExceedsQuayError::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(150),
    ///     SpaceInterval::new(SpacePosition::new(140), SpacePosition::new(160))
    /// );
    /// assert_eq!(error.quay_length(), SpaceLength::new(150));
    /// ```
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    /// Returns a reference to the assigned space interval that exceeds the quay.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, AssignmentExceedsQuayError};
    /// use dock_alloc_core::domain::{SpaceLength, SpaceInterval, SpacePosition};
    ///
    /// let assigned = SpaceInterval::new(SpacePosition::new(90), SpacePosition::new(110));
    /// let error = AssignmentExceedsQuayError::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     assigned
    /// );
    /// assert_eq!(error.assigned_interval(), assigned);
    /// ```
    pub fn assigned_interval(&self) -> SpaceInterval {
        self.assigned_interval
    }
}

impl Display for AssignmentExceedsQuayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment for request {} exceeds quay length {}: assigned interval {}",
            self.id, self.quay_length, self.assigned_interval
        )
    }
}

impl std::error::Error for AssignmentExceedsQuayError {}

/// An error indicating that two preassigned assignments overlap in space and time.
///
/// This error occurs when attempting to add a preassigned assignment that
/// conflicts with an existing preassigned assignment, creating an impossible
/// scenario where two requests would occupy the same space at the same time.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{RequestId, PreassignedOverlapError};
///
/// let error = PreassignedOverlapError::new(
///     RequestId::new(1),
///     RequestId::new(2)
/// );
/// assert_eq!(error.request_a(), RequestId::new(1));
/// assert_eq!(error.request_b(), RequestId::new(2));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PreassignedOverlapError {
    a: RequestId,
    b: RequestId,
}

impl PreassignedOverlapError {
    /// Creates a new `PreassignedOverlapError`.
    ///
    /// # Arguments
    ///
    /// * `a` - The identifier of the first conflicting request
    /// * `b` - The identifier of the second conflicting request
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, PreassignedOverlapError};
    ///
    /// let error = PreassignedOverlapError::new(
    ///     RequestId::new(10),
    ///     RequestId::new(20)
    /// );
    /// ```
    pub fn new(a: RequestId, b: RequestId) -> Self {
        PreassignedOverlapError { a, b }
    }

    /// Returns the identifier of the first conflicting request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, PreassignedOverlapError};
    ///
    /// let error = PreassignedOverlapError::new(
    ///     RequestId::new(5),
    ///     RequestId::new(7)
    /// );
    /// assert_eq!(error.request_a(), RequestId::new(5));
    /// ```
    pub fn request_a(&self) -> RequestId {
        self.a
    }

    /// Returns the identifier of the second conflicting request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{RequestId, PreassignedOverlapError};
    ///
    /// let error = PreassignedOverlapError::new(
    ///     RequestId::new(5),
    ///     RequestId::new(7)
    /// );
    /// assert_eq!(error.request_b(), RequestId::new(7));
    /// ```
    pub fn request_b(&self) -> RequestId {
        self.b
    }
}

impl Display for PreassignedOverlapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Preassigned assignments for requests {} and {} overlap",
            self.a, self.b
        )
    }
}

/// An error that can occur when building a `Problem`.
///
/// This enum represents the different validation errors that can occur
/// when using `ProblemBuilder` to construct a berth allocation problem.
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{ProblemBuilder, ProblemBuildError, RequestId};
/// use dock_alloc_core::domain::SpaceLength;
///
/// // This will cause a duplicate ID error if you try to add the same request twice
/// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
/// // ... add requests that would cause errors
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProblemBuildError<T: PrimInt + Signed> {
    /// A request with this ID has already been added to the problem.
    DuplicateRequestId(RequestId),
    /// A preassigned assignment is outside its request's feasible time window.
    AssignmentOutsideTimeWindow(AssignmentOutsideTimeWindowError<T>),
    /// A preassigned assignment is outside its request's feasible space window.
    AssignmentOutsideSpaceWindow(AssignmentOutsideSpaceWindowError),
    /// A preassigned assignment extends beyond the quay length.
    AssignmentExceedsQuay(AssignmentExceedsQuayError),
    /// Two preassigned assignments overlap in space and time.
    PreassignedOverlap(PreassignedOverlapError),
}

impl<T: PrimInt + Signed + Display + Debug> Display for ProblemBuildError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProblemBuildError::DuplicateRequestId(id) => {
                write!(f, "Duplicate request ID found: {}", id)
            }
            ProblemBuildError::AssignmentOutsideTimeWindow(e) => write!(f, "{}", e),
            ProblemBuildError::AssignmentOutsideSpaceWindow(e) => write!(f, "{}", e),
            ProblemBuildError::AssignmentExceedsQuay(e) => write!(f, "{}", e),
            ProblemBuildError::PreassignedOverlap(e) => write!(f, "{}", e),
        }
    }
}

impl<T: PrimInt + Signed + Display + Debug> std::error::Error for ProblemBuildError<T> {}

/// A berth allocation problem instance.
///
/// This struct represents a complete berth allocation problem, containing both
/// unassigned requests that need to be allocated and preassigned (fixed) assignments
/// that must be respected in any solution.
///
/// The problem definition includes the quay length, which constrains where
/// assignments can be placed spatially.
///
/// # Type Parameters
///
/// * `T` - The numeric type used for time values (default: `i64`)
/// * `C` - The numeric type used for cost values (default: `i64`)
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{Problem, ProblemBuilder, Request, RequestId};
/// use dock_alloc_core::domain::*;
///
/// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
///
/// let request = Request::new(
///     RequestId::new(1),
///     SpaceLength::new(10),
///     TimeDelta::new(5),
///     SpacePosition::new(20),
///     Cost::new(2),
///     Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
/// ).unwrap();
///
/// builder.add_unassigned_request(request).unwrap();
/// let problem = builder.build();
///
/// assert_eq!(problem.total_requests(), 1);
/// assert_eq!(problem.quay_length(), SpaceLength::new(100));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Problem<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    unassigned: HashMap<RequestId, MoveableRequest<T, C>>,
    preassigned: HashMap<RequestId, FixedAssignment<T, C>>,
    quay_length: SpaceLength,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProblemRequest<'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    Moveable(&'a MoveableRequest<T, C>),
    Fixed(FixedRequest<'a, T, C>),
}

impl<'a, T, C> Display for ProblemRequest<'a, T, C>
where
    T: PrimInt + Signed + Display,
    C: PrimInt + Signed + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProblemRequest::Moveable(mr) => write!(f, "Moveable({})", mr),
            ProblemRequest::Fixed(fr) => write!(f, "Fixed({})", fr),
        }
    }
}

impl<T, C> Problem<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(
        unassigned: HashMap<RequestId, MoveableRequest<T, C>>,
        preassigned: HashMap<RequestId, FixedAssignment<T, C>>,
        quay_length: SpaceLength,
    ) -> Self {
        Self {
            unassigned,
            preassigned,
            quay_length,
        }
    }

    #[inline]
    pub fn unassigned(&self) -> &HashMap<RequestId, MoveableRequest<T, C>> {
        &self.unassigned
    }

    #[inline]
    pub fn preassigned(&self) -> &HashMap<RequestId, FixedAssignment<T, C>> {
        &self.preassigned
    }

    /// Returns the total length of the quay.
    ///
    /// This defines the spatial constraint for the problem - no assignment
    /// can extend beyond this length.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::ProblemBuilder;
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(200));
    /// let problem = builder.build();
    /// assert_eq!(problem.quay_length(), SpaceLength::new(200));
    /// ```
    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    /// Returns the total number of requests in this problem.
    ///
    /// This includes both unassigned requests and preassigned requests.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// # let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// # let request1 = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    /// # let request2 = Request::new(
    /// #     RequestId::new(2), SpaceLength::new(8), TimeDelta::new(3),
    /// #     SpacePosition::new(15), Cost::new(1), Cost::new(2),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(8)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(40))
    /// # ).unwrap();
    /// # builder.add_unassigned_request(request1).unwrap();
    /// # builder.add_unassigned_request(request2).unwrap();
    /// # let problem = builder.build();
    ///
    /// assert_eq!(problem.total_requests(), 2);
    /// ```
    #[inline]
    pub fn total_requests(&self) -> usize {
        self.unassigned.len() + self.preassigned.len()
    }

    pub fn iter_moveable_requests(&self) -> impl Iterator<Item = &MoveableRequest<T, C>> {
        self.unassigned.values()
    }

    pub fn iter_fixed_requests(&self) -> impl Iterator<Item = FixedRequest<'_, T, C>> {
        self.preassigned
            .values()
            .map(|fa| FixedRequest::new(fa.assignment().request()))
    }

    pub fn iter_requests(&self) -> impl Iterator<Item = ProblemRequest<'_, T, C>> {
        self.unassigned
            .values()
            .map(ProblemRequest::Moveable)
            .chain(
                self.preassigned
                    .values()
                    .map(|fa| ProblemRequest::Fixed(FixedRequest::new(fa.assignment().request()))),
            )
    }

    pub fn iter_fixed_assignments(&self) -> impl Iterator<Item = &FixedAssignment<T, C>> {
        self.preassigned.values()
    }
}

/// Type alias for a berth allocation problem using standard integer types.
///
/// This is a convenience alias for `Problem<i64, i64>`, representing the most
/// common configuration where both time and cost values are 64-bit signed integers.
pub type BerthAllocationProblem = Problem<i64, i64>;

/// A builder for constructing `Problem` instances with validation.
///
/// `ProblemBuilder` provides a safe way to construct berth allocation problems
/// by validating constraints as requests and assignments are added. It ensures
/// that all assignments are feasible and that preassigned assignments don't conflict.
///
/// # Type Parameters
///
/// * `T` - The numeric type used for time values (default: `i64`)
/// * `C` - The numeric type used for cost values (default: `i64`)
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{ProblemBuilder, Request, FixedAssignment, Assignment, RequestId};
/// use dock_alloc_core::domain::*;
///
/// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
///
/// // Add an unassigned request
/// let request1 = Request::new(
///     RequestId::new(1),
///     SpaceLength::new(10),
///     TimeDelta::new(5),
///     SpacePosition::new(20),
///     Cost::new(2),
///     Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
/// ).unwrap();
/// builder.add_unassigned_request(request1).unwrap();
///
/// // Add a preassigned request
/// let request2 = Request::new(
///     RequestId::new(2),
///     SpaceLength::new(8),
///     TimeDelta::new(3),
///     SpacePosition::new(15),
///     Cost::new(1),
///     Cost::new(2),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(8)),
///     SpaceInterval::new(SpacePosition::new(60), SpacePosition::new(80))
/// ).unwrap();
/// let assignment = Assignment::new(request2, SpacePosition::new(65), TimePoint::new(1));
/// builder.add_preassigned(FixedAssignment::new(assignment)).unwrap();
///
/// let problem = builder.build();
/// assert_eq!(problem.total_requests(), 2);
/// ```
pub struct ProblemBuilder<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    unassigned: HashMap<RequestId, MoveableRequest<T, C>>,
    preassigned: HashMap<RequestId, FixedAssignment<T, C>>,
    quay_length: SpaceLength,
}

impl<T, C> ProblemBuilder<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    /// Creates a new `ProblemBuilder` with the specified quay length.
    ///
    /// # Arguments
    ///
    /// * `quay_length` - The total length of the quay
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::ProblemBuilder;
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(150));
    /// ```
    pub fn new(quay_length: SpaceLength) -> Self {
        Self {
            unassigned: HashMap::new(),
            preassigned: HashMap::new(),
            quay_length,
        }
    }

    /// Sets the quay length for this problem.
    ///
    /// # Arguments
    ///
    /// * `length` - The new quay length
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::ProblemBuilder;
    /// use dock_alloc_core::domain::SpaceLength;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// builder.quay_length(SpaceLength::new(200));
    /// ```
    pub fn quay_length(&mut self, length: SpaceLength) -> &mut Self {
        self.quay_length = length;
        self
    }

    /// Adds an unassigned request to the problem.
    ///
    /// The request will need to be allocated a berth position and time
    /// in any solution to the problem.
    ///
    /// # Arguments
    ///
    /// * `request` - The request to add
    ///
    /// # Errors
    ///
    /// Returns `ProblemBuildError::DuplicateRequestId` if a request with the same
    /// ID has already been added to this problem.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(10),
    ///     TimeDelta::new(5),
    ///     SpacePosition::new(20),
    ///     Cost::new(2),
    ///     Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// ).unwrap();
    ///
    /// builder.add_unassigned_request(request).unwrap();
    /// ```
    pub fn add_unassigned_request(
        &mut self,
        request: Request<T, C>,
    ) -> Result<&mut Self, ProblemBuildError<T>> {
        let id = request.id();
        if self.unassigned.contains_key(&id) || self.preassigned.contains_key(&id) {
            return Err(ProblemBuildError::DuplicateRequestId(id));
        }
        self.unassigned.insert(id, MoveableRequest::new(request));
        Ok(self)
    }

    #[inline]
    fn assignment_spans(a: &Assignment<T, C>) -> (TimeInterval<T>, SpaceInterval) {
        let t0 = a.start_time();
        let t1 = t0 + a.request().processing_duration();
        let s0 = a.start_position();
        let s1 = SpacePosition::new(s0.value() + a.request().length().value());
        (TimeInterval::new(t0, t1), SpaceInterval::new(s0, s1))
    }

    /// Adds a preassigned (fixed) assignment to the problem.
    ///
    /// The assignment is validated to ensure it respects all constraints:
    /// - Must be within the request's feasible time and space windows
    /// - Must not extend beyond the quay length
    /// - Must not overlap with other preassigned assignments
    ///
    /// # Arguments
    ///
    /// * `fixed` - The fixed assignment to add
    ///
    /// # Errors
    ///
    /// Returns various `ProblemBuildError` variants for different constraint violations:
    /// - `DuplicateRequestId` if a request with the same ID already exists
    /// - `AssignmentOutsideTimeWindow` if the assignment is outside the time window
    /// - `AssignmentOutsideSpaceWindow` if the assignment is outside the space window
    /// - `AssignmentExceedsQuay` if the assignment extends beyond the quay
    /// - `PreassignedOverlap` if the assignment overlaps with existing preassigned assignments
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{ProblemBuilder, FixedAssignment, Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(10),
    ///     TimeDelta::new(5),
    ///     SpacePosition::new(20),
    ///     Cost::new(2),
    ///     Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// ).unwrap();
    ///
    /// let assignment = Assignment::new(request, SpacePosition::new(15), TimePoint::new(2));
    /// builder.add_preassigned(FixedAssignment::new(assignment)).unwrap();
    /// ```
    pub fn add_preassigned(
        &mut self,
        fixed: FixedAssignment<T, C>,
    ) -> Result<&mut Self, ProblemBuildError<T>> {
        let a = fixed.assignment();
        let r = a.request();
        let id = r.id();

        if self.unassigned.contains_key(&id) || self.preassigned.contains_key(&id) {
            return Err(ProblemBuildError::DuplicateRequestId(id));
        }

        let (tspan, sspan) = Self::assignment_spans(a);
        let tw = r.feasible_time_window();
        if !tw.contains_interval(&tspan) {
            return Err(ProblemBuildError::AssignmentOutsideTimeWindow(
                AssignmentOutsideTimeWindowError::new(id, tw, tspan),
            ));
        }

        let sw = r.feasible_space_window();
        if !sw.contains_interval(&sspan) {
            return Err(ProblemBuildError::AssignmentOutsideSpaceWindow(
                AssignmentOutsideSpaceWindowError::new(id, sw, sspan),
            ));
        }

        if sspan.end().value() > self.quay_length.value() {
            return Err(ProblemBuildError::AssignmentExceedsQuay(
                AssignmentExceedsQuayError::new(id, self.quay_length, sspan),
            ));
        }

        // Preassigned overlap check (only among fixed ones)
        for (&other_id, other_fixed) in &self.preassigned {
            let (ot, os) = Self::assignment_spans(other_fixed.assignment());
            if tspan.intersects(&ot) && sspan.intersects(&os) {
                return Err(ProblemBuildError::PreassignedOverlap(
                    PreassignedOverlapError::new(id, other_id),
                ));
            }
        }

        self.preassigned.insert(id, fixed);
        Ok(self)
    }

    /// Builds the final `Problem` instance from the current state.
    ///
    /// This consumes the builder's current state and returns a validated
    /// problem instance ready for optimization.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// // ... add requests ...
    /// let problem = builder.build();
    /// ```
    pub fn build(&self) -> Problem<T, C> {
        Problem::new(
            self.unassigned.clone(),
            self.preassigned.clone(),
            self.quay_length,
        )
    }
}

/// Statistics about a solution to the berth allocation problem.
///
/// This struct provides a summary of key quality metrics for a solution,
/// aggregating costs, waiting times, and position deviations across all
/// assigned requests.
///
/// # Type Parameters
///
/// * `T` - The numeric type used for time values (default: `i64`)
/// * `C` - The numeric type used for cost values (default: `i64`)
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{Solution, Assignment, Request, RequestId};
/// use dock_alloc_core::domain::*;
/// use std::collections::HashMap;
///
/// // Stats are typically created automatically when building solutions
/// let request = Request::new(
///     RequestId::new(1),
///     SpaceLength::new(10),
///     TimeDelta::new(5),
///     SpacePosition::new(20),
///     Cost::new(2),
///     Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
/// ).unwrap();
///
/// let assignment = Assignment::new(request, SpacePosition::new(25), TimePoint::new(3));
/// let mut assignments = HashMap::new();
/// assignments.insert(RequestId::new(1), assignment);
/// let solution = Solution::from_assignments(assignments);
///
/// let stats = solution.stats();
/// println!("Total cost: {}", stats.total_cost());
/// println!("Total waiting time: {}", stats.total_waiting_time());
/// println!("Total position deviation: {}", stats.total_target_position_deviation());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SolutionStats<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    total_cost: Cost<C>,
    total_waiting_time: TimeDelta<T>,
    total_target_position_deviation: SpaceLength,
}

impl<T, C> SolutionStats<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(
        total_cost: Cost<C>,
        total_waiting_time: TimeDelta<T>,
        total_target_position_deviation: SpaceLength,
    ) -> Self {
        SolutionStats {
            total_cost,
            total_waiting_time,
            total_target_position_deviation,
        }
    }

    /// Returns the total cost of the solution.
    ///
    /// This includes both waiting costs and position deviation costs
    /// summed across all assignments.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Solution, Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// use std::collections::HashMap;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    /// # let assignment = Assignment::new(request, SpacePosition::new(25), TimePoint::new(3));
    /// # let mut assignments = HashMap::new();
    /// # assignments.insert(RequestId::new(1), assignment);
    /// # let solution = Solution::from_assignments(assignments);
    ///
    /// println!("Solution cost: {}", solution.stats().total_cost());
    /// ```
    #[inline]
    pub fn total_cost(&self) -> Cost<C> {
        self.total_cost
    }

    /// Returns the total waiting time across all assignments.
    ///
    /// This is the sum of waiting times for all requests, where waiting time
    /// is the difference between the assignment start time and the request's
    /// arrival time (clamped to be non-negative).
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Solution, Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// use std::collections::HashMap;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    /// # let assignment = Assignment::new(request, SpacePosition::new(25), TimePoint::new(3));
    /// # let mut assignments = HashMap::new();
    /// # assignments.insert(RequestId::new(1), assignment);
    /// # let solution = Solution::from_assignments(assignments);
    ///
    /// println!("Total waiting time: {}", solution.stats().total_waiting_time());
    /// ```
    #[inline]
    pub fn total_waiting_time(&self) -> TimeDelta<T> {
        self.total_waiting_time
    }

    /// Returns the total target position deviation across all assignments.
    ///
    /// This is the sum of absolute deviations from target positions
    /// for all requests in the solution.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Solution, Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// use std::collections::HashMap;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    /// # let assignment = Assignment::new(request, SpacePosition::new(25), TimePoint::new(3));
    /// # let mut assignments = HashMap::new();
    /// # assignments.insert(RequestId::new(1), assignment);
    /// # let solution = Solution::from_assignments(assignments);
    ///
    /// println!("Total position deviation: {}", solution.stats().total_target_position_deviation());
    /// ```
    #[inline]
    pub fn total_target_position_deviation(&self) -> SpaceLength {
        self.total_target_position_deviation
    }
}

/// A solution to the berth allocation problem.
///
/// This struct represents a complete solution, containing assignments for
/// requests and automatically computed statistics about the solution quality.
/// Solutions are typically created from a set of assignments and automatically
/// calculate metrics like total cost, waiting time, and position deviation.
///
/// # Type Parameters
///
/// * `T` - The numeric type used for time values (default: `i64`)
/// * `C` - The numeric type used for cost values (default: `i64`)
///
/// # Examples
///
/// ```
/// use dock_alloc_model::{Solution, Assignment, Request, RequestId};
/// use dock_alloc_core::domain::*;
/// use std::collections::HashMap;
///
/// let request = Request::new(
///     RequestId::new(1),
///     SpaceLength::new(10),
///     TimeDelta::new(5),
///     SpacePosition::new(20),
///     Cost::new(2),
///     Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
/// ).unwrap();
///
/// let assignment = Assignment::new(request, SpacePosition::new(25), TimePoint::new(3));
/// let mut assignments = HashMap::new();
/// assignments.insert(RequestId::new(1), assignment);
///
/// let solution = Solution::from_assignments(assignments);
/// println!("Solution has {} assignments", solution.decisions().len());
/// println!("Total cost: {}", solution.stats().total_cost());
/// ```
#[derive(Debug, Clone)]
pub struct Solution<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    decisions: HashMap<RequestId, Assignment<T, C>>,
    stats: SolutionStats<T, C>,
}

impl<T, C> Solution<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
{
    /// Creates a new solution from a set of assignments.
    ///
    /// This method automatically computes solution statistics including
    /// total cost, waiting time, and position deviation.
    ///
    /// # Arguments
    ///
    /// * `assignments` - A map from request IDs to their assignments
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Solution, Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// use std::collections::HashMap;
    ///
    /// let request = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(10),
    ///     TimeDelta::new(5),
    ///     SpacePosition::new(20),
    ///     Cost::new(2),
    ///     Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// ).unwrap();
    ///
    /// let assignment = Assignment::new(request, SpacePosition::new(25), TimePoint::new(3));
    /// let mut assignments = HashMap::new();
    /// assignments.insert(RequestId::new(1), assignment);
    ///
    /// let solution = Solution::from_assignments(assignments);
    /// assert_eq!(solution.decisions().len(), 1);
    /// ```
    #[inline]
    pub fn from_assignments(assignments: HashMap<RequestId, Assignment<T, C>>) -> Self {
        let mut total_wait = TimeDelta::<T>::new(T::zero());
        let mut total_dev = SpaceLength::new(0);
        let mut total_cost = Cost::<C>::new(C::zero());

        for a in assignments.values() {
            let r = a.request();

            // Time (nonnegative wait)
            let wait = (a.start_time() - r.arrival_time())
                .clamp(TimeDelta::zero(), TimeDelta::new(T::max_value()));
            total_wait += wait;

            // Space
            let dev = a.start_position() - r.target_position();
            total_dev += dev;

            total_cost = total_cost + r.waiting_cost(wait) + r.target_position_deviation_cost(dev);
        }

        let stats = SolutionStats::new(total_cost, total_wait, total_dev);
        Self {
            decisions: assignments,
            stats,
        }
    }

    /// Returns a reference to the solution statistics.
    ///
    /// The statistics provide a summary of solution quality including
    /// total cost, waiting time, and position deviation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Solution, Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// use std::collections::HashMap;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    /// # let assignment = Assignment::new(request, SpacePosition::new(25), TimePoint::new(3));
    /// # let mut assignments = HashMap::new();
    /// # assignments.insert(RequestId::new(1), assignment);
    /// # let solution = Solution::from_assignments(assignments);
    ///
    /// let stats = solution.stats();
    /// println!("Total cost: {}", stats.total_cost());
    /// ```
    #[inline]
    pub fn stats(&self) -> &SolutionStats<T, C> {
        &self.stats
    }

    /// Returns a reference to the assignment decisions.
    ///
    /// This map contains the final assignments for all requests in the solution,
    /// mapping request IDs to their corresponding assignments.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_model::{Solution, Assignment, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    /// use std::collections::HashMap;
    /// # let request = Request::new(
    /// #     RequestId::new(1), SpaceLength::new(10), TimeDelta::new(5),
    /// #     SpacePosition::new(20), Cost::new(2), Cost::new(1),
    /// #     TimeInterval::new(TimePoint::new(0), TimePoint::new(10)),
    /// #     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(50))
    /// # ).unwrap();
    /// # let assignment = Assignment::new(request, SpacePosition::new(25), TimePoint::new(3));
    /// # let mut assignments = HashMap::new();
    /// # assignments.insert(RequestId::new(1), assignment);
    /// # let solution = Solution::from_assignments(assignments);
    ///
    /// let decisions = solution.decisions();
    /// if let Some(assignment) = decisions.get(&RequestId::new(1)) {
    ///     println!("Request 1 starts at position {}", assignment.start_position());
    /// }
    /// ```
    #[inline]
    pub fn decisions(&self) -> &HashMap<RequestId, Assignment<T, C>> {
        &self.decisions
    }
}

#[cfg(test)]
mod builder_tests {
    use super::*;
    use dock_alloc_core::domain::{
        Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
    };

    fn req_ok(id: u64, len: usize, proc_t: i64, t0: i64, t1: i64, s0: usize, s1: usize) -> Request {
        Request::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimeDelta::new(proc_t),
            SpacePosition::new(s0),
            Cost::new(1),
            Cost::new(1),
            TimeInterval::new(TimePoint::new(t0), TimePoint::new(t1)),
            SpaceInterval::new(SpacePosition::new(s0), SpacePosition::new(s1)),
        )
        .expect("valid request")
    }

    #[test]
    fn duplicate_ids_rejected() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(20));
        let r1 = req_ok(1, 4, 3, 0, 10, 0, 20);
        let r2 = req_ok(1, 5, 3, 0, 10, 0, 20);
        b.add_unassigned_request(r1).unwrap();
        assert!(matches!(
            b.add_unassigned_request(r2),
            Err(ProblemBuildError::DuplicateRequestId(_))
        ));
    }

    #[test]
    fn preassigned_outside_time_window_rejected() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(20));
        let r = req_ok(1, 4, 5, 10, 20, 0, 20);
        let a = Assignment::new(r, SpacePosition::new(0), TimePoint::new(16)); // [16,21) leaks past 20
        assert!(matches!(
            b.add_preassigned(FixedAssignment::new(a)),
            Err(ProblemBuildError::AssignmentOutsideTimeWindow(_))
        ));
    }

    #[test]
    fn preassigned_outside_space_window_rejected() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(20));
        let r = req_ok(1, 6, 2, 0, 10, 5, 12);
        let a = Assignment::new(r, SpacePosition::new(7), TimePoint::new(1)); // [7,13) leaks past 12
        assert!(matches!(
            b.add_preassigned(FixedAssignment::new(a)),
            Err(ProblemBuildError::AssignmentOutsideSpaceWindow(_))
        ));
    }

    #[test]
    fn preassigned_exceeds_quay_rejected() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(10));
        let r = req_ok(1, 6, 2, 0, 10, 0, 20);
        let a = Assignment::new(r, SpacePosition::new(6), TimePoint::new(1)); // [6,12) > quay 10
        assert!(matches!(
            b.add_preassigned(FixedAssignment::new(a)),
            Err(ProblemBuildError::AssignmentExceedsQuay(_))
        ));
    }

    #[test]
    fn overlapping_preassigned_rejected() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(20));
        let r1 = req_ok(1, 4, 5, 0, 20, 0, 20);
        let r2 = req_ok(2, 4, 5, 0, 20, 0, 20);
        b.add_preassigned(FixedAssignment::new(Assignment::new(
            r1,
            SpacePosition::new(5),
            TimePoint::new(2),
        )))
        .unwrap(); // t[2,7), s[5,9)
        let a2 = Assignment::new(r2, SpacePosition::new(7), TimePoint::new(4)); // t[4,9), s[7,11) -> intersects both axes
        assert!(matches!(
            b.add_preassigned(FixedAssignment::new(a2)),
            Err(ProblemBuildError::PreassignedOverlap(_))
        ));
    }

    #[test]
    fn build_ok_when_valid() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(20));
        let r1 = req_ok(1, 4, 3, 0, 10, 0, 20);
        let r2 = req_ok(2, 4, 3, 0, 10, 0, 20);
        b.add_unassigned_request(r1).unwrap();
        b.add_preassigned(FixedAssignment::new(Assignment::new(
            r2,
            SpacePosition::new(10),
            TimePoint::new(0),
        )))
        .unwrap();
        let p = b.build();
        assert_eq!(p.total_requests(), 2);
        assert_eq!(p.unassigned().len(), 1);
        assert_eq!(p.preassigned().len(), 1);
    }
}
