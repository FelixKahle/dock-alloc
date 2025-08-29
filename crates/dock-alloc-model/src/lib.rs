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
    /// Compares two `Request` instances for equality based on their unique identifiers.
    ///
    /// Two `Request` instances are considered equal if they have the same `id`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req1 = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let req2 = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(150),
    ///     TimeDelta::new(15),
    ///     SpacePosition::new(60),
    ///     Cost::new(6),
    ///     Cost::new(3),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let req3 = Request::new(
    ///     RequestId::new(2),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req1, req2); // Same id
    /// assert_ne!(req1, req3); // Different id
    /// ```
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
    /// Hashes the `Request` instance based on its unique identifier.
    ///
    /// This ensures that two `Request` instances with the same `id`
    /// will produce the same hash value.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    /// use std::hash::{Hash, DefaultHasher, Hasher};
    ///
    /// let req1 = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let req2 = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(150),
    ///     TimeDelta::new(15),
    ///     SpacePosition::new(60),
    ///     Cost::new(6),
    ///     Cost::new(3),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let req3 = Request::new(
    ///     RequestId::new(2),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let mut hasher = DefaultHasher::new();
    /// req1.hash(&mut hasher);
    /// let hash1 = hasher.finish();
    /// let mut hasher = DefaultHasher::new();
    /// req2.hash(&mut hasher);
    /// let hash2 = hasher.finish();
    /// let mut hasher = DefaultHasher::new();
    /// req3.hash(&mut hasher);
    /// let hash3 = hasher.finish();
    /// assert_eq!(hash1, hash2); // Same id -> same hash
    /// assert_ne!(hash1, hash3); // Different id -> different hash
    /// ```
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
    /// Compares two `Request` instances for ordering based on their unique identifiers.
    ///
    /// The ordering is determined by the `id` field of the `Request`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req1 = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let req2 = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(150),
    ///     TimeDelta::new(15),
    ///     SpacePosition::new(60),
    ///     Cost::new(6),
    ///     Cost::new(3),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let req3 = Request::new(
    ///     RequestId::new(2),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req1.partial_cmp(&req2), Some(std::cmp::Ordering::Equal)); // Same id
    /// assert_eq!(req1.partial_cmp(&req3), Some(std::cmp::Ordering::Less)); // req1.id < req3.id
    /// assert_eq!(req3.partial_cmp(&req1), Some(std::cmp::Ordering::Greater)); // req3.id > req1.id
    /// ```
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
    /// Compares two `Request` instances for ordering based on their unique identifiers.
    ///
    /// The ordering is determined by the `id` field of the `Request`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req1 = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let req2 = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(150),
    ///     TimeDelta::new(15),
    ///     SpacePosition::new(60),
    ///     Cost::new(6),
    ///     Cost::new(3),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let req3 = Request::new(
    ///     RequestId::new(2),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req1.cmp(&req2), std::cmp::Ordering::Equal); // Same id
    /// assert_eq!(req1.cmp(&req3), std::cmp::Ordering::Less); // req1.id < req3.id
    /// assert_eq!(req3.cmp(&req1), std::cmp::Ordering::Greater); // req3.id > req1.id
    /// ```
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
    /// Creates a new `Request` instance with the provided parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req.id(), RequestId::new(1));
    /// assert_eq!(req.length(), SpaceLength::new(100));
    /// assert_eq!(req.processing_duration(), TimeDelta::new(10));
    /// assert_eq!(req.target_position(), SpacePosition::new(50));
    /// assert_eq!(req.cost_per_delay(), Cost::new(5));
    /// assert_eq!(req.cost_per_position_deviation(), Cost::new(2));
    /// assert_eq!(req.feasible_time_window(), TimeInterval::new(TimePoint::new(0), TimePoint::new(100)));
    /// assert_eq!(req.feasible_space_window(), SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)));
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
    ) -> Self {
        Request {
            id,
            length,
            processing_duration,
            target_position,
            cost_per_delay,
            cost_per_position_deviation,
            feasible_time_window,
            feasible_space_window,
        }
    }

    /// Returns the unique identifier of the request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req.id(), RequestId::new(1));
    /// ```
    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    /// Returns the length of the request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req.length(), SpaceLength::new(100));
    /// ```
    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.length
    }

    /// Returns the arrival time of the request, which is the start of its feasible time window.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req.arrival_time(), TimePoint::new(0));
    /// ```
    #[inline]
    pub fn arrival_time(&self) -> TimePoint<T> {
        self.feasible_time_window.start()
    }

    /// Returns the processing duration of the request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req.processing_duration(), TimeDelta::new(10));
    /// ```
    #[inline]
    pub fn processing_duration(&self) -> TimeDelta<T> {
        self.processing_duration
    }

    /// Returns the target position of the request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req.target_position(), SpacePosition::new(50));
    /// ```
    #[inline]
    pub fn target_position(&self) -> SpacePosition {
        self.target_position
    }

    /// Returns the cost per unit of delay for the request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req.cost_per_delay(), Cost::new(5));
    /// ```
    #[inline]
    pub fn cost_per_delay(&self) -> Cost<C> {
        self.cost_per_delay
    }

    /// Returns the cost per unit of position deviation for the request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req.cost_per_position_deviation(), Cost::new(2));
    /// ```
    #[inline]
    pub fn cost_per_position_deviation(&self) -> Cost<C> {
        self.cost_per_position_deviation
    }

    /// Returns the feasible time window for the request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req.feasible_time_window(), TimeInterval::new(TimePoint::new(0), TimePoint::new(100)));
    /// ```
    #[inline]
    pub fn feasible_time_window(&self) -> TimeInterval<T> {
        self.feasible_time_window
    }

    /// Returns the feasible space window for the request.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// assert_eq!(req.feasible_space_window(), SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)));
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
    /// Calculates the waiting cost for a given waiting time.
    ///
    /// # Panics
    ///
    /// Panics if the waiting time value does not fit into the cost type `C`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let waiting_time = TimeDelta::new(3);
    /// let cost = req.waiting_cost(waiting_time);
    /// assert_eq!(cost, Cost::new(15)); // 5 * 3
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
    /// Calculates the target position deviation cost for a given deviation.
    ///
    /// # Panics
    ///
    /// Panics if the deviation value does not fit into the cost type `C`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let deviation = SpaceLength::new(4);
    /// let cost = req.target_position_deviation_cost(deviation);
    /// assert_eq!(cost, Cost::new(8)); // 2 * 4
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
    /// Formats the `Request` for display purposes.
    ///
    /// Formats the `Request` in a human-readable form, displaying all its attributes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// println!("{}", req);
    /// ```
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
    /// Creates a new `Assignment` instance with the provided request, start position, and start time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId, Assignment};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let assignment = Assignment::new(req, SpacePosition::new(30), TimePoint::new(5));
    /// assert_eq!(assignment.request(), &req);
    /// assert_eq!(assignment.start_position(), SpacePosition::new(30));
    /// assert_eq!(assignment.start_time(), TimePoint::new(5));
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

    /// Returns a reference to the request associated with the assignment.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId, Assignment};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let assignment = Assignment::new(req, SpacePosition::new(30), TimePoint::new(5));
    /// assert_eq!(assignment.request(), &req);
    /// ```
    #[inline]
    pub fn request(&self) -> &Request<T, C> {
        &self.request
    }

    /// Returns the start position of the assignment.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId, Assignment};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let assignment = Assignment::new(req, SpacePosition::new(30), TimePoint::new(5));
    /// assert_eq!(assignment.start_position(), SpacePosition::new(30));
    /// ```
    #[inline]
    pub fn start_position(&self) -> SpacePosition {
        self.start_position
    }

    /// Returns the start time of the assignment.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId, Assignment};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let assignment = Assignment::new(req, SpacePosition::new(30), TimePoint::new(5));
    /// assert_eq!(assignment.start_time(), TimePoint::new(5));
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
    /// Formats the `Assignment` for display purposes.
    ///
    /// Formats the `Assignment` in a human-readable form,
    /// displaying the request ID, start position, and start time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId, Assignment};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let assignment = Assignment::new(req, SpacePosition::new(30), TimePoint::new(5));
    /// println!("{}", assignment);
    /// ```
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

/// An entry in the problem, which can be either an unassigned
/// request or a pre-assigned assignment.
///
/// This enum encapsulates the two possible states of a problem entry,
/// either being an unassigned request or a pre-assigned assignment.
/// The solver must respect pre-assigned assignments and only assign unassigned requests.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProblemEntry<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    Unassigned(Request<T, C>),
    PreAssigned(Assignment<T, C>),
}

impl<T> Display for ProblemEntry<T>
where
    T: PrimInt + Signed + Display,
{
    /// Formats the `ProblemEntry` for display purposes.
    ///
    /// Formats the `ProblemEntry` in a human-readable form,
    /// indicating whether it is an unassigned request or a pre-assigned assignment.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId, Assignment, ProblemEntry};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let assignment = Assignment::new(req, SpacePosition::new(30), TimePoint::new(5));
    /// let entry1 = ProblemEntry::Unassigned(req);
    /// let entry2 = ProblemEntry::PreAssigned(assignment);
    /// println!("{}", entry1);
    /// println!("{}", entry2);
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProblemEntry::Unassigned(request) => write!(f, "Unassigned({})", request),
            ProblemEntry::PreAssigned(assignment) => write!(f, "PreAssigned({})", assignment),
        }
    }
}

/// A berth allocation problem instance.
///
/// This struct encapsulates the details of a berth allocation problem,
/// including the set of problem entries (requests and pre-assigned assignments)
/// and the length of the quay.
#[derive(Debug, Clone)]
pub struct Problem<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    entries: HashMap<RequestId, ProblemEntry<T, C>>,
    quay_length: SpaceLength,
}

impl<T, C> Problem<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    /// Creates a new `Problem` instance with the provided entries and quay length.
    #[inline]
    fn new(entries: HashMap<RequestId, ProblemEntry<T, C>>, quay_length: SpaceLength) -> Self {
        Problem {
            entries,
            quay_length,
        }
    }

    /// Returns a reference to the entries in the problem.
    #[inline]
    pub fn entries(&self) -> &HashMap<RequestId, ProblemEntry<T, C>> {
        &self.entries
    }

    /// Returns a reference to the problem entry for the given request ID, if it exists.
    #[inline]
    pub fn entry(&self, id: RequestId) -> Option<&ProblemEntry<T, C>> {
        self.entries.get(&id)
    }

    /// Returns the length of the quay.
    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }
}

pub type BerthAllocationProblem = Problem<i64, i64>;

pub struct ProblemBuilder<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    entries: HashMap<RequestId, ProblemEntry<T, C>>,
    quay_length: SpaceLength,
}

impl<T, C> ProblemBuilder<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    /// Creates a new `ProblemBuilder` instance with the specified quay length.
    pub fn new(quay_length: SpaceLength) -> Self {
        Self {
            entries: HashMap::new(),
            quay_length,
        }
    }

    /// Sets the quay length for the problem.
    pub fn quay_length(&mut self, length: SpaceLength) -> &mut Self {
        self.quay_length = length;
        self
    }

    /// Adds an unassigned request to the problem.
    pub fn add_unassigned_request(&mut self, request: Request<T, C>) -> &mut Self {
        self.entries
            .insert(request.id(), ProblemEntry::Unassigned(request));
        self
    }

    /// Adds a pre-assigned assignment to the problem.
    pub fn add_preassigned(&mut self, assignment: Assignment<T, C>) -> &mut Self {
        self.entries.insert(
            assignment.request().id(),
            ProblemEntry::PreAssigned(assignment),
        );
        self
    }

    /// Builds and returns the `Problem` instance.
    pub fn build(&self) -> Problem<T, C> {
        Problem::new(self.entries.clone(), self.quay_length)
    }
}

/// Statistics about a solution to the berth allocation problem.
///
/// This struct encapsulates key metrics of a solution, including total cost,
/// total waiting time, and total target position deviation.
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
    /// Creates a new `SolutionStats` instance with the provided metrics.
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
    #[inline]
    pub fn total_cost(&self) -> Cost<C> {
        self.total_cost
    }

    /// Returns the total waiting time of the solution.
    #[inline]
    pub fn total_waiting_time(&self) -> TimeDelta<T> {
        self.total_waiting_time
    }

    /// Returns the total target position deviation of the solution.
    #[inline]
    pub fn total_target_position_deviation(&self) -> SpaceLength {
        self.total_target_position_deviation
    }
}

/// A solution to the berth allocation problem.
///
/// This struct encapsulates the decisions made in the solution,
/// including the assignments of requests and the associated statistics.
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
    /// Creates a new `Solution` instance from the provided assignments.
    ///
    /// Calculates the total cost, total waiting time, and total target position deviation
    /// based on the assignments and their associated requests.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId, Assignment, Solution};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let assignment = Assignment::new(req, SpacePosition::new(30), TimePoint::new(5));
    /// let mut assignments = std::collections::HashMap::new();
    /// assignments.insert(req.id(), assignment);
    /// let solution = Solution::from_assignments(assignments);
    /// println!("Total cost: {}", solution.stats().total_cost());
    /// println!("Total waiting time: {}", solution.stats().total_waiting_time());
    /// println!("Total target position deviation: {}", solution.stats().total_target_position_deviation());
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
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId, Assignment, Solution};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let assignment = Assignment::new(req, SpacePosition::new(30), TimePoint::new(5));
    /// let mut assignments = std::collections::HashMap::new();
    /// assignments.insert(req.id(), assignment);
    /// let solution = Solution::from_assignments(assignments);
    /// let stats = solution.stats();
    /// ```
    #[inline]
    pub fn stats(&self) -> &SolutionStats<T, C> {
        &self.stats
    }

    /// Returns a reference to the decisions made in the solution.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimePoint, TimeDelta, TimeInterval, SpaceInterval, Cost};
    /// use dock_alloc_model::{Request, RequestId, Assignment, Solution};
    ///
    /// let req = Request::new(
    ///     RequestId::new(1),
    ///     SpaceLength::new(100),
    ///     TimeDelta::new(10),
    ///     SpacePosition::new(50),
    ///     Cost::new(5),
    ///     Cost::new(2),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)),
    /// );
    /// let assignment = Assignment::new(req, SpacePosition::new(30), TimePoint::new(5));
    /// let mut assignments = std::collections::HashMap::new();
    /// assignments.insert(req.id(), assignment);
    /// let solution = Solution::from_assignments(assignments);
    /// let decisions = solution.decisions();
    /// ```
    #[inline]
    pub fn decisions(&self) -> &HashMap<RequestId, Assignment<T, C>> {
        &self.decisions
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dock_alloc_core::domain::{
        Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
    };
    use std::collections::HashMap;

    fn create_test_request(id: u64, arrival_time: i64, target_pos: usize) -> Request {
        Request::new(
            RequestId::new(id),
            SpaceLength::new(100),
            TimeDelta::new(20),
            SpacePosition::new(target_pos),
            Cost::new(10), // cost per unit of delay
            Cost::new(5),  // cost per unit of position deviation
            TimeInterval::new(
                TimePoint::new(arrival_time),
                TimePoint::new(arrival_time + 100),
            ),
            SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(500)),
        )
    }

    #[test]
    fn test_solution_stats_with_delay_and_deviation() {
        let req = create_test_request(1, 50, 100);
        // Expected wait: 60 (start_time) - 50 (arrival_time) = 10
        // Expected deviation: |120 (start_pos) - 100 (target_pos)| = 20
        // Expected wait cost: 10 (wait) * 10 (cost_per_delay) = 100
        // Expected deviation cost: 20 (dev) * 5 (cost_per_dev) = 100
        // Expected total cost: 100 + 100 = 200
        let assignment = Assignment::new(req, SpacePosition::new(120), TimePoint::new(60));

        let mut assignments = HashMap::new();
        assignments.insert(req.id(), assignment);

        let solution = Solution::from_assignments(assignments);
        let stats = solution.stats();

        assert_eq!(stats.total_waiting_time(), TimeDelta::new(10));
        assert_eq!(
            stats.total_target_position_deviation(),
            SpaceLength::new(20)
        );
        assert_eq!(stats.total_cost(), Cost::new(200));
    }

    #[test]
    fn test_solution_stats_perfect_assignment() {
        let req = create_test_request(1, 50, 100);
        let assignment = Assignment::new(req, SpacePosition::new(100), TimePoint::new(50));

        let mut assignments = HashMap::new();
        assignments.insert(req.id(), assignment);

        let solution = Solution::from_assignments(assignments);
        let stats = solution.stats();

        assert_eq!(stats.total_waiting_time(), TimeDelta::new(0));
        assert_eq!(stats.total_target_position_deviation(), SpaceLength::new(0));
        assert_eq!(stats.total_cost(), Cost::new(0));
    }

    #[test]
    fn test_solution_stats_summation_with_multiple_assignments() {
        let req1 = create_test_request(1, 50, 100); // wait: 10, dev: 20, cost: 200
        let req2 = create_test_request(2, 80, 200); // wait: 5,  dev: 10, cost: 100 (5*10 + 10*5)

        let ass1 = Assignment::new(req1, SpacePosition::new(120), TimePoint::new(60));
        let ass2 = Assignment::new(req2, SpacePosition::new(190), TimePoint::new(85));

        let mut assignments = HashMap::new();
        assignments.insert(req1.id(), ass1);
        assignments.insert(req2.id(), ass2);

        let solution = Solution::from_assignments(assignments);
        let stats = solution.stats();

        assert_eq!(stats.total_waiting_time(), TimeDelta::new(15)); // 10 + 5
        assert_eq!(
            stats.total_target_position_deviation(),
            SpaceLength::new(30)
        ); // 20 + 10
        assert_eq!(stats.total_cost(), Cost::new(300)); // 200 + 100
    }

    #[test]
    fn test_solution_stats_clamps_early_arrival_wait_time() {
        // If an assignment starts *before* the request's arrival time, the wait time
        // should be 0, not negative.
        let req = create_test_request(1, 50, 100); // Arrival is at time 50
        let assignment = Assignment::new(req, SpacePosition::new(100), TimePoint::new(40)); // Starts at 40

        let mut assignments = HashMap::new();
        assignments.insert(req.id(), assignment);

        let solution = Solution::from_assignments(assignments);
        let stats = solution.stats();

        assert_eq!(stats.total_waiting_time(), TimeDelta::new(0));
        assert_eq!(stats.total_cost(), Cost::new(0)); // No deviation, and wait cost is 0
    }

    #[test]
    fn test_empty_solution_has_zero_stats() {
        let assignments: HashMap<RequestId, Assignment> = HashMap::new();
        let solution = Solution::from_assignments(assignments);
        let stats = solution.stats();

        assert_eq!(stats.total_cost(), Cost::new(0));
        assert_eq!(stats.total_waiting_time(), TimeDelta::new(0));
        assert_eq!(stats.total_target_position_deviation(), SpaceLength::new(0));
    }
}
