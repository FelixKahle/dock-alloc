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
use std::borrow::Cow;
use std::fmt::Display;
use std::{collections::HashMap, fmt::Debug, hash::Hash};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RequestId(u64);

impl RequestId {
    #[inline]
    pub const fn new(id: u64) -> Self {
        RequestId(id)
    }

    #[inline]
    pub const fn value(&self) -> u64 {
        self.0
    }
}

impl Display for RequestId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RequestId({})", self.0)
    }
}

impl From<u64> for RequestId {
    fn from(value: u64) -> Self {
        RequestId(value)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TimeWindowTooShortError<T: PrimInt + Signed> {
    id: RequestId,
    processing: TimeDelta<T>,
    window: TimeInterval<T>,
}

impl<T: PrimInt + Signed> TimeWindowTooShortError<T> {
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

    pub fn id(&self) -> RequestId {
        self.id
    }

    pub fn processing_duration(&self) -> TimeDelta<T> {
        self.processing
    }

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpaceWindowTooShortError {
    id: RequestId,
    length: SpaceLength,
    window: SpaceInterval,
}

impl SpaceWindowTooShortError {
    pub fn new(id: RequestId, length: SpaceLength, window: SpaceInterval) -> Self {
        SpaceWindowTooShortError { id, length, window }
    }

    pub fn id(&self) -> RequestId {
        self.id
    }

    pub fn length(&self) -> SpaceLength {
        self.length
    }

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

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.length
    }

    #[inline]
    pub fn arrival_time(&self) -> TimePoint<T> {
        self.feasible_time_window.start()
    }

    #[inline]
    pub fn processing_duration(&self) -> TimeDelta<T> {
        self.processing_duration
    }

    #[inline]
    pub fn target_position(&self) -> SpacePosition {
        self.target_position
    }

    #[inline]
    pub fn cost_per_delay(&self) -> Cost<C> {
        self.cost_per_delay
    }

    #[inline]
    pub fn cost_per_position_deviation(&self) -> Cost<C> {
        self.cost_per_position_deviation
    }

    #[inline]
    pub fn feasible_time_window(&self) -> TimeInterval<T> {
        self.feasible_time_window
    }

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

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Assignment<'r, T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    request: Cow<'r, Request<T, C>>,
    start_position: SpacePosition,
    start_time: TimePoint<T>,
}

impl<'r, T, C> Assignment<'r, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    pub fn borrowed(
        request: &'r Request<T, C>,
        start_position: SpacePosition,
        start_time: TimePoint<T>,
    ) -> Self {
        Self {
            request: Cow::Borrowed(request),
            start_position,
            start_time,
        }
    }

    #[inline]
    pub fn owned(
        request: Request<T, C>,
        start_position: SpacePosition,
        start_time: TimePoint<T>,
    ) -> Self {
        Self {
            request: Cow::Owned(request),
            start_position,
            start_time,
        }
    }

    #[inline]
    pub fn into_owned(self) -> Assignment<'static, T, C>
    where
        Request<T, C>: Clone,
    {
        Assignment {
            request: Cow::Owned(self.request.into_owned()),
            start_position: self.start_position,
            start_time: self.start_time,
        }
    }

    #[inline]
    pub fn request(&self) -> &Request<T, C> {
        &self.request
    }

    #[inline]
    pub fn start_position(&self) -> SpacePosition {
        self.start_position
    }

    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }
}

impl<'r, T, C> Display for Assignment<'r, T, C>
where
    T: PrimInt + Signed + Display,
    C: PrimInt + Signed + Display,
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
pub struct FixedRequest<'r, T = i64, C = i64>(&'r Request<T, C>)
where
    T: PrimInt + Signed,
    C: PrimInt + Signed;

impl<'r, T, C> FixedRequest<'r, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn new(r: &'r Request<T, C>) -> Self {
        Self(r)
    }

    pub fn request(&self) -> &'r Request<T, C> {
        self.0
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FixedAssignment<'r, T = i64, C = i64>(Assignment<'r, T, C>)
where
    T: PrimInt + Signed,
    C: PrimInt + Signed;

impl<'r, T, C> FixedAssignment<'r, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    pub fn new(a: Assignment<'r, T, C>) -> Self {
        Self(a)
    }

    pub fn assignment(&self) -> &Assignment<'_, T, C> {
        &self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentOutsideTimeWindowError<T: PrimInt + Signed> {
    id: RequestId,
    time_window: TimeInterval<T>,
    assigned_interval: TimeInterval<T>,
}

impl<T: PrimInt + Signed> AssignmentOutsideTimeWindowError<T> {
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

    pub fn id(&self) -> RequestId {
        self.id
    }

    pub fn time_window(&self) -> TimeInterval<T> {
        self.time_window
    }

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentOutsideSpaceWindowError {
    id: RequestId,
    space_window: SpaceInterval,
    assigned_interval: SpaceInterval,
}

impl AssignmentOutsideSpaceWindowError {
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

    pub fn id(&self) -> RequestId {
        self.id
    }

    pub fn space_window(&self) -> SpaceInterval {
        self.space_window
    }

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentExceedsQuayError {
    id: RequestId,
    quay_length: SpaceLength,
    assigned_interval: SpaceInterval,
}

impl AssignmentExceedsQuayError {
    pub fn new(id: RequestId, quay_length: SpaceLength, assigned_interval: SpaceInterval) -> Self {
        AssignmentExceedsQuayError {
            id,
            quay_length,
            assigned_interval,
        }
    }

    pub fn id(&self) -> RequestId {
        self.id
    }

    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PreassignedOverlapError {
    a: RequestId,
    b: RequestId,
}

impl PreassignedOverlapError {
    pub fn new(a: RequestId, b: RequestId) -> Self {
        PreassignedOverlapError { a, b }
    }

    pub fn request_a(&self) -> RequestId {
        self.a
    }

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Problem<'p, T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    unassigned: HashMap<RequestId, MoveableRequest<T, C>>,
    preassigned: HashMap<RequestId, FixedAssignment<'p, T, C>>,
    quay_length: SpaceLength,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProblemRequest<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    Moveable(&'p MoveableRequest<T, C>),
    Fixed(FixedRequest<'p, T, C>),
}

impl<'p, T, C> Display for ProblemRequest<'p, T, C>
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

impl<'p, T, C> Problem<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(
        unassigned: HashMap<RequestId, MoveableRequest<T, C>>,
        preassigned: HashMap<RequestId, FixedAssignment<'p, T, C>>,
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
    pub fn preassigned(&self) -> &HashMap<RequestId, FixedAssignment<'_, T, C>> {
        &self.preassigned
    }

    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

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

    pub fn iter_fixed_assignments(&self) -> impl Iterator<Item = &FixedAssignment<'_, T, C>> {
        self.preassigned.values()
    }
}

pub type BerthAllocationProblem<'a> = Problem<'a, i64, i64>;

pub struct ProblemBuilder<'p, T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    unassigned: HashMap<RequestId, MoveableRequest<T, C>>,
    preassigned: HashMap<RequestId, FixedAssignment<'p, T, C>>,
    quay_length: SpaceLength,
}

impl<'a, T, C> ProblemBuilder<'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    pub fn new(quay_length: SpaceLength) -> Self {
        Self {
            unassigned: HashMap::new(),
            preassigned: HashMap::new(),
            quay_length,
        }
    }

    pub fn quay_length(&mut self, length: SpaceLength) -> &mut Self {
        self.quay_length = length;
        self
    }

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

    pub fn add_preassigned(
        &mut self,
        fixed: FixedAssignment<'a, T, C>,
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

    pub fn build(&'_ self) -> Problem<'_, T, C> {
        Problem::new(
            self.unassigned.clone(),
            self.preassigned.clone(),
            self.quay_length,
        )
    }
}

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

    #[inline]
    pub fn total_cost(&self) -> Cost<C> {
        self.total_cost
    }

    #[inline]
    pub fn total_waiting_time(&self) -> TimeDelta<T> {
        self.total_waiting_time
    }

    #[inline]
    pub fn total_target_position_deviation(&self) -> SpaceLength {
        self.total_target_position_deviation
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Solution<T = i64, C = i64>
where
    T: PrimInt + Signed + 'static,
    C: PrimInt + Signed + 'static,
{
    decisions: HashMap<RequestId, Assignment<'static, T, C>>,
    stats: SolutionStats<T, C>,
}

impl<T, C> Solution<T, C>
where
    T: PrimInt + Signed + 'static,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize> + 'static,
{
    #[inline]
    pub fn from_assignments(assignments: HashMap<RequestId, Assignment<'static, T, C>>) -> Self {
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

    #[inline]
    pub fn stats(&self) -> &SolutionStats<T, C> {
        &self.stats
    }

    #[inline]
    pub fn decisions(&'_ self) -> &HashMap<RequestId, Assignment<'_, T, C>> {
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
    fn test_duplicate_ids_rejected() {
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
    fn test_preassigned_outside_time_window_rejected() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(20));
        let r = req_ok(1, 4, 5, 10, 20, 0, 20);
        let a = Assignment::borrowed(&r, SpacePosition::new(0), TimePoint::new(16)); // [16,21) leaks past 20
        assert!(matches!(
            b.add_preassigned(FixedAssignment::new(a)),
            Err(ProblemBuildError::AssignmentOutsideTimeWindow(_))
        ));
    }

    #[test]
    fn test_preassigned_outside_space_window_rejected() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(20));
        let r = req_ok(1, 6, 2, 0, 10, 5, 12);
        let a = Assignment::borrowed(&r, SpacePosition::new(7), TimePoint::new(1)); // [7,13) leaks past 12
        assert!(matches!(
            b.add_preassigned(FixedAssignment::new(a)),
            Err(ProblemBuildError::AssignmentOutsideSpaceWindow(_))
        ));
    }

    #[test]
    fn test_preassigned_exceeds_quay_rejected() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(10));
        let r = req_ok(1, 6, 2, 0, 10, 0, 20);
        let a = Assignment::borrowed(&r, SpacePosition::new(6), TimePoint::new(1)); // [6,12) > quay 10
        assert!(matches!(
            b.add_preassigned(FixedAssignment::new(a)),
            Err(ProblemBuildError::AssignmentExceedsQuay(_))
        ));
    }

    #[test]
    fn test_overlapping_preassigned_rejected() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(20));
        let r1 = req_ok(1, 4, 5, 0, 20, 0, 20);
        let r2 = req_ok(2, 4, 5, 0, 20, 0, 20);
        b.add_preassigned(FixedAssignment::new(Assignment::borrowed(
            &r1,
            SpacePosition::new(5),
            TimePoint::new(2),
        )))
        .unwrap(); // t[2,7), s[5,9)
        let a2 = Assignment::borrowed(&r2, SpacePosition::new(7), TimePoint::new(4)); // t[4,9), s[7,11) -> intersects both axes
        assert!(matches!(
            b.add_preassigned(FixedAssignment::new(a2)),
            Err(ProblemBuildError::PreassignedOverlap(_))
        ));
    }

    #[test]
    fn test_build_ok_when_valid() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(20));
        let r1 = req_ok(1, 4, 3, 0, 10, 0, 20);
        let r2 = req_ok(2, 4, 3, 0, 10, 0, 20);
        b.add_unassigned_request(r1).unwrap();
        b.add_preassigned(FixedAssignment::new(Assignment::borrowed(
            &r2,
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
