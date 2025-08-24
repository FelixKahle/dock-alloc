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

//! # Dock Allocation Model
//!
//! `dock_alloc_model` provides the core data structures for defining and representing
//! berth allocation problems (BAP). It serves as a foundational layer for developing
//! optimization solvers, simulators, or management systems that deal with the
//! allocation of resources along a one-dimensional space over time.
//!
//! The crate is designed to be **solver-agnostic**, focusing solely on providing a
//! robust, type-safe, and validated model of the problem domain.
//!
//! ## Core Concepts
//!
//! The main components of the model are:
//!
//! - **`Request`**: Represents a single need for a time-space allocation. A `Request`
//!   encapsulates all necessary constraints, such as physical length, required processing
//!   time, feasible time and space windows, and cost parameters for delays or deviations.
//!
//! - **`Problem`**: Defines a complete, self-contained problem instance. It consists of a
//!   set of `Request`s, the total `quay_length`, and the status of each request—either
//!   `Unassigned` (to be scheduled by a solver) or `PreAssigned` (a fixed, immovable
//!   booking). The `Problem` constructor performs rigorous validation, such as checking for
//!   overlaps between pre-assigned requests.
//!
//! - **`Decision` & `Solution`**: These structs represent the output of a solver. A `Decision`
//!   is a choice for a single request (either `Assign` it to a specific time/place or `Drop` it),
//!   and a `Solution` is a complete collection of decisions for a `Problem`. The `Solution`
//!   constructor provides a comprehensive validation layer to ensure the solver's output is
//!   feasible and correct according to the problem's rules.
//!
//! ## An Abstract `Request`
//!
//! It's important to note that a `Request` does not have to be a vessel. It is an
//! abstract representation of any space-time requirement. For example, you can model:
//!
//! - **A maintenance window**: By creating a `Request` with a hard `feasible_time_window`
//!   and `feasible_space_window` constraint, zero costs, and treating it as a `PreAssigned` entry
//!   in the `Problem`.
//! - **A no-go zone**: Similar to a maintenance window, blocking off a part of the quay
//!   for a specific duration.
//! - **Any other resource booking**: The generic nature of the model allows it to be adapted
//!   to other domains beyond maritime logistics.
//!
//! ## Example
//!
//! Here is a minimal example of creating a simple berth allocation problem.
//!
//! ```
//! use std::collections::HashSet;
//! use dock_alloc_core::domain::{
//!     Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
//! };
//! use dock_alloc_model::{Problem, ProblemEntry, Request, RequestId};
//!
//! // 1. Define the requests.
//! let request1 = Request::new(
//!     RequestId::new(1),
//!     SpaceLength::new(150), // length of 150 units
//!     TimeDelta::new(3600),  // needs 1 hour
//!     SpacePosition::new(100), // prefers position 100
//!     Cost::new(10),         // cost per second of delay
//!     Cost::new(5),          // cost per meter of deviation
//!     TimeInterval::new(TimePoint::new(0), TimePoint::new(86400)), // feasible anytime today
//!     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(500)), // can berth anywhere up to 500
//!     Some(Cost::new(10000)), // can be dropped for a penalty
//! ).unwrap();
//!
//! let requests = HashSet::from([request1]);
//!
//! // 2. Define which requests are to be scheduled.
//! let entries = HashSet::from([ProblemEntry::Unassigned(RequestId::new(1))]);
//!
//! // 3. Create the problem instance with a quay of length 1000.
//! let quay_length = SpaceLength::new(1000);
//! let problem = Problem::new(requests, entries, quay_length);
//!
//! assert!(problem.is_ok());
//! ```

#![allow(dead_code)]

use dock_alloc_core::domain::{
    Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use num_traits::{PrimInt, Signed, Zero};
use std::fmt::Display;
use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
};

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RequestTimeWindowTooShortError<TimeType: PrimInt + Signed> {
    feasible_time_window: TimeInterval<TimeType>,
    processing_duration: TimeDelta<TimeType>,
}

impl<TimeType: PrimInt + Signed> RequestTimeWindowTooShortError<TimeType> {
    #[inline]
    pub fn new(
        feasible_time_window: TimeInterval<TimeType>,
        processing_duration: TimeDelta<TimeType>,
    ) -> Self {
        Self {
            feasible_time_window,
            processing_duration,
        }
    }

    #[inline]
    pub fn feasible_time_window(&self) -> TimeInterval<TimeType> {
        self.feasible_time_window
    }

    #[inline]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RequestSpaceWindowTooShortError {
    feasible_space_window: SpaceInterval,
    length: SpaceLength,
}

impl RequestSpaceWindowTooShortError {
    pub fn new(feasible_space_window: SpaceInterval, length: SpaceLength) -> Self {
        Self {
            feasible_space_window,
            length,
        }
    }

    #[inline]
    pub fn feasible_space_window(&self) -> SpaceInterval {
        self.feasible_space_window
    }

    #[inline]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RequestCreationError<TimeType: PrimInt + Signed> {
    TimeWindowTooShort(RequestTimeWindowTooShortError<TimeType>),
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

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.length
    }

    #[inline]
    pub fn arrival_time(&self) -> TimePoint<TimeType> {
        self.feasible_time_window.start()
    }

    #[inline]
    pub fn processing_duration(&self) -> TimeDelta<TimeType> {
        self.processing_duration
    }

    #[inline]
    pub fn target_position(&self) -> SpacePosition {
        self.target_position
    }

    #[inline]
    pub fn cost_per_delay(&self) -> Cost<CostType> {
        self.cost_per_delay
    }

    #[inline]
    pub fn cost_per_position_deviation(&self) -> Cost<CostType> {
        self.cost_per_position_deviation
    }

    #[inline]
    pub fn feasible_time_window(&self) -> TimeInterval<TimeType> {
        self.feasible_time_window
    }

    #[inline]
    pub fn feasible_space_window(&self) -> SpaceInterval {
        self.feasible_space_window
    }

    #[inline]
    pub fn drop_penalty(&self) -> Option<Cost<CostType>> {
        self.drop_penalty
    }

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Assignment<TimeType = i64>
where
    TimeType: PrimInt + Signed,
{
    request_id: RequestId,
    start_position: SpacePosition,
    start_time: TimePoint<TimeType>,
}

impl<TimeType> Assignment<TimeType>
where
    TimeType: PrimInt + Signed,
{
    #[inline]
    pub fn new(
        request_id: RequestId,
        start_position: SpacePosition,
        start_time: TimePoint<TimeType>,
    ) -> Self {
        Self {
            request_id,
            start_position,
            start_time,
        }
    }

    #[inline]
    pub fn request_id(&self) -> RequestId {
        self.request_id
    }

    #[inline]
    pub fn start_position(&self) -> SpacePosition {
        self.start_position
    }

    #[inline]
    pub fn start_time(&self) -> TimePoint<TimeType> {
        self.start_time
    }
}
impl<TimeType> Display for Assignment<TimeType>
where
    TimeType: PrimInt + Signed + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment(request_id: {}, start_position: {}, start_time: {})",
            self.request_id, self.start_position, self.start_time
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProblemEntry<TimeType = i64>
where
    TimeType: PrimInt + Signed,
{
    Unassigned(RequestId),
    PreAssigned(Assignment<TimeType>),
}

impl<TimeType> Display for ProblemEntry<TimeType>
where
    TimeType: PrimInt + Signed + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProblemEntry::Unassigned(request_id) => {
                write!(f, "Unassigned(request_id: {})", request_id)
            }
            ProblemEntry::PreAssigned(assignment) => write!(f, "PreAssigned({})", assignment),
        }
    }
}

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
    #[inline]
    pub fn new(request_id: RequestId) -> Self {
        MissingRequestError(request_id)
    }

    #[inline]
    pub fn request_id(&self) -> RequestId {
        self.0
    }
}

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
    #[inline]
    pub fn new(request_id: RequestId, end_pos: SpacePosition, quay_length: SpaceLength) -> Self {
        Self {
            request_id,
            end_pos,
            quay_length,
        }
    }

    #[inline]
    pub fn request_id(&self) -> RequestId {
        self.request_id
    }

    #[inline]
    pub fn end_pos(&self) -> SpacePosition {
        self.end_pos
    }

    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RequestRect<TimeType: PrimInt + Signed> {
    id: RequestId,
    time_interval: TimeInterval<TimeType>,
    space_interval: SpaceInterval,
}

impl<TimeType: PrimInt + Signed> RequestRect<TimeType> {
    #[inline]
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

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn time_interval(&self) -> &TimeInterval<TimeType> {
        &self.time_interval
    }

    #[inline]
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
    #[inline]
    fn new(a: RequestRect<TimeType>, b: RequestRect<TimeType>) -> Self {
        Self { a, b }
    }

    #[inline]
    fn a(&self) -> &RequestRect<TimeType> {
        &self.a
    }

    #[inline]
    fn b(&self) -> &RequestRect<TimeType> {
        &self.b
    }
}

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
    #[inline]
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
    #[inline]
    pub fn new(request_id: RequestId, assigned: SpaceInterval, feasible: SpaceInterval) -> Self {
        Self {
            request_id,
            assigned,
            feasible,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProblemError<TimeType: PrimInt + Signed> {
    MissingRequest(MissingRequestError),
    RequestOutOfBounds(RequestOutOfBoundsError),
    RequestOverlap(RequestOverlapError<TimeType>),
    AssignmentViolatesTimeWindow(AssignmentViolatesTimeWindow<TimeType>),
    AssignmentViolatesSpaceWindow(AssignmentViolatesSpaceWindow),
}

impl<TimeType: PrimInt + Signed> From<MissingRequestError> for ProblemError<TimeType> {
    #[inline]
    fn from(err: MissingRequestError) -> Self {
        ProblemError::MissingRequest(err)
    }
}

impl<TimeType: PrimInt + Signed> From<RequestOutOfBoundsError> for ProblemError<TimeType> {
    #[inline]
    fn from(err: RequestOutOfBoundsError) -> Self {
        ProblemError::RequestOutOfBounds(err)
    }
}

impl<TimeType: PrimInt + Signed> From<RequestOverlapError<TimeType>> for ProblemError<TimeType> {
    #[inline]
    fn from(err: RequestOverlapError<TimeType>) -> Self {
        ProblemError::RequestOverlap(err)
    }
}

impl<TimeType: PrimInt + Signed> From<AssignmentViolatesTimeWindow<TimeType>>
    for ProblemError<TimeType>
{
    #[inline]
    fn from(err: AssignmentViolatesTimeWindow<TimeType>) -> Self {
        ProblemError::AssignmentViolatesTimeWindow(err)
    }
}

impl<TimeType: PrimInt + Signed> From<AssignmentViolatesSpaceWindow> for ProblemError<TimeType> {
    #[inline]
    fn from(err: AssignmentViolatesSpaceWindow) -> Self {
        ProblemError::AssignmentViolatesSpaceWindow(err)
    }
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum EventKind {
    Start,
    End,
}

impl Display for EventKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EventKind::Start => write!(f, "Start"),
            EventKind::End => write!(f, "End"),
        }
    }
}

impl EventKind {
    #[inline]
    const fn key(self) -> u8 {
        match self {
            EventKind::End => 0,
            EventKind::Start => 1,
        }
    }
}

#[derive(Clone, Copy)]
struct Event<U: PrimInt + Signed> {
    time: TimePoint<U>,
    kind: EventKind,
    rect_index: usize,
}

impl<U: PrimInt + Signed> Event<U> {
    #[inline]
    fn new(time: TimePoint<U>, kind: EventKind, rect_index: usize) -> Self {
        Self {
            time,
            kind,
            rect_index,
        }
    }
}

impl<U: PrimInt + Signed + Display> Display for Event<U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Event(time: {}, kind: {}, rect_index: {})",
            self.time, self.kind, self.rect_index
        )
    }
}

#[inline]
fn check_space_overlaps<T: PrimInt + Signed>(
    rects: &[RequestRect<T>],
) -> Result<(), RequestOverlapError<T>> {
    if rects.is_empty() {
        return Ok(());
    }
    let mut events: Vec<Event<T>> = Vec::with_capacity(rects.len() * 2);
    for (i, r) in rects.iter().enumerate() {
        events.push(Event::new(r.time_interval().start(), EventKind::Start, i));
        events.push(Event::new(r.time_interval().end(), EventKind::End, i));
    }
    events.sort_by_key(|e| (e.time, e.kind.key()));
    let mut active: BTreeSet<(SpacePosition, usize)> = BTreeSet::new();
    for e in events {
        let rect = rects[e.rect_index];
        match e.kind {
            EventKind::Start => {
                let key = (rect.space_interval().start(), e.rect_index);
                if let Some(&(_, pred_idx)) = active.range(..key).next_back() {
                    let pred = rects[pred_idx];
                    if pred.space_interval().intersects(rect.space_interval()) {
                        return Err(RequestOverlapError::new(pred, rect));
                    }
                }
                if let Some(&(_, succ_idx)) = active.range(key..).next() {
                    let succ = rects[succ_idx];
                    if succ.space_interval().intersects(rect.space_interval()) {
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
    pub fn new(
        requests: HashSet<Request<TimeType, CostType>>,
        entries: HashSet<ProblemEntry<TimeType>>,
        quay_length: SpaceLength,
    ) -> Result<Self, ProblemError<TimeType>> {
        let request_map: HashMap<RequestId, &Request<TimeType, CostType>> = requests
            .iter()
            .map(|request| (request.id(), request))
            .collect();

        for entry in &entries {
            if let ProblemEntry::Unassigned(id) = *entry
                && !request_map.contains_key(&id)
            {
                return Err(ProblemError::MissingRequest(MissingRequestError::new(id)));
            }
        }

        let quay_end_position: SpacePosition = SpacePosition::new(quay_length.value());
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

                let start_time = assignment.start_time();
                let end_time = start_time + request.processing_duration();
                let assigned_time_interval = TimeInterval::new(start_time, end_time);
                let feasible_time = request.feasible_time_window();
                if !(start_time >= feasible_time.start() && end_time <= feasible_time.end()) {
                    return Err(ProblemError::AssignmentViolatesTimeWindow(
                        AssignmentViolatesTimeWindow::new(
                            request_id,
                            assigned_time_interval,
                            feasible_time,
                        ),
                    ));
                }

                let start_position = assignment.start_position();
                let end_position = start_position + request.length();
                if end_position > quay_end_position {
                    return Err(ProblemError::RequestOutOfBounds(
                        RequestOutOfBoundsError::new(request_id, end_position, quay_length),
                    ));
                }
                let assigned_space_interval = SpaceInterval::new(start_position, end_position);
                let feasible_space = request.feasible_space_window();
                if !(start_position >= feasible_space.start()
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

        if !pre_assigned_rects.is_empty() {
            check_space_overlaps(&pre_assigned_rects).map_err(ProblemError::RequestOverlap)?;
        }

        Ok(Problem {
            requests,
            entries,
            quay_length,
        })
    }

    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    #[inline]
    pub fn requests(&self) -> &HashSet<Request<TimeType, CostType>> {
        &self.requests
    }

    #[inline]
    pub fn entries(&self) -> &HashSet<ProblemEntry<TimeType>> {
        &self.entries
    }

    #[inline]
    pub fn request_len(&self) -> usize {
        self.requests.len()
    }
}

pub type BerthAllocationProblem = Problem<i64, i64>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Decision<TimeType = i64>
where
    TimeType: PrimInt + Signed,
{
    Assign(Assignment<TimeType>),
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
    #[inline]
    pub fn request_id(&self) -> RequestId {
        match *self {
            Decision::Assign(assignment) => assignment.request_id(),
            Decision::Drop(request_id) => request_id,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PreassignedChangedError<TimeType: PrimInt + Signed> {
    request_id: RequestId,
    expected: (TimePoint<TimeType>, SpacePosition),
    actual: (TimePoint<TimeType>, SpacePosition),
}

impl<TimeType: PrimInt + Signed> PreassignedChangedError<TimeType> {
    #[inline]
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

    #[inline]
    pub fn request_id(&self) -> RequestId {
        self.request_id
    }

    #[inline]
    pub fn expected(&self) -> &(TimePoint<TimeType>, SpacePosition) {
        &self.expected
    }

    #[inline]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolutionError<TimeType: PrimInt + Signed> {
    UnknownRequest(RequestId),
    DuplicateDecision(RequestId),
    MissingDecision(RequestId),
    PreassignmentChanged(PreassignedChangedError<TimeType>),
    PreassignedDropped(RequestId),
    DroppedNotDroppable(RequestId),
    NegativeWaitingTime(RequestId),
    AssignmentViolatesTimeWindow(AssignmentViolatesTimeWindow<TimeType>),
    AssignmentViolatesSpaceWindow(AssignmentViolatesSpaceWindow),
    RequestOutOfBounds(RequestOutOfBoundsError),
    RequestOverlap(RequestOverlapError<TimeType>),
}

impl<TimeType: PrimInt + Signed> From<PreassignedChangedError<TimeType>>
    for SolutionError<TimeType>
{
    #[inline]
    fn from(err: PreassignedChangedError<TimeType>) -> Self {
        SolutionError::PreassignmentChanged(err)
    }
}

impl<TimeType: PrimInt + Signed> From<AssignmentViolatesTimeWindow<TimeType>>
    for SolutionError<TimeType>
{
    #[inline]
    fn from(err: AssignmentViolatesTimeWindow<TimeType>) -> Self {
        SolutionError::AssignmentViolatesTimeWindow(err)
    }
}

impl<TimeType: PrimInt + Signed> From<AssignmentViolatesSpaceWindow> for SolutionError<TimeType> {
    #[inline]
    fn from(err: AssignmentViolatesSpaceWindow) -> Self {
        SolutionError::AssignmentViolatesSpaceWindow(err)
    }
}

impl<TimeType: PrimInt + Signed> From<RequestOutOfBoundsError> for SolutionError<TimeType> {
    #[inline]
    fn from(err: RequestOutOfBoundsError) -> Self {
        SolutionError::RequestOutOfBounds(err)
    }
}

impl<TimeType: PrimInt + Signed> From<RequestOverlapError<TimeType>> for SolutionError<TimeType> {
    #[inline]
    fn from(err: RequestOverlapError<TimeType>) -> Self {
        SolutionError::RequestOverlap(err)
    }
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
    #[inline]
    pub fn total_cost(&self) -> Cost<CostType> {
        self.total_cost
    }

    #[inline]
    pub fn total_waiting_time(&self) -> TimeDelta<TimeType> {
        self.total_waiting_time
    }

    #[inline]
    pub fn total_target_position_deviation(&self) -> SpaceLength {
        self.total_target_position_deviation
    }

    #[inline]
    pub fn total_dropped_requests(&self) -> usize {
        self.total_dropped_requests
    }
}

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
    pub fn new(
        problem: &Problem<TimeType, CostType>,
        decisions: impl IntoIterator<Item = Decision<TimeType>>,
    ) -> Result<Self, SolutionError<TimeType>> {
        let request_map: HashMap<RequestId, &Request<TimeType, CostType>> = problem
            .requests()
            .iter()
            .map(|req| (req.id(), req))
            .collect();

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
                        && (exp.start_position() != a.start_position()
                            || exp.start_time() != a.start_time())
                    {
                        return Err(SolutionError::PreassignmentChanged(
                            PreassignedChangedError::new(
                                request_id,
                                (exp.start_time(), exp.start_position()),
                                (a.start_time(), a.start_position()),
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

        for &id in &unassigned_set {
            if !seen_ids.contains(&id) {
                return Err(SolutionError::MissingDecision(id));
            }
        }

        for (&id, &assign) in &preassigned_map {
            decisions_map.entry(id).or_insert(Decision::Assign(assign));
        }

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
            let start_time = assignment.start_time();
            let end_time = start_time + request.processing_duration();
            let assigned_time = TimeInterval::new(start_time, end_time);
            let feasible_time = request.feasible_time_window();
            if !(start_time >= feasible_time.start() && end_time <= feasible_time.end()) {
                return Err(SolutionError::AssignmentViolatesTimeWindow(
                    AssignmentViolatesTimeWindow::new(request_id, assigned_time, feasible_time),
                ));
            }

            let start_position = assignment.start_position();
            let end_position = start_position + request.length();
            if end_position > quay_end {
                return Err(SolutionError::RequestOutOfBounds(
                    RequestOutOfBoundsError::new(request_id, end_position, problem.quay_length()),
                ));
            }
            let assigned_space = SpaceInterval::new(start_position, end_position);
            let feasible_space = request.feasible_space_window();
            if !(start_position >= feasible_space.start() && end_position <= feasible_space.end()) {
                return Err(SolutionError::AssignmentViolatesSpaceWindow(
                    AssignmentViolatesSpaceWindow::new(request_id, assigned_space, feasible_space),
                ));
            }

            let waiting_time = start_time - request.arrival_time();
            if waiting_time.value() < TimeType::zero() {
                return Err(SolutionError::NegativeWaitingTime(request_id));
            }
            let position_deviation = start_position - request.target_position();

            total_cost = total_cost
                + request.waiting_cost(waiting_time)
                + request.target_position_deviation_cost(position_deviation);
            total_waiting_time += waiting_time;
            total_position_deviation += position_deviation;
            assigned_rects.push(RequestRect::new(request_id, assigned_time, assigned_space));
        }

        let mut dropped_count = 0usize;
        for (&request_id, decision) in &decisions_map {
            if let Decision::Drop(_) = decision {
                dropped_count += 1;
                if let Some(penalty) = request_map[&request_id].drop_penalty() {
                    total_cost += penalty;
                }
            }
        }

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

    #[inline]
    pub fn stats(&self) -> &SolutionStats<TimeType, CostType> {
        &self.stats
    }

    #[inline]
    pub fn decisions(&self) -> &HashMap<RequestId, Decision<TimeType>> {
        &self.decisions
    }

    #[inline]
    pub fn assigned(&self) -> impl Iterator<Item = (&RequestId, &Assignment<TimeType>)> {
        self.decisions
            .iter()
            .filter_map(|(id, decision)| match decision {
                Decision::Assign(assignment) => Some((id, assignment)),
                _ => None,
            })
    }

    #[inline]
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
            start_position: SpacePosition(100), \
            start_time: TimePoint(1622547800))"
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
                assert_eq!(a.start_position(), SpacePosition::new(100));
                assert_eq!(a.start_time(), TimePoint::new(5));
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
