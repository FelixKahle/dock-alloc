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

use crate::id::{FixedRequestId, RequestId};
use dock_alloc_core::{
    SolverVariable,
    space::{SpaceInterval, SpaceLength},
    time::{TimeInterval, TimePoint},
};
use std::fmt::Display;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpaceWindowTooShortError {
    id: RequestId,
    length: SpaceLength,
    window: SpaceInterval,
}

impl SpaceWindowTooShortError {
    #[inline]
    pub fn new(id: RequestId, length: SpaceLength, window: SpaceInterval) -> Self {
        Self { id, length, window }
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
    pub fn space_window(&self) -> SpaceInterval {
        self.window
    }
}

impl Display for SpaceWindowTooShortError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Request {} has length {} not fitting space window {}",
            self.id, self.length, self.window
        )
    }
}

impl std::error::Error for SpaceWindowTooShortError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentBeforeArrivalTimeError<T: SolverVariable> {
    id: RequestId,
    arrival_time: TimePoint<T>,
    assigned_start_time: TimePoint<T>,
}

impl<T: SolverVariable> AssignmentBeforeArrivalTimeError<T> {
    #[inline]
    pub fn new(
        id: RequestId,
        arrival_time: TimePoint<T>,
        assigned_start_time: TimePoint<T>,
    ) -> Self {
        Self {
            id,
            arrival_time,
            assigned_start_time,
        }
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn arrival_time(&self) -> TimePoint<T> {
        self.arrival_time
    }

    #[inline]
    pub fn assigned_start_time(&self) -> TimePoint<T> {
        self.assigned_start_time
    }
}

impl<T: SolverVariable + Display> std::fmt::Display for AssignmentBeforeArrivalTimeError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment for request {} starts before its arrival time: {} < {}",
            self.id, self.assigned_start_time, self.arrival_time
        )
    }
}

impl<T: SolverVariable + std::fmt::Debug + Display> std::error::Error
    for AssignmentBeforeArrivalTimeError<T>
{
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentOutsideSpaceWindowError {
    id: RequestId,
    space_window: SpaceInterval,
    assigned_interval: SpaceInterval,
}

impl AssignmentOutsideSpaceWindowError {
    #[inline]
    pub fn new(
        id: RequestId,
        space_window: SpaceInterval,
        assigned_interval: SpaceInterval,
    ) -> Self {
        Self {
            id,
            space_window,
            assigned_interval,
        }
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn space_window(&self) -> SpaceInterval {
        self.space_window
    }

    #[inline]
    pub fn assigned_interval(&self) -> SpaceInterval {
        self.assigned_interval
    }
}
impl Display for AssignmentOutsideSpaceWindowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment for request {} is outside its space window: {} not in {}",
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
    #[inline]
    pub fn new(id: RequestId, quay_length: SpaceLength, assigned_interval: SpaceInterval) -> Self {
        Self {
            id,
            quay_length,
            assigned_interval,
        }
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    #[inline]
    pub fn assigned_interval(&self) -> SpaceInterval {
        self.assigned_interval
    }
}

impl Display for AssignmentExceedsQuayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment for request {} exceeds quay length {}: {}",
            self.id, self.quay_length, self.assigned_interval
        )
    }
}

impl std::error::Error for AssignmentExceedsQuayError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentOverlapError<T: SolverVariable> {
    a: RequestId,
    b: RequestId,
    time_a: TimeInterval<T>,
    time_b: TimeInterval<T>,
    space_a: SpaceInterval,
    space_b: SpaceInterval,
}

impl<T: SolverVariable> AssignmentOverlapError<T> {
    #[inline]
    pub fn new(
        a: RequestId,
        b: RequestId,
        time_a: TimeInterval<T>,
        time_b: TimeInterval<T>,
        space_a: SpaceInterval,
        space_b: SpaceInterval,
    ) -> Self {
        Self {
            a,
            b,
            time_a,
            time_b,
            space_a,
            space_b,
        }
    }

    #[inline]
    pub fn request_a(&self) -> RequestId {
        self.a
    }

    #[inline]
    pub fn request_b(&self) -> RequestId {
        self.b
    }

    #[inline]
    pub fn time_a(&self) -> TimeInterval<T> {
        self.time_a
    }

    #[inline]
    pub fn time_b(&self) -> TimeInterval<T> {
        self.time_b
    }

    #[inline]
    pub fn space_a(&self) -> SpaceInterval {
        self.space_a
    }

    #[inline]
    pub fn space_b(&self) -> SpaceInterval {
        self.space_b
    }
}

impl<T: SolverVariable + Display> Display for AssignmentOverlapError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignments for requests {} and {} overlap: time_a={}, time_b={}, space_a={}, space_b={}",
            self.a, self.b, self.time_a, self.time_b, self.space_a, self.space_b
        )
    }
}

impl<T: SolverVariable + std::fmt::Debug + Display> std::error::Error
    for AssignmentOverlapError<T>
{
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PreassignedOverlapError {
    a: FixedRequestId,
    b: FixedRequestId,
}

impl PreassignedOverlapError {
    #[inline]
    pub fn new(a: FixedRequestId, b: FixedRequestId) -> Self {
        Self { a, b }
    }

    #[inline]
    pub fn request_a(&self) -> FixedRequestId {
        self.a
    }

    #[inline]
    pub fn request_b(&self) -> FixedRequestId {
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
pub enum ProblemBuildError<T: SolverVariable> {
    DuplicateRequestId(RequestId),
    AssignmentBeforeArrivalTime(AssignmentBeforeArrivalTimeError<T>),
    AssignmentOutsideSpaceWindow(AssignmentOutsideSpaceWindowError),
    AssignmentExceedsQuay(AssignmentExceedsQuayError),
    PreassignedOverlap(PreassignedOverlapError),
}

impl<T: SolverVariable + Display> Display for ProblemBuildError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProblemBuildError::DuplicateRequestId(id) => write!(f, "Duplicate request ID: {}", id),
            ProblemBuildError::AssignmentBeforeArrivalTime(e) => write!(f, "{e}"),
            ProblemBuildError::AssignmentOutsideSpaceWindow(e) => write!(f, "{e}"),
            ProblemBuildError::AssignmentExceedsQuay(e) => write!(f, "{e}"),
            ProblemBuildError::PreassignedOverlap(e) => write!(f, "{e}"),
        }
    }
}

impl<T: SolverVariable + std::fmt::Debug + Display> std::error::Error for ProblemBuildError<T> {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolutionValidationError<T = i64>
where
    T: SolverVariable,
{
    AssignmentBeforeArrivalTime(AssignmentBeforeArrivalTimeError<T>),
    Overlap(AssignmentOverlapError<T>),
}

impl<T> std::fmt::Display for SolutionValidationError<T>
where
    T: SolverVariable + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SolutionValidationError::AssignmentBeforeArrivalTime(e) => write!(f, "{e}"),
            SolutionValidationError::Overlap(e) => write!(f, "{e}"),
        }
    }
}

impl<T> std::error::Error for SolutionValidationError<T> where
    T: SolverVariable + std::fmt::Debug + std::fmt::Display
{
}
