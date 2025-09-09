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

use crate::{
    domain::{SpaceTimeRectangle, Version},
    ledger::{
        AssignmentLedger, AssignmentLedgerOverlay, BrandedFixedRequestId, BrandedMovableAssignment,
        BrandedMovableRequest, BrandedMovableRequestId, StageError,
    },
    occupancy::{BerthOccupancy, BerthOccupancyOverlay},
    quay::{QuayRead, QuaySpaceIntervalOutOfBoundsError, QuayWrite},
};
use dock_alloc_core::domain::{SpaceInterval, TimeInterval};
use dock_alloc_model::{
    AnyAssignmentRef, AssignmentRef, Fixed, Kind, Movable, Problem, SolutionRef,
};
use num_traits::{PrimInt, Signed};
use std::{fmt::Display, marker::PhantomData};

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub struct FreeSlot<'bo, T: PrimInt + Signed> {
    space: SpaceInterval,
    time: TimeInterval<T>,
    _brand: PhantomData<&'bo ()>,
}

impl<'bo, T: PrimInt + Signed> FreeSlot<'bo, T> {
    fn new(space: SpaceInterval, time: TimeInterval<T>) -> Self {
        Self {
            space,
            time,
            _brand: PhantomData,
        }
    }

    #[inline]
    pub fn space(&self) -> SpaceInterval {
        self.space
    }

    #[inline]
    pub fn time(&self) -> TimeInterval<T> {
        self.time
    }
}

pub struct ProposeCtx<'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    ledger: &'p AssignmentLedger<'p, T, C>,
    berth: &'p BerthOccupancy<T, Q>,
    problem: &'p Problem<T, C>,
    stamp: Version,
}

impl<'p, T, C, Q> ProposeCtx<'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    #[inline]
    pub fn new(
        ledger: &'p AssignmentLedger<'p, T, C>,
        berth: &'p BerthOccupancy<T, Q>,
        problem: &'p Problem<T, C>,
        stamp: Version,
    ) -> Self {
        Self {
            ledger,
            berth,
            problem,
            stamp,
        }
    }

    #[inline]
    pub fn ledger(&self) -> &'p AssignmentLedger<'p, T, C> {
        self.ledger
    }

    #[inline]
    pub fn berth(&self) -> &'p BerthOccupancy<T, Q> {
        self.berth
    }

    #[inline]
    pub fn problem(&self) -> &'p Problem<T, C> {
        self.problem
    }

    #[inline]
    pub fn stamp(&self) -> Version {
        self.stamp
    }

    #[inline]
    pub fn with_builder<F, R>(&self, f: F) -> R
    where
        F: for<'brand, 'bo, 'al> FnOnce(PlanBuilder<'brand, 'bo, 'p, 'al, T, C, Q>) -> R,
    {
        let alov = AssignmentLedgerOverlay::new(self.ledger());
        let bov = BerthOccupancyOverlay::new(self.berth());
        f(PlanBuilder::new(self.problem(), alov, bov))
    }
}

impl<'al, 'p, T, C> From<&BrandedMovableAssignment<'al, 'p, T, C>> for SpaceTimeRectangle<T>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(m: &BrandedMovableAssignment<'al, 'p, T, C>) -> Self {
        let a = m.assignment();

        // Time
        let start_time = a.start_time();
        let processing_duration = a.request().processing_duration();
        let end_time = start_time + processing_duration;

        // Space
        let space = a.start_position();
        let length = a.request().length();
        let end_space = space + length;

        SpaceTimeRectangle::new(
            SpaceInterval::new(space, end_space),
            TimeInterval::new(start_time, end_time),
        )
    }
}

impl<'p, K, T, C> From<AssignmentRef<'p, K, T, C>> for SpaceTimeRectangle<T>
where
    K: Kind,
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(a: AssignmentRef<'p, K, T, C>) -> Self {
        // Time
        let start_time = a.start_time();
        let processing_duration = a.request().processing_duration();
        let end_time = start_time + processing_duration;

        // Space
        let space = a.start_position();
        let length = a.request().length();
        let end_space = space + length;

        SpaceTimeRectangle::new(
            SpaceInterval::new(space, end_space),
            TimeInterval::new(start_time, end_time),
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnassignOperation<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    moveable: AssignmentRef<'p, Movable, T, C>,
}

impl<'p, T, C> UnassignOperation<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(assignment: AssignmentRef<'p, Movable, T, C>) -> Self {
        Self {
            moveable: assignment,
        }
    }

    #[inline]
    pub fn moveable(&self) -> &AssignmentRef<'p, Movable, T, C> {
        &self.moveable
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AssignOperation<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    assignment: AssignmentRef<'p, Movable, T, C>,
}

impl<'p, T, C> AssignOperation<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(assignment: AssignmentRef<'p, Movable, T, C>) -> Self {
        Self { assignment }
    }

    #[inline]
    pub fn assignment(&self) -> &AssignmentRef<'p, Movable, T, C> {
        &self.assignment
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Operation<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    Unassign(UnassignOperation<'p, T, C>),
    Assign(AssignOperation<'p, T, C>),
}

impl<'p, T, C> From<UnassignOperation<'p, T, C>> for Operation<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn from(op: UnassignOperation<'p, T, C>) -> Self {
        Operation::Unassign(op)
    }
}

impl<'brand, 'p, T, C> From<AssignOperation<'p, T, C>> for Operation<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn from(op: AssignOperation<'p, T, C>) -> Self {
        Operation::Assign(op)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan<'brand, 'bo, 'p, 'al, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    operations: Vec<Operation<'p, T, C>>,
    assignment_overlay: AssignmentLedgerOverlay<'brand, 'p, 'al, T, C>,
    berth_overlay: BerthOccupancyOverlay<'bo, 'p, T, Q>,
}

impl<'brand, 'bo, 'p, 'al, T, C, Q> Plan<'brand, 'bo, 'p, 'al, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + QuayWrite,
{
    #[inline]
    fn new(
        operations: Vec<Operation<'p, T, C>>,
        assignment_overlay: AssignmentLedgerOverlay<'brand, 'p, 'al, T, C>,
        berth_overlay: BerthOccupancyOverlay<'bo, 'p, T, Q>,
    ) -> Self {
        Self {
            operations,
            assignment_overlay,
            berth_overlay,
        }
    }

    #[inline]
    pub fn operations(&self) -> &[Operation<'p, T, C>] {
        &self.operations
    }

    #[inline]
    pub fn iter_operations(&self) -> impl DoubleEndedIterator<Item = &Operation<'p, T, C>> {
        self.operations.iter()
    }

    pub fn commit(
        self,
        ledger: &mut AssignmentLedger<'p, T, C>,
        berth: &mut BerthOccupancy<T, Q>,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        ledger.apply(self.assignment_overlay);
        berth.apply(self.berth_overlay)?;
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProposeError {
    Stage(StageError),
    QuaySpaceIntervalOutOfBounds(QuaySpaceIntervalOutOfBoundsError),
}

impl From<StageError> for ProposeError {
    #[inline]
    fn from(e: StageError) -> Self {
        ProposeError::Stage(e)
    }
}

impl From<QuaySpaceIntervalOutOfBoundsError> for ProposeError {
    #[inline]
    fn from(e: QuaySpaceIntervalOutOfBoundsError) -> Self {
        ProposeError::QuaySpaceIntervalOutOfBounds(e)
    }
}

impl Display for ProposeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProposeError::Stage(e) => write!(f, "{}", e),
            ProposeError::QuaySpaceIntervalOutOfBounds(e) => write!(f, "{}", e),
        }
    }
}

impl std::error::Error for ProposeError {}

pub struct PlanBuilder<'brand, 'bo, 'p, 'al, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    problem: &'p Problem<T, C>,
    assignment_overlay: AssignmentLedgerOverlay<'brand, 'p, 'al, T, C>,
    berth_overlay: BerthOccupancyOverlay<'bo, 'p, T, Q>,
    operations: Vec<Operation<'p, T, C>>,
}

pub struct Explorer<'brand, 'bo, 'p, 'al, 'pb, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    builder: &'pb PlanBuilder<'brand, 'bo, 'p, 'al, T, C, Q>,
}

impl<'brand, 'bo, 'p, 'al, 'pb, T, C, Q> Explorer<'brand, 'bo, 'p, 'al, 'pb, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    #[allow(dead_code)]
    #[inline]
    fn new(builder: &'pb PlanBuilder<'brand, 'bo, 'p, 'al, T, C, Q>) -> Self {
        Self { builder }
    }

    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = BrandedFixedRequestId<'brand>> + '_ {
        self.builder.assignment_overlay.iter_fixed_handles()
    }

    #[inline]
    pub fn iter_fixed_assignments(
        &self,
    ) -> impl Iterator<Item = AssignmentRef<'_, Fixed, T, C>> + '_ {
        self.builder.assignment_overlay.iter_fixed_assignments()
    }

    #[inline]
    pub fn iter_movable_handles(
        &self,
    ) -> impl Iterator<Item = BrandedMovableRequestId<'brand>> + '_ {
        self.builder.assignment_overlay.iter_movable_handles()
    }

    #[inline]
    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = BrandedMovableAssignment<'brand, 'p, T, C>> + '_
    where
        'al: 'p,
    {
        self.builder.assignment_overlay.iter_movable_assignments()
    }

    #[inline]
    pub fn iter_unassigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMovableRequest<'brand, 'p, T, C>> + '_ {
        self.builder.assignment_overlay.iter_unassigned_requests()
    }

    #[inline]
    pub fn iter_assigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMovableRequest<'brand, 'p, T, C>> + '_ {
        self.builder.assignment_overlay.iter_assigned_requests()
    }

    #[inline]
    pub fn iter_assignments(&self) -> impl Iterator<Item = AnyAssignmentRef<'_, T, C>> + '_ {
        self.builder.assignment_overlay.iter_assignments()
    }

    /// Slots are branded by the **berth** brand `'bo`.
    pub fn iter_slots_for_request(
        &self,
        request: &BrandedMovableRequest<'brand, 'p, T, C>,
    ) -> impl Iterator<Item = FreeSlot<'bo, T>> + '_ {
        let time_search_window = request.feasible_time_window();
        let space_search_window = request.feasible_space_window();
        let processing_duration = request.processing_duration();
        let length = request.length();

        self.builder
            .berth_overlay
            .iter_free_slots(
                time_search_window,
                processing_duration,
                length,
                space_search_window,
            )
            .map(move |slot| {
                let time_interval = TimeInterval::new(
                    slot.slot().start_time(),
                    slot.slot().start_time() + processing_duration,
                );
                FreeSlot::new(slot.slot().space(), time_interval)
            })
    }

    pub fn iter_slots_for_request_within(
        &self,
        request: &BrandedMovableRequest<'brand, 'p, T, C>,
        time_search_window: TimeInterval<T>,
        space_search_window: SpaceInterval,
    ) -> impl Iterator<Item = FreeSlot<'bo, T>> + '_ {
        let proc = request.processing_duration();
        let len = request.length();
        let t_opt = time_search_window.intersection(&request.feasible_time_window());
        let s_opt = space_search_window.intersection(&request.feasible_space_window());

        t_opt
            .and_then(|twin| s_opt.map(|swin| (twin, swin)))
            .filter(|(twin, swin)| twin.duration() >= proc && swin.measure() >= len)
            .map(move |(twin, swin)| {
                self.builder
                    .berth_overlay
                    .iter_free_slots(twin, proc, len, swin)
                    .map(move |slot| {
                        let time = TimeInterval::new(
                            slot.slot().start_time(),
                            slot.slot().start_time() + proc,
                        );
                        FreeSlot::new(slot.slot().space(), time)
                    })
            })
            .into_iter()
            .flatten()
    }
}

impl<'brand, 'bo, 'p, 'al, T, C, Q> PlanBuilder<'brand, 'bo, 'p, 'al, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead + QuayWrite,
{
    fn new(
        problem: &'p Problem<T, C>,
        assignment_overlay: AssignmentLedgerOverlay<'brand, 'p, 'al, T, C>,
        berth_overlay: BerthOccupancyOverlay<'bo, 'p, T, Q>,
    ) -> Self {
        Self {
            problem,
            assignment_overlay,
            berth_overlay,
            operations: Vec::new(),
        }
    }

    #[inline]
    pub fn problem(&self) -> &'p Problem<T, C> {
        self.problem
    }

    #[inline]
    pub fn with_explorer<'pb, F, R>(&'pb self, f: F) -> R
    where
        F: FnOnce(&Explorer<'brand, 'bo, 'p, 'al, 'pb, T, C, Q>) -> R,
    {
        let explorer = Explorer { builder: self };
        f(&explorer)
    }

    #[inline]
    fn add_operation<O>(&mut self, op: O)
    where
        O: Into<Operation<'p, T, C>>,
    {
        self.operations.push(op.into());
    }

    pub fn propose_unassign(
        &mut self,
        assignment: &'brand BrandedMovableAssignment<'brand, 'p, T, C>,
    ) -> Result<FreeSlot<'bo, T>, ProposeError> {
        let a = assignment.assignment();
        let proc = a.request().processing_duration();
        let time = TimeInterval::new(a.start_time(), a.start_time() + proc);
        let len = a.request().length();
        let space = SpaceInterval::new(a.start_position(), a.start_position() + len);
        let free: FreeSlot<'bo, T> = FreeSlot::new(space, time);
        let rect: SpaceTimeRectangle<T> = a.into();

        self.assignment_overlay.uncommit_assignment(assignment)?;
        self.berth_overlay.free(&rect)?;
        self.add_operation(UnassignOperation::new(assignment.assignment().clone()));

        Ok(free)
    }

    pub fn propose_assign(
        &mut self,
        req: &BrandedMovableRequest<'brand, 'p, T, C>,
        slot: FreeSlot<'bo, T>,
    ) -> Result<BrandedMovableAssignment<'brand, 'p, T, C>, ProposeError> {
        let a = AssignmentRef::new(req.request(), slot.space().start(), slot.time().start());
        let rect: SpaceTimeRectangle<T> = a.into();

        let ma = self.assignment_overlay.commit_assignment(
            req.request(),
            slot.time().start(),
            slot.space().start(),
        )?;
        self.berth_overlay.occupy(&rect)?;
        self.add_operation(AssignOperation::new(a));

        Ok(ma)
    }
}
