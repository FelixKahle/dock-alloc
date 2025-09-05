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

use std::marker::PhantomData;

use crate::{
    domain::{SpaceTimeRectangle, Version},
    ledger::{
        AssignmentLedger, AssignmentLedgerOverlay, BrandedMoveableAssignment,
        BrandedMoveableRequest, FixedHandle, MovableHandle, StageError,
    },
    occupancy::{BerthOccupancy, BerthOccupancyOverlay},
    quay::QuayRead,
};
use dock_alloc_core::domain::{SpaceInterval, TimeInterval};
use dock_alloc_model::{Assignment, FixedAssignment, Problem};
use num_traits::{PrimInt, Signed};

pub struct ProposeCtx<'brand, 'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    ledger: &'p AssignmentLedger<'brand, 'p, T, C>,
    berth: &'p BerthOccupancy<T, Q>,
    problem: &'p Problem<'p, T, C>,
    stamp: Version,
}

impl<'brand, 'p, T, C, Q> ProposeCtx<'brand, 'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    pub fn new(
        ledger: &'p AssignmentLedger<'brand, 'p, T, C>,
        berth: &'p BerthOccupancy<T, Q>,
        problem: &'p Problem<'p, T, C>,
        stamp: Version,
    ) -> Self {
        Self {
            ledger,
            berth,
            problem,
            stamp,
        }
    }

    pub fn ledger(&self) -> &'p AssignmentLedger<'brand, 'p, T, C> {
        self.ledger
    }
    pub fn berth(&self) -> &'p BerthOccupancy<T, Q> {
        self.berth
    }
    pub fn problem(&self) -> &'p Problem<'p, T, C> {
        self.problem
    }
    pub fn stamp(&self) -> Version {
        self.stamp
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub struct FreeSlot<'brand, T: PrimInt + Signed> {
    space: SpaceInterval,
    time: TimeInterval<T>,
    _brand: PhantomData<&'brand ()>,
}

impl<'brand, T: PrimInt + Signed> FreeSlot<'brand, T> {
    fn new(space: SpaceInterval, time: TimeInterval<T>) -> Self {
        Self {
            space,
            time,
            _brand: PhantomData,
        }
    }

    pub fn space(&self) -> SpaceInterval {
        self.space
    }

    pub fn time(&self) -> TimeInterval<T> {
        self.time
    }
}

impl<'brand, 'p, T, C> From<&BrandedMoveableAssignment<'brand, 'p, T, C>> for FreeSlot<'brand, T>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(assignment: &BrandedMoveableAssignment<'brand, 'p, T, C>) -> Self {
        let assignment = assignment.assignment();

        // Time
        let start_time = assignment.start_time();
        let processing_duration = assignment.request().processing_duration();
        let end_time = start_time + processing_duration;

        // Space
        let space = assignment.start_position();
        let length = assignment.request().length();
        let end_space = space + length;

        FreeSlot::new(
            SpaceInterval::new(space, end_space),
            TimeInterval::new(start_time, end_time),
        )
    }
}

impl<'brand, 'p, T, C> From<&BrandedMoveableAssignment<'brand, 'p, T, C>> for SpaceTimeRectangle<T>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(m: &BrandedMoveableAssignment<'brand, 'p, T, C>) -> Self {
        let assignment = m.assignment();

        // Time
        let start_time = assignment.start_time();
        let processing_duration = assignment.request().processing_duration();
        let end_time = start_time + processing_duration;

        // Space
        let space = assignment.start_position();
        let length = assignment.request().length();
        let end_space = space + length;

        SpaceTimeRectangle::new(
            SpaceInterval::new(space, end_space),
            TimeInterval::new(start_time, end_time),
        )
    }
}

impl<'brand, 'p, T, C> From<&Assignment<'p, T, C>> for SpaceTimeRectangle<T>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(assignment: &Assignment<'p, T, C>) -> Self {
        // Time
        let start_time = assignment.start_time();
        let processing_duration = assignment.request().processing_duration();
        let end_time = start_time + processing_duration;

        // Space
        let space = assignment.start_position();
        let length = assignment.request().length();
        let end_space = space + length;

        SpaceTimeRectangle::new(
            SpaceInterval::new(space, end_space),
            TimeInterval::new(start_time, end_time),
        )
    }
}

pub struct UnassignOperation<'brand, 'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    moveable: &'brand BrandedMoveableAssignment<'brand, 'p, T, C>,
    _brand: PhantomData<&'brand ()>,
}

impl<'brand, 'p, T, C> UnassignOperation<'brand, 'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn new(assignment: &'brand BrandedMoveableAssignment<'brand, 'p, T, C>) -> Self {
        Self {
            moveable: assignment,
            _brand: PhantomData,
        }
    }

    pub fn moveable(&self) -> &'brand BrandedMoveableAssignment<'brand, 'p, T, C> {
        self.moveable
    }
}

pub struct AssignOperation<'brand, 'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    assignment: BrandedMoveableAssignment<'brand, 'p, T, C>,
    _brand: PhantomData<&'brand ()>,
}

impl<'brand, 'p, T, C> AssignOperation<'brand, 'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[allow(dead_code)]
    fn new(assignment: BrandedMoveableAssignment<'brand, 'p, T, C>) -> Self {
        Self {
            assignment,
            _brand: PhantomData,
        }
    }

    pub fn assignment(&self) -> &BrandedMoveableAssignment<'brand, 'p, T, C> {
        &self.assignment
    }
}

pub enum Operation<'brand, 'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    Unassign(UnassignOperation<'brand, 'p, T, C>),
    Assign(AssignOperation<'brand, 'p, T, C>),
}

impl<'brand, 'p, T, C> From<UnassignOperation<'brand, 'p, T, C>> for Operation<'brand, 'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(op: UnassignOperation<'brand, 'p, T, C>) -> Self {
        Operation::Unassign(op)
    }
}

impl<'brand, 'p, T, C> From<AssignOperation<'brand, 'p, T, C>> for Operation<'brand, 'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(op: AssignOperation<'brand, 'p, T, C>) -> Self {
        Operation::Assign(op)
    }
}

pub struct PlanBuilder<'brand, 'p, 'ctx, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    ctx: &'ctx ProposeCtx<'brand, 'p, T, C, Q>,
    assignment_overlay: AssignmentLedgerOverlay<'brand, 'p, 'ctx, T, C>,
    berth_overlay: BerthOccupancyOverlay<'brand, 'p, T, Q>,
    operations: Vec<Operation<'brand, 'p, T, C>>,
}

pub struct Explorer<'brand, 'p, 'ctx, 'pb, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    builder: &'pb PlanBuilder<'brand, 'p, 'ctx, T, C, Q>,
}

impl<'brand, 'p, 'ctx, 'pb, T, C, Q> Explorer<'brand, 'p, 'ctx, 'pb, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    #[allow(dead_code)]
    fn new(builder: &'pb PlanBuilder<'brand, 'p, 'ctx, T, C, Q>) -> Self {
        Self { builder }
    }

    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = FixedHandle<'brand>> + '_ {
        self.builder.assignment_overlay.iter_fixed_handles()
    }

    #[inline]
    pub fn iter_fixed_assignments(
        &self,
    ) -> impl Iterator<Item = &'_ FixedAssignment<'_, T, C>> + '_ {
        self.builder.assignment_overlay.iter_fixed_assignments()
    }

    #[inline]
    pub fn iter_movable_handles(&self) -> impl Iterator<Item = MovableHandle<'brand>> + '_ {
        self.builder.assignment_overlay.iter_movable_handles()
    }

    #[inline]
    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = &BrandedMoveableAssignment<'brand, 'p, T, C>> + '_ {
        self.builder.assignment_overlay.iter_movable_assignments()
    }

    #[inline]
    pub fn iter_unassigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMoveableRequest<'brand, 'p, T, C>> + '_ {
        self.builder.assignment_overlay.iter_unassigned_requests()
    }

    #[inline]
    pub fn iter_assigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMoveableRequest<'brand, 'p, T, C>> + '_ {
        self.builder.assignment_overlay.iter_assigned_requests()
    }

    #[inline]
    pub fn iter_assignments(&self) -> impl Iterator<Item = &'_ Assignment<'_, T, C>> + '_ {
        self.builder.assignment_overlay.iter_assignments()
    }

    pub fn iter_slots_for_request(
        &self,
        request: &BrandedMoveableRequest<'brand, 'p, T, C>,
    ) -> impl Iterator<Item = FreeSlot<'brand, T>> + '_ {
        let time_search_window = request.feasible_time_window();
        let space_search_window = request.feasible_space_window();
        let processing_duration = request.processing_duration();
        let length = request.length();

        self.builder
            .berth_overlay
            .iter_free(
                time_search_window,
                processing_duration,
                length,
                space_search_window,
            )
            .map(move |slot| {
                let time_interval =
                    TimeInterval::new(slot.start_time(), slot.start_time() + processing_duration);
                FreeSlot::new(slot.space(), time_interval)
            })
    }

    pub fn iter_slots_for_request_within(
        &self,
        request: &BrandedMoveableRequest<'brand, 'p, T, C>,
        time_search_window: TimeInterval<T>,
        space_search_window: SpaceInterval,
    ) -> impl Iterator<Item = FreeSlot<'brand, T>> + '_ {
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
                    .iter_free(twin, proc, len, swin)
                    .map(move |slot| {
                        let time = TimeInterval::new(slot.start_time(), slot.start_time() + proc);
                        FreeSlot::new(slot.space(), time)
                    })
            })
            .into_iter()
            .flatten()
    }
}

impl<'brand, 'p, 'ctx, T, C, Q> PlanBuilder<'brand, 'p, 'ctx, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    #[allow(dead_code)]
    fn new(ctx: &'ctx ProposeCtx<'brand, 'p, T, C, Q>) -> Self {
        let assignment_overlay = AssignmentLedgerOverlay::new(ctx.ledger());
        let berth_overlay = BerthOccupancyOverlay::new(ctx.berth());
        Self {
            ctx,
            assignment_overlay,
            berth_overlay,
            operations: Vec::new(),
        }
    }

    pub fn problem(&self) -> &'p Problem<'p, T, C> {
        self.ctx.problem()
    }

    pub fn with_explorer<'pb, F, R>(&'pb self, f: F) -> R
    where
        F: FnOnce(&Explorer<'brand, 'p, 'ctx, 'pb, T, C, Q>) -> R,
    {
        let explorer = Explorer { builder: self };
        f(&explorer)
    }

    fn add_operation<O>(&mut self, op: O)
    where
        O: Into<Operation<'brand, 'p, T, C>>,
    {
        self.operations.push(op.into());
    }

    pub fn propose_unassign(
        &mut self,
        assignment: &'brand BrandedMoveableAssignment<'brand, 'p, T, C>,
    ) -> Result<FreeSlot<'brand, T>, StageError> {
        let free: FreeSlot<'brand, T> = assignment.into();
        let rect: SpaceTimeRectangle<T> = assignment.into();
        self.assignment_overlay.uncommit_assignment(assignment)?;
        self.berth_overlay.free(&rect);
        self.add_operation(UnassignOperation::new(assignment));
        Ok(free)
    }

    pub fn propose_assign(
        &mut self,
        req: &BrandedMoveableRequest<'brand, 'p, T, C>,
        slot: FreeSlot<'brand, T>,
    ) -> Result<BrandedMoveableAssignment<'brand, 'p, T, C>, StageError> {
        let a = Assignment::borrowed(req.request(), slot.space().start(), slot.time().start());
        let ma = self.assignment_overlay.commit_assignment(&a)?;
        let rect: SpaceTimeRectangle<T> = (&a).into();
        self.berth_overlay.occupy(&rect);
        self.operations
            .push(AssignOperation::new(ma.clone()).into());
        Ok(ma)
    }
}
