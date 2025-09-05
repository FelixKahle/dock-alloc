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
    ledger::{AssignmentLedger, AssignmentOverlay, MovableAssignment, StageError},
    occupancy::{BerthOccupancy, BerthOccupancyOverlay},
    quay::QuayRead,
};
use dock_alloc_core::domain::{SpaceInterval, TimeInterval};
use dock_alloc_model::{Assignment, Problem};
use num_traits::{PrimInt, Signed};

pub struct ProposeCtx<'base, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    ledger: &'base AssignmentLedger<'base, 'base, T, C>,
    berth: &'base BerthOccupancy<T, Q>,
    problem: &'base Problem<'base, T, C>,
    stamp: Version,
}

impl<'brand, T, C, Q> ProposeCtx<'brand, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    pub fn new(
        ledger: &'brand AssignmentLedger<'brand, 'brand, T, C>,
        berth: &'brand BerthOccupancy<T, Q>,
        problem: &'brand Problem<T, C>,
        stamp: Version,
    ) -> Self {
        Self {
            ledger,
            berth,
            problem,
            stamp,
        }
    }

    pub fn ledger(&self) -> &'brand AssignmentLedger<'brand, 'brand, T, C> {
        self.ledger
    }

    pub fn berth(&self) -> &'brand BerthOccupancy<T, Q> {
        self.berth
    }

    pub fn problem(&self) -> &'brand Problem<'_, T, C> {
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

impl<'brand, 'a, T, C> From<&MovableAssignment<'brand, 'a, T, C>> for FreeSlot<'brand, T>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(assignment: &MovableAssignment<'brand, 'a, T, C>) -> Self {
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

impl<'brand, 'a, T, C> From<&MovableAssignment<'brand, 'a, T, C>> for SpaceTimeRectangle<T>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(m: &MovableAssignment<'brand, 'a, T, C>) -> Self {
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

impl<'brand, 'a, T, C> From<&Assignment<'a, T, C>> for SpaceTimeRectangle<T>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(assignment: &Assignment<'a, T, C>) -> Self {
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

pub struct UnassignOperation<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    moveable: &'brand MovableAssignment<'brand, 'a, T, C>,
    _brand: PhantomData<&'brand ()>,
}

impl<'brand, 'a, T, C> UnassignOperation<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn new(assignment: &'brand MovableAssignment<'brand, 'a, T, C>) -> Self {
        Self {
            moveable: assignment,
            _brand: PhantomData,
        }
    }

    pub fn moveable(&self) -> &'brand MovableAssignment<'brand, 'a, T, C> {
        self.moveable
    }
}

pub struct AssignOperation<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    assignment: Assignment<'a, T, C>,
    _brand: PhantomData<&'brand ()>,
}

impl<'brand, 'a, T, C> AssignOperation<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn new(assignment: Assignment<'a, T, C>) -> Self {
        Self {
            assignment,
            _brand: PhantomData,
        }
    }

    pub fn assignment(&self) -> &Assignment<'a, T, C> {
        &self.assignment
    }
}

pub enum Operation<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    Unassign(UnassignOperation<'brand, 'a, T, C>),
    Assign(AssignOperation<'brand, 'a, T, C>),
}

impl<'brand, 'a, T, C> From<UnassignOperation<'brand, 'a, T, C>> for Operation<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(op: UnassignOperation<'brand, 'a, T, C>) -> Self {
        Operation::Unassign(op)
    }
}

impl<'brand, 'a, T, C> From<AssignOperation<'brand, 'a, T, C>> for Operation<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(op: AssignOperation<'brand, 'a, T, C>) -> Self {
        Operation::Assign(op)
    }
}

pub struct PlanBuilder<'brand, 'base, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    ctx: &'brand ProposeCtx<'base, T, C, Q>,
    assignment_overlay: AssignmentOverlay<'brand, 'base, 'base, T, C>,
    berth_overlay: BerthOccupancyOverlay<'brand, 'base, T, Q>,
    operations: Vec<Operation<'brand, 'base, T, C>>,
}

impl<'brand, 'base, T, C, Q> PlanBuilder<'brand, 'base, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    #[allow(dead_code)]
    fn new(ctx: &'brand ProposeCtx<'base, T, C, Q>) -> Self {
        let assignment_overlay = AssignmentOverlay::new(ctx.ledger());
        let berth_overlay = BerthOccupancyOverlay::new(ctx.berth());
        Self {
            ctx,
            assignment_overlay,
            berth_overlay,
            operations: Vec::new(),
        }
    }

    pub fn problem(&self) -> &'brand Problem<'base, T, C> {
        self.ctx.problem()
    }

    fn add_operation<O>(&mut self, op: O)
    where
        O: Into<Operation<'brand, 'base, T, C>>,
    {
        self.operations.push(op.into());
    }

    pub fn propose_unassign(
        &mut self,
        assignment: &'brand MovableAssignment<'brand, 'base, T, C>,
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
        assignment: &Assignment<'base, T, C>,
    ) -> Result<(), StageError> {
        let rect: SpaceTimeRectangle<T> = assignment.into();
        self.assignment_overlay.commit_assignment(assignment)?;
        self.berth_overlay.occupy(&rect);
        self.add_operation(AssignOperation::new(assignment.clone()));
        Ok(())
    }
}
