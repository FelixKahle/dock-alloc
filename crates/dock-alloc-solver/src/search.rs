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
    domain::Version,
    ledger::{AssignmentLedger, AssignmentOverlay, MovableAssignment, MovableHandle, StageError},
    occupancy::{BerthOccupancy, BerthOccupancyOverlay},
    quay::QuayRead,
};
use dock_alloc_core::domain::{SpaceInterval, TimeInterval};
use dock_alloc_model::{MoveableRequest, Problem};
use num_traits::{PrimInt, Signed};

pub struct ProposeCtx<'base, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    ledger: &'base AssignmentLedger<'base, 'base, T, C>,
    berth: &'base BerthOccupancy<T, Q>,
    problem: &'base Problem<T, C>,
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

    pub fn problem(&self) -> &'brand Problem<T, C> {
        self.problem
    }

    pub fn stamp(&self) -> Version {
        self.stamp
    }
}

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

impl<'brand, T, C> From<&MovableAssignment<'brand, T, C>> for FreeSlot<'brand, T>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(assignment: &MovableAssignment<'brand, T, C>) -> Self {
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

pub struct UnassignOperation<'brand, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    moveable: &'brand MoveableRequest<T, C>,
    _brand: PhantomData<&'brand ()>,
}

pub struct AssignOperation<'brand, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    assignment: &'brand MovableAssignment<'brand, T, C>,
    _brand: PhantomData<&'brand ()>,
}

pub enum Operation<'brand, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    Unassign(UnassignOperation<'brand, T, C>),
    Assign(AssignOperation<'brand, T, C>),
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
    operations: Vec<Operation<'brand, T, C>>,
}

impl<'brand, 'base, T, C, Q> PlanBuilder<'brand, 'base, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
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

    pub fn propose_unassign(
        &mut self,
        assignment: &'brand MovableAssignment<'brand, T, C>,
    ) -> Result<FreeSlot<'brand, T>, StageError> {
        let free: FreeSlot<'brand, T> = assignment.into();
        let _ = self.assignment_overlay.uncommit_assignment(assignment)?;
        self.berth_overlay.free(free.time(), free.space());
        Ok(free)
    }
}
