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

use std::{fmt::Display, marker::PhantomData};

use crate::{
    domain::{SpaceTimeRectangle, Version},
    ledger::{AssignmentLedger, AssignmentLedgerOverlay, StageError},
    occupancy::{BerthOccupancy, BerthOccupancyOverlay},
    quay::{QuayRead, QuaySpaceIntervalOutOfBoundsError},
};
use dock_alloc_core::domain::{SpaceInterval, TimeInterval};
use dock_alloc_model::{
    AnyAssignmentRef, AssignmentRef, Fixed, FixedRequestId, Kind, Movable, MovableRequestId,
    Problem, Request,
};
use num_traits::{PrimInt, Signed};

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
    T: PrimInt + Signed + 'static,
    C: PrimInt + Signed + 'static,
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
        F: for<'bo, 'al> FnOnce(PlanBuilder<'bo, 'p, 'al, T, C, Q>) -> R,
    {
        let alov = AssignmentLedgerOverlay::new(self.ledger());
        let bov = BerthOccupancyOverlay::new(self.berth());
        f(PlanBuilder::new(self.problem(), alov, bov))
    }
}

impl<'al, T, C> From<AssignmentRef<'al, Movable, T, C>> for SpaceTimeRectangle<T>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(a: AssignmentRef<'al, Movable, T, C>) -> Self {
        // Time
        let start_time = a.start_time();
        let processing_duration = a.request().processing_duration();
        let end_time = start_time + processing_duration;

        // Space
        let space = a.start_position();
        let len = a.request().length();
        SpaceTimeRectangle::new(
            SpaceInterval::new(space, space + len),
            TimeInterval::new(start_time, end_time),
        )
    }
}

impl<'p, K, T, C> From<&AssignmentRef<'p, K, T, C>> for SpaceTimeRectangle<T>
where
    K: Kind,
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(a: &AssignmentRef<'p, K, T, C>) -> Self {
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

pub struct PlanBuilder<'bo, 'p, 'al, T, C, Q>
where
    T: PrimInt + Signed + 'static,
    C: PrimInt + Signed + 'static,
    Q: QuayRead,
{
    problem: &'p Problem<T, C>,
    overlay: AssignmentLedgerOverlay<'p, 'al, T, C>,
    berth_overlay: BerthOccupancyOverlay<'bo, 'p, T, Q>,
}

pub struct Explorer<'bo, 'p, 'al, 'pb, T, C, Q>
where
    T: PrimInt + Signed + 'static,
    C: PrimInt + Signed + 'static,
    Q: QuayRead,
{
    builder: &'pb PlanBuilder<'bo, 'p, 'al, T, C, Q>,
}

impl<'bo, 'p, 'al, 'pb, T, C, Q> Explorer<'bo, 'p, 'al, 'pb, T, C, Q>
where
    T: PrimInt + Signed + 'static,
    C: PrimInt + Signed + 'static,
    Q: QuayRead,
{
    #[allow(dead_code)]
    #[inline]
    fn new(builder: &'pb PlanBuilder<'bo, 'p, 'al, T, C, Q>) -> Self {
        Self { builder }
    }

    #[inline]
    pub fn iter_fixed_ids(&self) -> impl Iterator<Item = &FixedRequestId> + '_ {
        self.builder.overlay.iter_fixed_ids()
    }

    #[inline]
    pub fn iter_fixed_assignments(
        &self,
    ) -> impl Iterator<Item = AssignmentRef<'_, Fixed, T, C>> + '_ {
        self.builder.overlay.iter_fixed_assignments()
    }

    #[inline]
    pub fn iter_movable_ids(&self) -> impl Iterator<Item = &MovableRequestId> + '_ {
        self.builder.overlay.iter_movable_ids()
    }

    #[inline]
    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = AssignmentRef<'p, Movable, T, C>> + '_ {
        self.builder.overlay.iter_movable_assignments()
    }

    #[inline]
    pub fn iter_unassigned_requests(&self) -> impl Iterator<Item = &Request<Movable, T, C>> + '_ {
        self.builder.overlay.iter_unassigned_requests()
    }

    #[inline]
    pub fn iter_assigned_requests(&self) -> impl Iterator<Item = &Request<Movable, T, C>> + '_ {
        self.builder.overlay.iter_assigned_requests()
    }

    #[inline]
    pub fn iter_assignments(&self) -> impl Iterator<Item = AnyAssignmentRef<'_, T, C>> + '_ {
        self.builder.overlay.iter_assignments()
    }

    pub fn iter_slots_for_request(
        &self,
        request: &Request<Movable, T, C>,
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
                let time_interval =
                    TimeInterval::new(slot.start_time(), slot.start_time() + processing_duration);
                FreeSlot::new(slot.space(), time_interval)
            })
    }

    pub fn iter_slots_for_request_within(
        &self,
        request: &Request<Movable, T, C>,
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
                        let time = TimeInterval::new(slot.start_time(), slot.start_time() + proc);
                        FreeSlot::new(slot.space(), time)
                    })
            })
            .into_iter()
            .flatten()
    }
}

impl<'bo, 'p, 'al, T, C, Q> PlanBuilder<'bo, 'p, 'al, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    pub fn new(
        problem: &'p Problem<T, C>,
        overlay: AssignmentLedgerOverlay<'p, 'al, T, C>,
        berth_overlay: BerthOccupancyOverlay<'bo, 'p, T, Q>,
    ) -> Self {
        Self {
            problem,
            overlay,
            berth_overlay,
        }
    }

    #[inline]
    pub fn problem(&self) -> &'p Problem<T, C> {
        self.problem
    }

    #[inline]
    pub fn with_explorer<'pb, F, R>(&'pb self, f: F) -> R
    where
        F: FnOnce(&Explorer<'bo, 'p, 'al, 'pb, T, C, Q>) -> R,
    {
        let explorer = Explorer { builder: self };
        f(&explorer)
    }

    pub fn propose_unassign(
        &mut self,
        assignment: &AssignmentRef<'p, Movable, T, C>,
    ) -> Result<FreeSlot<'bo, T>, ProposeError>
    where
        'al: 'p,
    {
        let proc = assignment.request().processing_duration();
        let time = TimeInterval::new(assignment.start_time(), assignment.start_time() + proc);
        let len = assignment.request().length();
        let space = SpaceInterval::new(
            assignment.start_position(),
            assignment.start_position() + len,
        );
        let free: FreeSlot<'bo, T> = FreeSlot::new(space, time);
        let rect: SpaceTimeRectangle<T> = (*assignment).into();
        self.overlay.uncommit_assignment(assignment)?;
        self.berth_overlay.free(&rect)?;

        Ok(free)
    }

    pub fn propose_assign(
        &mut self,
        req: &'p Request<Movable, T, C>,
        slot: FreeSlot<'bo, T>,
    ) -> Result<AssignmentRef<'p, Movable, T, C>, ProposeError> {
        let a = AssignmentRef::new(req, slot.space().start(), slot.time().start());
        let ma = self
            .overlay
            .commit_assignment(req, slot.time().start(), slot.space().start())?;
        let rect: SpaceTimeRectangle<T> = a.into();
        self.berth_overlay.occupy(&rect)?;
        Ok(ma)
    }
}
