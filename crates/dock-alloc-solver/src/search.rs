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
    ledger::{
        AssignmentLedger, AssignmentLedgerOverlay, BrandedMoveableAssignment,
        BrandedMoveableRequest, FixedHandle, MovableHandle, StageError,
    },
    occupancy::{BerthOccupancy, BerthOccupancyOverlay},
    quay::{QuayRead, QuaySpaceIntervalOutOfBoundsError},
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

impl<'p, T, C> From<&Assignment<'p, T, C>> for SpaceTimeRectangle<T>
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Plan<'brand, 'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    operations: Vec<Operation<'brand, 'p, T, C>>,
}

impl<'brand, 'p, T, C> Plan<'brand, 'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(operations: Vec<Operation<'brand, 'p, T, C>>) -> Self {
        Self { operations }
    }

    #[inline]
    pub fn operations(&self) -> &Vec<Operation<'brand, 'p, T, C>> {
        &self.operations
    }

    #[inline]
    pub fn iter_operations(&self) -> impl DoubleEndedIterator<Item = &Operation<'brand, 'p, T, C>> {
        self.operations.iter()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProposeError {
    Stage(StageError),
    QuaySpaceIntervalOutOfBounds(QuaySpaceIntervalOutOfBoundsError),
}

impl From<StageError> for ProposeError {
    fn from(e: StageError) -> Self {
        ProposeError::Stage(e)
    }
}

impl From<QuaySpaceIntervalOutOfBoundsError> for ProposeError {
    fn from(e: QuaySpaceIntervalOutOfBoundsError) -> Self {
        ProposeError::QuaySpaceIntervalOutOfBounds(e)
    }
}

impl Display for ProposeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProposeError::Stage(e) => write!(f, "{}", e),
            ProposeError::QuaySpaceIntervalOutOfBounds(e) => {
                write!(f, "{}", e)
            }
        }
    }
}

impl std::error::Error for ProposeError {}

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
    ) -> Result<FreeSlot<'brand, T>, ProposeError> {
        let free: FreeSlot<'brand, T> = assignment.into();
        let rect: SpaceTimeRectangle<T> = assignment.into();
        self.assignment_overlay.uncommit_assignment(assignment)?;
        self.berth_overlay.free(&rect)?;
        self.add_operation(UnassignOperation::new(assignment));
        Ok(free)
    }

    pub fn propose_assign(
        &mut self,
        req: &BrandedMoveableRequest<'brand, 'p, T, C>,
        slot: FreeSlot<'brand, T>,
    ) -> Result<BrandedMoveableAssignment<'brand, 'p, T, C>, ProposeError> {
        let a = Assignment::borrowed(req.request(), slot.space().start(), slot.time().start());
        let ma = self.assignment_overlay.commit_assignment(&a)?;
        let rect: SpaceTimeRectangle<T> = (&a).into();
        self.berth_overlay.occupy(&rect)?;
        self.operations
            .push(AssignOperation::new(ma.clone()).into());
        Ok(ma)
    }

    pub fn build(self) -> Plan<'brand, 'p, T, C> {
        Plan::new(self.operations)
    }
}

#[cfg(test)]
mod tests {
    use crate::quay::BooleanVecQuay;

    use super::*;
    use dock_alloc_core::domain::{
        Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
    };
    use dock_alloc_model::{ProblemBuilder, Request, RequestId};

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

    fn asg<'r>(r: &'r Request, pos: usize, time: i64) -> Assignment<'r, i64, i64> {
        Assignment::borrowed(r, SpacePosition::new(pos), TimePoint::new(time))
    }

    // Helper for creating a standard test request
    fn test_request() -> Request {
        req_ok(1, 10, 5, 0, 100, 0, 100)
    }

    #[test]
    fn free_slot_from_branded_movable_assignment_is_correct() {
        // Set up problem
        let r = test_request();
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(200));
        b.add_unassigned_request(r.clone()).unwrap();
        let p = b.build();
        let mut ledger = AssignmentLedger::from(&p);

        // commit once to get a branded assignment
        let a = asg(&r, 30, 10); // space [30, 40), time [10, 15)
        let ma = ledger.commit_assignment(&a).expect("commit");

        let slot = FreeSlot::from(&ma);

        assert_eq!(
            slot.space(),
            SpaceInterval::new(SpacePosition::new(30), SpacePosition::new(40))
        );
        assert_eq!(
            slot.time(),
            TimeInterval::new(TimePoint::new(10), TimePoint::new(15))
        );
    }

    #[test]
    fn spacetime_rectangle_matches_for_assignment_and_branded() {
        // Set up problem
        let r = test_request();
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(200));
        b.add_unassigned_request(r.clone()).unwrap();
        let p = b.build();
        let mut ledger = AssignmentLedger::from(&p);

        let a = asg(&r, 7, 2);
        let ma = ledger.commit_assignment(&a).expect("commit");

        let rect_from_a: SpaceTimeRectangle<i64> = (&a).into();
        let rect_from_ma: SpaceTimeRectangle<i64> = (&ma).into();

        assert_eq!(rect_from_a.space(), rect_from_ma.space());
        assert_eq!(rect_from_a.time(), rect_from_ma.time());

        // sanity on exact coordinates: len=10, proc=5 from req_ok
        assert_eq!(
            rect_from_a.space(),
            SpaceInterval::new(SpacePosition::new(7), SpacePosition::new(17))
        );
        assert_eq!(
            rect_from_a.time(),
            TimeInterval::new(TimePoint::new(2), TimePoint::new(7))
        );
    }

    #[test]
    fn plan_records_operations_in_order() {
        // Set up problem
        let r = test_request();
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(200));
        b.add_unassigned_request(r.clone()).unwrap();
        let p = b.build();
        let mut ledger = AssignmentLedger::from(&p);

        let a = asg(&r, 0, 0);
        let ma = ledger.commit_assignment(&a).expect("commit");

        // record: unassign then assign (order matters)
        let un = UnassignOperation::new(&ma);
        let reassign = AssignOperation::new(ma.clone());

        let plan = Plan::new(vec![un.into(), reassign.into()]);

        // iterate and ensure order & kinds
        let mut it = plan.iter_operations();
        match it.next().unwrap() {
            Operation::Unassign(op) => assert_eq!(op.moveable().id(), ma.id()),
            other => panic!("expected Unassign first, got {:?}", other),
        }
        match it.next().unwrap() {
            Operation::Assign(op) => assert_eq!(op.assignment().id(), ma.id()),
            other => panic!("expected Assign second, got {:?}", other),
        }
        assert!(it.next().is_none());
    }

    #[test]
    fn free_slot_constructor_is_opaque_but_round_trips() {
        // Construct by hand and ensure getters are stable.
        let s = SpaceInterval::new(SpacePosition::new(5), SpacePosition::new(12));
        let t = TimeInterval::new(TimePoint::new(20), TimePoint::new(25));
        let slot = FreeSlot::<'static, i64>::new(s, t);

        assert_eq!(slot.space(), s);
        assert_eq!(slot.time(), t);
    }

    #[test]
    fn overlay_unassign_makes_request_discoverable_again() {
        // Build problem with one movable request
        let r = req_ok(1, 10, 5, 0, 100, 0, 100);
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(200));
        b.add_unassigned_request(r.clone()).unwrap();
        let p = b.build();

        // Base ledger + base commit
        let mut ledger = AssignmentLedger::from(&p);
        let a = asg(&r, 30, 10);
        let ma = ledger.commit_assignment(&a).expect("commit");

        // Create overlay and stage uncommit
        let mut ov = AssignmentLedgerOverlay::new(&ledger);
        let _ = ov.uncommit_assignment(&ma).expect("stage uncommit");

        // After uncommit:
        //  - request should be visible as *unassigned* in the overlay
        //  - and should NOT be visible as assigned
        let unassigned_ids: Vec<_> = ov.iter_unassigned_requests().map(|mr| mr.id()).collect();
        assert!(unassigned_ids.contains(&r.id()));

        let assigned_ids: Vec<_> = ov.iter_assigned_requests().map(|mr| mr.id()).collect();
        assert!(!assigned_ids.contains(&r.id()));
    }

    #[test]
    fn explorer_finds_freed_slot_after_unassign_within_tight_window() {
        let r = req_ok(1, 10, 5, 0, 100, 0, 100);
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(200));
        b.add_unassigned_request(r.clone()).unwrap();
        let p = b.build();

        let mut ledger = AssignmentLedger::from(&p);
        let a = asg(&r, 50, 20); // occupies [50,60) × [20,25)
        let ma = ledger.commit_assignment(&a).expect("commit");
        let mut berth: BerthOccupancy<_, _> =
            BerthOccupancy::<i64, BooleanVecQuay>::new(500.into());

        let base_rect: SpaceTimeRectangle<i64> = (&a).into();
        berth.occupy(&base_rect).expect("seed base occupancy"); // adjust if signature differs

        let ctx = ProposeCtx::new(&ledger, &berth, &p, Version::new(0));
        let mut pb = PlanBuilder::new(&ctx);

        // Before unassign: explorer should NOT produce a slot in the exact tight window.
        pb.with_explorer(|ex| {
            // While it's assigned, the request is in 'assigned' view:
            let req_assigned = ex
                .iter_assigned_requests()
                .find(|mr| mr.id() == r.id())
                .expect("assigned req present");

            let t_win = TimeInterval::new(a.start_time(), a.start_time() + r.processing_duration());
            let s_win = SpaceInterval::new(a.start_position(), a.start_position() + r.length());
            let any = ex
                .iter_slots_for_request_within(&req_assigned, t_win, s_win)
                .next();
            assert!(
                any.is_none(),
                "slot should NOT be visible before unassign within tight window"
            );
        });

        // Stage unassign (frees it in the overlay)
        let freed_slot = pb.propose_unassign(&ma).expect("propose_unassign");

        // After unassign: explorer should show a slot that starts at freed start-time and covers space.
        pb.with_explorer(|ex| {
            // Now it's unassigned:
            let req_unassigned = ex
                .iter_unassigned_requests()
                .find(|mr| mr.id() == r.id())
                .expect("unassigned req present");

            let t_win = TimeInterval::new(freed_slot.time().start(), freed_slot.time().end());
            let s_win = SpaceInterval::new(freed_slot.space().start(), freed_slot.space().end());

            let proc = r.processing_duration();

            let mut found_covering = false;
            for slot in ex.iter_slots_for_request_within(&req_unassigned, t_win, s_win) {
                // Iterator returns 'start time + space'; duration should match proc.
                let starts_at_freed_time = slot.time().start() == freed_slot.time().start();
                let duration_ok = slot.time().duration() == proc;

                // Be lenient: slot may be equal or a superset in space.
                let covers_space = slot.space().start() <= freed_slot.space().start()
                    && slot.space().end() >= freed_slot.space().end();

                if starts_at_freed_time && duration_ok && covers_space {
                    found_covering = true;
                    break;
                }
            }

            assert!(
                found_covering,
                "expected to rediscover a slot covering the freed region at the same start time"
            );
        });
    }

    #[test]
    fn iter_slots_for_request_within_respects_clamping_and_invariants() {
        let r = req_ok(1, 10, 5, 0, 100, 0, 100);
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(200));
        b.add_unassigned_request(r.clone()).unwrap();
        let p = b.build();

        let ledger = AssignmentLedger::from(&p);
        let berth: BerthOccupancy<_, _> =
            BerthOccupancy::<i64, BooleanVecQuay>::new(SpaceLength::new(200));

        let ctx = ProposeCtx::new(&ledger, &berth, &p, Version::new(0));
        let pb = PlanBuilder::new(&ctx);

        pb.with_explorer(|ex| {
            let req = ex
                .iter_unassigned_requests()
                .next()
                .expect("one unassigned request");

            // Too-short time window (duration < proc): no slots
            let too_short_time = TimeInterval::new(TimePoint::new(0), TimePoint::new(3)); // proc=5
            let big_space = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100));
            assert!(
                ex.iter_slots_for_request_within(&req, too_short_time, big_space)
                    .next()
                    .is_none(),
                "should yield no slots when time window < proc"
            );

            // Too-narrow space window (measure < len): no slots
            let ok_time = TimeInterval::new(TimePoint::new(0), TimePoint::new(100));
            let too_narrow_space = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(8)); // len=10
            assert!(
                ex.iter_slots_for_request_within(&req, ok_time, too_narrow_space)
                    .next()
                    .is_none(),
                "should yield no slots when space width < len"
            );

            // Valid wide windows: all yielded slots satisfy invariants
            let mut it = ex
                .iter_slots_for_request_within(&req, ok_time, big_space)
                .take(8); // sample a few
            let mut saw_any = false;
            while let Some(slot) = it.next() {
                saw_any = true;
                // duration equals processing time
                assert_eq!(slot.time().duration(), req.processing_duration());
                // space width is >= required len (can be equal or larger)
                assert!(slot.space().measure() >= req.length());
                // slot fully inside the clamped search windows
                assert!(ok_time.contains_interval(&slot.time()));
                assert!(big_space.contains_interval(&slot.space()));
                // slot also inside the request's feasible windows by construction
                assert!(req.feasible_time_window().contains_interval(&slot.time()));
                assert!(req.feasible_space_window().contains_interval(&slot.space()));
            }
            assert!(saw_any, "expected at least one feasible slot");
        });
    }

    #[test]
    fn assign_hides_slot_then_unassign_restores_covering_slot() {
        let r = req_ok(1, 10, 5, 0, 100, 0, 100);
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(200));
        b.add_unassigned_request(r.clone()).unwrap();
        let p = b.build();

        let ledger = AssignmentLedger::from(&p);
        let berth: BerthOccupancy<_, _> =
            BerthOccupancy::<i64, BooleanVecQuay>::new(SpaceLength::new(200));

        let ctx = ProposeCtx::new(&ledger, &berth, &p, Version::new(0));
        let mut pb = PlanBuilder::new(&ctx);

        // Pick request + slot while unassigned
        let (req, slot) = pb.with_explorer(|ex| {
            let req = ex.iter_unassigned_requests().next().unwrap();
            let slot = ex.iter_slots_for_request(&req).next().unwrap();
            (req, slot)
        });

        assert!(req.id() == r.id(), "request id must match");

        let asg_rect = SpaceTimeRectangle::new(
            SpaceInterval::new(slot.space().start(), slot.space().start() + req.length()),
            slot.time(),
        );

        let ma = pb.propose_assign(&req, slot).expect("assign");
        assert!(pb.berth_overlay.is_occupied(&asg_rect).unwrap());
        let freed = pb.propose_unassign(&ma).expect("unassign");
        assert!(pb.berth_overlay.is_free(&asg_rect).unwrap());

        pb.with_explorer(|ex| {
            // refresh request from overlay
            let req_unassigned = ex
                .iter_unassigned_requests()
                .find(|mr| mr.id() == req.id())
                .expect("request back in unassigned view");

            let proc = req_unassigned.processing_duration();

            // Let the iterator pick its canonical start in time and space
            let t_search = slot.time();
            let s_search = slot.space();
            let reappears = ex
                .iter_slots_for_request_within(&req_unassigned, t_search, s_search)
                .any(|cand| {
                    cand.time().duration() == proc
                        && cand.time().start() <= freed.time().start()
                        && cand.space().start() <= freed.space().start()
                        && cand.space().end() >= freed.space().end()
                });

            assert!(
                reappears,
                "expected a slot in the feasible window that covers the freed space to reappear"
            );
        });
    }

    #[test]
    fn plan_builder_records_operations_in_sequence_assign_then_unassign() {
        let r = req_ok(1, 10, 5, 0, 100, 0, 100);
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(200));
        b.add_unassigned_request(r.clone()).unwrap();
        let p = b.build();

        let ledger = AssignmentLedger::from(&p);
        let berth: BerthOccupancy<_, _> =
            BerthOccupancy::<i64, BooleanVecQuay>::new(SpaceLength::new(200));

        let ctx = ProposeCtx::new(&ledger, &berth, &p, Version::new(0));
        let mut pb = PlanBuilder::new(&ctx);

        // choose req + initial slot
        let (req, slot) = pb.with_explorer(|ex| {
            let req = ex
                .iter_unassigned_requests()
                .next()
                .expect("one unassigned request");
            let slot = ex
                .iter_slots_for_request(&req)
                .next()
                .expect("at least one slot");
            (req, slot)
        });

        let ma = pb.propose_assign(&req, slot).expect("assign ok");

        // immediately unassign
        let _freed = pb.propose_unassign(&ma).expect("unassign ok");

        let plan = pb.build();
        let mut it = plan.iter_operations();

        match it.next().unwrap() {
            Operation::Assign(op) => {
                assert_eq!(op.assignment().id(), ma.id());
            }
            other => panic!("expected Assign first, got {:?}", other),
        }
        match it.next().unwrap() {
            Operation::Unassign(op) => {
                assert_eq!(op.moveable().id(), ma.id());
            }
            other => panic!("expected Unassign second, got {:?}", other),
        }
        assert!(it.next().is_none());
    }

    #[test]
    fn iter_slots_for_request_produces_duration_equal_to_processing_time() {
        let r = req_ok(1, 10, 5, 0, 100, 0, 100);
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(200));
        b.add_unassigned_request(r.clone()).unwrap();
        let p = b.build();

        let ledger = AssignmentLedger::from(&p);
        let berth: BerthOccupancy<_, _> =
            BerthOccupancy::<i64, BooleanVecQuay>::new(SpaceLength::new(200));

        let ctx = ProposeCtx::new(&ledger, &berth, &p, Version::new(0));
        let pb = PlanBuilder::new(&ctx);

        pb.with_explorer(|ex| {
            let req = ex
                .iter_unassigned_requests()
                .next()
                .expect("one unassigned request");
            for slot in ex.iter_slots_for_request(&req).take(5) {
                assert_eq!(slot.time().duration(), req.processing_duration());
                assert!(slot.space().measure() >= req.length());
            }
        });
    }
}
