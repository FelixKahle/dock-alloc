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
    berth::{
        berthocc::BerthOccupancy,
        commit::BerthOverlayCommit,
        overlay::{BerthOccupancyOverlay, BrandedFreeRegion, BrandedFreeSlot},
        quay::{QuayRead, QuaySpaceIntervalOutOfBoundsError},
    },
    domain::SpaceTimeRectangle,
    framework::iter::{RegionsForRequestIter, SlotsForRequestIter},
    registry::{
        commit::LedgerOverlayCommit,
        ledger::AssignmentLedger,
        operations::Operation,
        overlay::{
            AssignmentLedgerOverlay, BrandedFixedRequestId, BrandedMovableAssignment,
            BrandedMovableRequest, BrandedMovableRequestId, StageError,
        },
    },
};
use dock_alloc_core::{
    SolverVariable,
    cost::Cost,
    space::{SpaceInterval, SpacePosition},
    time::{TimeDelta, TimeInterval, TimePoint},
};
use dock_alloc_model::prelude::*;
use std::fmt::{Debug, Display};

pub struct PlanningContext<'p, 'al, 'bo, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    ledger: &'al AssignmentLedger<'p, T, C>,
    berth: &'bo BerthOccupancy<T, Q>,
    problem: &'p Problem<T, C>,
}

impl<'p, 'al, 'bo, T, C, Q> PlanningContext<'p, 'al, 'bo, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub fn new(
        ledger: &'al AssignmentLedger<'p, T, C>,
        berth: &'bo BerthOccupancy<T, Q>,
        problem: &'p Problem<T, C>,
    ) -> Self {
        Self {
            ledger,
            berth,
            problem,
        }
    }

    #[inline]
    pub fn ledger(&self) -> &'al AssignmentLedger<'p, T, C> {
        self.ledger
    }
    #[inline]
    pub fn berth(&self) -> &'bo BerthOccupancy<T, Q> {
        self.berth
    }
    #[inline]
    pub fn problem(&self) -> &'p Problem<T, C> {
        self.problem
    }

    pub fn with_builder<F, R>(&self, f: F) -> R
    where
        F: for<'alob, 'boob> FnOnce(PlanBuilder<'alob, 'boob, 'p, 'bo, 'al, T, C, Q>) -> R,
    {
        let alov = AssignmentLedgerOverlay::new(self.ledger());
        let bov = BerthOccupancyOverlay::new(self.berth());
        f(PlanBuilder::new(self.problem(), alov, bov))
    }
}

impl<'al, 'p, T, C> From<&BrandedMovableAssignment<'al, 'p, T, C>> for SpaceTimeRectangle<T>
where
    T: SolverVariable,
    C: SolverVariable,
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
    T: SolverVariable,
    C: SolverVariable,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlanEval<T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    delta_cost: Cost<C>,
    delta_wait: TimeDelta<T>,
    delta_dev: i64,
}

impl<T, C> PlanEval<T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    #[inline]
    fn new(delta_cost: Cost<C>, delta_wait: TimeDelta<T>, delta_dev: i64) -> Self {
        Self {
            delta_cost,
            delta_wait,
            delta_dev,
        }
    }

    #[inline]
    pub fn delta_cost(&self) -> Cost<C> {
        self.delta_cost
    }

    #[inline]
    pub fn delta_wait(&self) -> TimeDelta<T> {
        self.delta_wait
    }

    #[inline]
    pub fn delta_dev(&self) -> i64 {
        self.delta_dev
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan<'p, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    eval: PlanEval<T, C>,
    berth_commit: BerthOverlayCommit<T>,
    ledger_commit: LedgerOverlayCommit<'p, T, C>,
}

impl<'p, T, C> Display for Plan<'p, T, C>
where
    T: SolverVariable + Display,
    C: SolverVariable + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let berth_op_string = self
            .berth_commit
            .operations()
            .iter()
            .map(|op| format!("{}", op))
            .collect::<Vec<_>>()
            .join(", ");
        let ledger_op_string = self
            .ledger_commit
            .operations()
            .iter()
            .map(|op| format!("{}", op))
            .collect::<Vec<_>>()
            .join(", ");

        write!(
            f,
            "Plan(frees: {}, occupies: {}, eval: Δcost={}, Δwait={}, Δdev={} | berth_ops: [{}] | ledger_ops: [{}])",
            self.berth_commit.operations().len(),
            self.ledger_commit.operations().len(),
            self.eval.delta_cost(),
            self.eval.delta_wait(),
            self.eval.delta_dev(),
            berth_op_string,
            ledger_op_string
        )
    }
}

impl<'p, T, C> Plan<'p, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    #[inline]
    fn new(
        eval: PlanEval<T, C>,
        berth_commit: BerthOverlayCommit<T>,
        ledger_commit: LedgerOverlayCommit<'p, T, C>,
    ) -> Self {
        Self {
            eval,
            berth_commit,
            ledger_commit,
        }
    }

    pub fn operation_count(&self) -> usize {
        self.berth_commit.operations().len() + self.ledger_commit.operations().len()
    }

    pub fn eval(&self) -> &PlanEval<T, C> {
        &self.eval
    }

    pub fn berth_commit(&self) -> &BerthOverlayCommit<T> {
        &self.berth_commit
    }

    pub fn ledger_commit(&self) -> &LedgerOverlayCommit<'p, T, C> {
        &self.ledger_commit
    }
}

#[repr(transparent)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FreeRegionViolationError<T: SolverVariable>(SpaceTimeRectangle<T>);

impl<T: SolverVariable> FreeRegionViolationError<T> {
    #[inline]
    pub fn requested(&self) -> &SpaceTimeRectangle<T> {
        &self.0
    }
}

impl<T: SolverVariable + Display> Display for FreeRegionViolationError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Violated free region: {}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProposeError<T: SolverVariable> {
    Stage(StageError),
    QuaySpaceIntervalOutOfBounds(QuaySpaceIntervalOutOfBoundsError),
    FreeRegionViolation(FreeRegionViolationError<T>),
}

impl<T: SolverVariable> From<StageError> for ProposeError<T> {
    #[inline]
    fn from(e: StageError) -> Self {
        ProposeError::Stage(e)
    }
}

impl<T: SolverVariable> From<QuaySpaceIntervalOutOfBoundsError> for ProposeError<T> {
    #[inline]
    fn from(e: QuaySpaceIntervalOutOfBoundsError) -> Self {
        ProposeError::QuaySpaceIntervalOutOfBounds(e)
    }
}

impl<T: SolverVariable + Display> Display for ProposeError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProposeError::Stage(e) => write!(f, "{}", e),
            ProposeError::QuaySpaceIntervalOutOfBounds(e) => write!(f, "{}", e),
            ProposeError::FreeRegionViolation(e) => write!(f, "{}", e),
        }
    }
}

impl<T: SolverVariable + Debug + Display> std::error::Error for ProposeError<T> {}

#[derive(Debug, Clone)]
pub struct PlanBuilder<'alob, 'boob, 'p, 'bo, 'al, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    problem: &'p Problem<T, C>,
    assignment_overlay: AssignmentLedgerOverlay<'alob, 'p, 'al, T, C>,
    berth_overlay: BerthOccupancyOverlay<'boob, 'bo, T, Q>,
}

pub struct Explorer<'alob, 'boob, 'p, 'bo, 'al, 'pb, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    assignment_overlay: &'pb AssignmentLedgerOverlay<'alob, 'p, 'al, T, C>,
    berth_overlay: &'pb BerthOccupancyOverlay<'boob, 'bo, T, Q>,
}

impl<'alob, 'boob, 'p, 'bo, 'al, 'pb, T, C, Q> Explorer<'alob, 'boob, 'p, 'bo, 'al, 'pb, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    #[inline]
    fn new(
        assignment_overlay: &'pb AssignmentLedgerOverlay<'alob, 'p, 'al, T, C>,
        berth_overlay: &'pb BerthOccupancyOverlay<'boob, 'bo, T, Q>,
    ) -> Self {
        Self {
            assignment_overlay,
            berth_overlay,
        }
    }

    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = BrandedFixedRequestId<'alob>> + '_ {
        self.assignment_overlay.iter_fixed_handles()
    }

    #[inline]
    pub fn iter_fixed_assignments(
        &self,
    ) -> impl Iterator<Item = AssignmentRef<'_, Fixed, T, C>> + '_ {
        self.assignment_overlay.iter_fixed_assignments()
    }

    #[inline]
    pub fn iter_movable_handles(
        &self,
    ) -> impl Iterator<Item = BrandedMovableRequestId<'alob>> + '_ {
        self.assignment_overlay.iter_movable_handles()
    }

    #[inline]
    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = BrandedMovableAssignment<'alob, 'p, T, C>> + '_ {
        self.assignment_overlay.iter_movable_assignments()
    }

    #[inline]
    pub fn iter_unassigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMovableRequest<'alob, 'p, T, C>> + '_ {
        self.assignment_overlay.iter_unassigned_requests()
    }

    #[inline]
    pub fn iter_assigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMovableRequest<'alob, 'p, T, C>> + '_ {
        self.assignment_overlay.iter_assigned_requests()
    }

    #[inline]
    pub fn iter_assignments(&self) -> impl Iterator<Item = AnyAssignmentRef<'_, T, C>> + '_ {
        self.assignment_overlay.iter_assignments()
    }

    pub fn iter_slots_for_request_within<'s>(
        &'s self,
        request: &'s BrandedMovableRequest<'alob, 'p, T, C>,
        time_search_window: TimeInterval<T>,
        space_search_window: SpaceInterval,
    ) -> SlotsForRequestIter<'s, 's, 'boob, 'bo, T, Q> {
        let p = request.processing_duration();
        let len = request.length();

        let arrival = request.arrival_time();
        let twin_start = if time_search_window.start() < arrival {
            arrival
        } else {
            time_search_window.start()
        };
        let twin_end = time_search_window.end();
        let twin = TimeInterval::new(twin_start, twin_end);

        let windows = request.feasible_space_windows();

        SlotsForRequestIter::new(
            self.berth_overlay,
            windows,
            twin,
            p,
            len,
            space_search_window,
        )
    }

    pub fn iter_regions_for_request_within<'s>(
        &'s self,
        request: &'s BrandedMovableRequest<'alob, 'p, T, C>,
        time_search_window: TimeInterval<T>,
        space_search_window: SpaceInterval,
    ) -> RegionsForRequestIter<'s, 's, 'boob, 'bo, T, Q> {
        let p = request.processing_duration();
        let len = request.length();

        let arrival = request.arrival_time();
        let twin_start = if time_search_window.start() < arrival {
            arrival
        } else {
            time_search_window.start()
        };
        let twin_end = time_search_window.end();
        let twin = TimeInterval::new(twin_start, twin_end);

        let windows = request.feasible_space_windows();

        RegionsForRequestIter::new(
            self.berth_overlay,
            windows,
            twin,
            p,
            len,
            space_search_window,
        )
    }
}

impl<'alob, 'boob, 'p, 'bo, 'al, T, C, Q> PlanBuilder<'alob, 'boob, 'p, 'bo, 'al, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn new(
        problem: &'p Problem<T, C>,
        assignment_overlay: AssignmentLedgerOverlay<'alob, 'p, 'al, T, C>,
        berth_overlay: BerthOccupancyOverlay<'boob, 'bo, T, Q>,
    ) -> Self {
        Self {
            problem,
            assignment_overlay,
            berth_overlay,
        }
    }

    #[inline]
    pub fn problem(&self) -> &'p Problem<T, C> {
        self.problem
    }

    #[inline]
    pub fn with_explorer<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&Explorer<'alob, 'boob, 'p, 'bo, 'al, '_, T, C, Q>) -> R,
    {
        let ex = Explorer::new(&self.assignment_overlay, &self.berth_overlay);
        f(&ex)
    }

    pub fn clear(&mut self) {
        self.assignment_overlay.clear();
        self.berth_overlay.clear();
    }

    pub fn build(self) -> Plan<'p, T, C>
    where
        C: TryFrom<T> + TryFrom<usize>,
    {
        let berth_commit = self.berth_overlay.into_commit();
        let ledger_commit = self.assignment_overlay.into_commit();

        let mut delta_cost = Cost::<C>::new(C::zero());
        let mut delta_wait = TimeDelta::<T>::new(T::zero());
        let mut delta_dev: i64 = 0;

        for op in ledger_commit.operations() {
            match op {
                Operation::Assign(assign) => {
                    let c = assign.assignment().cost();
                    let w = assign.assignment().waiting_time();
                    let d = assign.assignment().position_deviation(); // SpaceLength
                    delta_cost += c;
                    delta_wait += w;
                    delta_dev += d.value() as i64;
                }
                Operation::Unassign(unassign) => {
                    let c = unassign.assignment().cost();
                    let w = unassign.assignment().waiting_time();
                    let d = unassign.assignment().position_deviation(); // SpaceLength
                    delta_cost -= c;
                    delta_wait -= w;
                    delta_dev -= d.value() as i64; // now safe
                }
            }
        }

        let eval = PlanEval::new(delta_cost, delta_wait, delta_dev);
        Plan::new(eval, berth_commit, ledger_commit)
    }

    #[inline]
    pub fn begin(&mut self) -> Txn<'_, 'alob, 'boob, 'p, 'bo, 'al, T, C, Q> {
        // Compute children before taking &mut self (avoids E0502)
        let alov_child = self.assignment_overlay.clone();
        let bov_child = self.berth_overlay.clone();

        Txn {
            parent: self,
            alov: Some(alov_child),
            bov: Some(bov_child),
        }
    }
}

pub struct Txn<'pb, 'alob, 'boob, 'p, 'bo, 'al, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    parent: &'pb mut PlanBuilder<'alob, 'boob, 'p, 'bo, 'al, T, C, Q>,
    alov: Option<AssignmentLedgerOverlay<'alob, 'p, 'al, T, C>>,
    bov: Option<BerthOccupancyOverlay<'boob, 'bo, T, Q>>,
}

impl<'pb, 'alob, 'boob, 'p, 'bo, 'al, T, C, Q> Txn<'pb, 'alob, 'boob, 'p, 'bo, 'al, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    #[inline]
    pub fn ex(&self) -> Explorer<'alob, 'boob, 'p, 'bo, 'al, '_, T, C, Q> {
        let alov = self.alov.as_ref().expect("txn overlays already taken");
        let bov = self.bov.as_ref().expect("txn overlays already taken");
        Explorer::new(alov, bov)
    }

    pub fn problem(&self) -> &'p Problem<T, C> {
        self.parent.problem()
    }

    pub fn with_explorer<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&Explorer<'alob, 'boob, 'p, 'bo, 'al, '_, T, C, Q>) -> R,
    {
        let ex = self.ex();
        f(&ex)
    }

    pub fn propose_unassign(
        &mut self,
        a: &BrandedMovableAssignment<'alob, 'p, T, C>,
    ) -> Result<BrandedFreeRegion<'boob, T>, ProposeError<T>> {
        let rect: SpaceTimeRectangle<T> = a.into();
        let alov = self.alov.as_mut().expect("txn overlays already taken");
        let bov = self.bov.as_mut().expect("txn overlays already taken");
        alov.uncommit_assignment(a)?;
        let free = bov.free(&rect)?;
        Ok(free)
    }

    pub fn propose_assign_at(
        &mut self,
        req: &BrandedMovableRequest<'alob, 'p, T, C>,
        region: &BrandedFreeRegion<'boob, T>,
        t: TimePoint<T>,
        s: SpacePosition,
    ) -> Result<BrandedMovableAssignment<'alob, 'p, T, C>, ProposeError<T>> {
        let rect = SpaceTimeRectangle::new(
            SpaceInterval::new(s, s + req.length()),
            TimeInterval::new(t, t + req.processing_duration()),
        );
        if !region.region().rectangle().contains(&rect) {
            return Err(ProposeError::FreeRegionViolation(FreeRegionViolationError(
                rect,
            )));
        }
        let alov = self.alov.as_mut().expect("txn overlays already taken");
        let bov = self.bov.as_mut().expect("txn overlays already taken");
        let a = AssignmentRef::new(req.request(), s, t);
        let r2: SpaceTimeRectangle<T> = a.into();
        let ma = alov.commit_assignment(req.request(), t, s)?;
        bov.occupy(&r2)?;
        Ok(ma)
    }

    pub fn propose_assign(
        &mut self,
        req: &BrandedMovableRequest<'alob, 'p, T, C>,
        slot: BrandedFreeSlot<'boob, T>,
    ) -> Result<BrandedMovableAssignment<'alob, 'p, T, C>, ProposeError<T>> {
        let alov = self.alov.as_mut().expect("txn overlays already taken");
        let bov = self.bov.as_mut().expect("txn overlays already taken");
        let a = AssignmentRef::new(
            req.request(),
            slot.slot().space().start(),
            slot.slot().start_time(),
        );
        let rect: SpaceTimeRectangle<T> = a.into();
        let ma = alov.commit_assignment(
            req.request(),
            slot.slot().start_time(),
            slot.slot().space().start(),
        )?;
        bov.occupy(&rect)?;
        Ok(ma)
    }

    /// Merge child overlays back into the parent; dropping without commit rolls back.
    pub fn commit(mut self) {
        let alov = self.alov.take().expect("txn overlays already taken");
        let bov = self.bov.take().expect("txn overlays already taken");
        self.parent.assignment_overlay.absorb(alov);
        self.parent.berth_overlay.absorb(bov);
    }

    pub fn discard(mut self) {
        self.alov = None;
        self.bov = None;
    }
}
