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
        commit::BerthOverlayCommit,
        overlay::BerthOccupancyOverlay,
        prelude::BerthOccupancy,
        quay::{QuayRead, QuaySpaceIntervalOutOfBoundsError},
    },
    domain::SpaceTimeRectangle,
    state::{
        commit::LedgerOverlayCommit,
        ledger::AssignmentLedger,
        overlay::{
            AssignmentLedgerOverlay, BrandedFixedRequestId, BrandedMovableAssignment,
            BrandedMovableRequest, BrandedMovableRequestId, StageError,
        },
    },
};
use dock_alloc_core::domain::{SpaceInterval, TimeInterval};
use dock_alloc_model::{AnyAssignmentRef, AssignmentRef, Fixed, Kind, Problem};
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

pub struct ProposeCtx<'pp, 'pl, 'pb, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    ledger: &'pl AssignmentLedger<'pp, T, C>,
    berth: &'pb BerthOccupancy<T, Q>,
    problem: &'pp Problem<T, C>,
}

impl<'pp, 'pl, 'pb, T, C, Q> ProposeCtx<'pp, 'pl, 'pb, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    pub fn new(
        ledger: &'pl AssignmentLedger<'pp, T, C>,
        berth: &'pb BerthOccupancy<T, Q>,
        problem: &'pp Problem<T, C>,
    ) -> Self {
        Self {
            ledger,
            berth,
            problem,
        }
    }

    #[inline]
    pub fn ledger(&self) -> &'pl AssignmentLedger<'pp, T, C> {
        self.ledger
    }
    #[inline]
    pub fn berth(&self) -> &'pb BerthOccupancy<T, Q> {
        self.berth
    }
    #[inline]
    pub fn problem(&self) -> &'pp Problem<T, C> {
        self.problem
    }

    // Note the distinct lifetimes in PlanBuilder now: 'pp (problem), 'pb (berth), 'al (ledger ref)
    pub fn with_builder<F, R>(&self, f: F) -> R
    where
        F: for<'brand, 'bo, 'al> FnOnce(PlanBuilder<'brand, 'bo, 'pp, 'pb, 'al, T, C, Q>) -> R,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    berth_commit: BerthOverlayCommit<T>,
    ledger_commit: LedgerOverlayCommit<'p, T, C>,
}

impl<'p, T, C> Plan<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(
        berth_commit: BerthOverlayCommit<T>,
        ledger_commit: LedgerOverlayCommit<'p, T, C>,
    ) -> Self {
        Self {
            berth_commit,
            ledger_commit,
        }
    }

    pub fn berth_commit(&self) -> &BerthOverlayCommit<T> {
        &self.berth_commit
    }

    pub fn ledger_commit(&self) -> &LedgerOverlayCommit<'p, T, C> {
        &self.ledger_commit
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

pub struct PlanBuilder<'brand, 'bo, 'pp, 'pb, 'al, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    problem: &'pp Problem<T, C>,
    assignment_overlay: AssignmentLedgerOverlay<'brand, 'pp, 'al, T, C>,
    berth_overlay: BerthOccupancyOverlay<'bo, 'pb, T, Q>,
}

pub struct Explorer<'brand, 'bo, 'pp, 'pb, 'al, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    assignment_overlay: AssignmentLedgerOverlay<'brand, 'pp, 'al, T, C>,
    berth_overlay: BerthOccupancyOverlay<'bo, 'pb, T, Q>,
}

impl<'brand, 'bo, 'pp, 'pb, 'al, T, C, Q> Explorer<'brand, 'bo, 'pp, 'pb, 'al, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    fn new(builder: &PlanBuilder<'brand, 'bo, 'pp, 'pb, 'al, T, C, Q>) -> Self {
        Self {
            assignment_overlay: builder.assignment_overlay.clone(),
            berth_overlay: builder.berth_overlay.clone(),
        }
    }

    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = BrandedFixedRequestId<'brand>> + '_ {
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
    ) -> impl Iterator<Item = BrandedMovableRequestId<'brand>> + '_ {
        self.assignment_overlay.iter_movable_handles()
    }

    #[inline]
    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = BrandedMovableAssignment<'brand, 'pp, T, C>> + '_ {
        self.assignment_overlay.iter_movable_assignments()
    }

    #[inline]
    pub fn iter_unassigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMovableRequest<'brand, 'pp, T, C>> + '_ {
        self.assignment_overlay.iter_unassigned_requests()
    }

    #[inline]
    pub fn iter_assigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMovableRequest<'brand, 'pp, T, C>> + '_ {
        self.assignment_overlay.iter_assigned_requests()
    }

    #[inline]
    pub fn iter_assignments(&self) -> impl Iterator<Item = AnyAssignmentRef<'_, T, C>> + '_ {
        self.assignment_overlay.iter_assignments()
    }

    /// Slots are branded by the **berth** brand `'bo`.
    pub fn iter_slots_for_request(
        &self,
        request: &BrandedMovableRequest<'brand, 'pp, T, C>,
    ) -> impl Iterator<Item = FreeSlot<'bo, T>> + '_ {
        let time_search_window = request.feasible_time_window();
        let space_search_window = request.feasible_space_window();
        let processing_duration = request.processing_duration();
        let length = request.length();

        self.berth_overlay
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
        request: &BrandedMovableRequest<'brand, 'pp, T, C>,
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
                self.berth_overlay
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

impl<'brand, 'bo, 'pp, 'pb, 'al, T, C, Q> PlanBuilder<'brand, 'bo, 'pp, 'pb, 'al, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    fn new(
        problem: &'pp Problem<T, C>,
        assignment_overlay: AssignmentLedgerOverlay<'brand, 'pp, 'al, T, C>,
        berth_overlay: BerthOccupancyOverlay<'bo, 'pb, T, Q>,
    ) -> Self {
        Self {
            problem,
            assignment_overlay,
            berth_overlay,
        }
    }

    #[inline]
    pub fn problem(&self) -> &'pp Problem<T, C> {
        self.problem
    }

    #[inline]
    pub fn with_explorer<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&Explorer<'brand, 'bo, 'pp, 'pb, 'al, T, C, Q>) -> R,
    {
        let ex = Explorer::new(self);
        f(&ex)
    }

    pub fn propose_unassign(
        &mut self,
        assignment: &'brand BrandedMovableAssignment<'brand, 'pp, T, C>,
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

        Ok(free)
    }

    pub fn propose_assign(
        &mut self,
        req: &BrandedMovableRequest<'brand, 'pp, T, C>,
        slot: FreeSlot<'bo, T>,
    ) -> Result<BrandedMovableAssignment<'brand, 'pp, T, C>, ProposeError> {
        let a = AssignmentRef::new(req.request(), slot.space().start(), slot.time().start());
        let rect: SpaceTimeRectangle<T> = a.into();

        let ma = self.assignment_overlay.commit_assignment(
            req.request(),
            slot.time().start(),
            slot.space().start(),
        )?;
        self.berth_overlay.occupy(&rect)?;

        Ok(ma)
    }

    pub fn build(self) -> Plan<'pp, T, C> {
        let berth_commit = self.berth_overlay.into_commit();
        let ledger_commit = self.assignment_overlay.into_commit();
        Plan::new(berth_commit, ledger_commit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::berth::prelude::BooleanVecQuay;
    use dock_alloc_core::domain::{
        Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
    };
    use dock_alloc_model::{Movable, ProblemBuilder, Request, RequestId};
    use rayon::prelude::*;

    type Tm = i64;
    type Cm = i64;

    fn req_movable_ok(
        id: u64,
        len: usize,
        proc_t: i64,
        t0: i64,
        t1: i64,
        s0: usize,
        s1: usize,
    ) -> Request<Movable, Tm, Cm> {
        Request::<Movable, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimeDelta::new(proc_t),
            SpacePosition::new(s0),
            Cost::new(1),
            Cost::new(1),
            TimeInterval::new(TimePoint::new(t0), TimePoint::new(t1)),
            SpaceInterval::new(SpacePosition::new(s0), SpacePosition::new(s1)),
        )
        .expect("valid movable request")
    }

    #[test]
    fn collect_plans_in_parallel_with_rayon() {
        let n = 8usize;
        let quay_len = 200usize;

        let mut pb = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(quay_len));
        for i in 0..n {
            let base = i * 20;
            pb.add_movable_request(req_movable_ok(
                (i as u64) + 1,
                10,
                5,
                0,
                100,
                base,
                base + 20,
            ))
            .unwrap();
        }
        let problem = pb.build();

        let mut ledger = AssignmentLedger::from(&problem);
        let mut berth: BerthOccupancy<Tm, BooleanVecQuay> =
            BerthOccupancy::new(problem.quay_length());

        let mut ids: Vec<_> = problem.movables().keys().cloned().collect();
        ids.sort_by_key(|id| id.value());

        let plans = ids
            .par_iter()
            .map(|mid| {
                let alov = AssignmentLedgerOverlay::new(&ledger);
                let bov = BerthOccupancyOverlay::new(&berth);

                let mut b = PlanBuilder::new(&problem, alov, bov);
                let (req, slot) = b.with_explorer(|ex| {
                    let req = ex
                        .iter_unassigned_requests()
                        .find(|r| r.id() == *mid)
                        .expect("request visible in overlay");
                    let slot = ex
                        .iter_slots_for_request(&req)
                        .next()
                        .expect("at least one feasible slot");
                    (req, slot)
                });
                let _ = b.propose_assign(&req, slot).expect("stage assign");
                b.build()
            })
            .collect::<Vec<_>>();

        for p in &plans {
            assert_eq!(p.ledger_commit().operations().len(), 1);
        }
        for p in plans {
            ledger
                .apply(p.ledger_commit())
                .expect("apply ledger commit");
            berth.apply(p.berth_commit()).expect("apply berth commit");
        }
        assert_eq!(ledger.iter_movable_assignments().count(), ids.len());
    }
}
