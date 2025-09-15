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
        quay::{QuayRead, QuaySpaceIntervalOutOfBoundsError, QuayWrite},
    },
    domain::SpaceTimeRectangle,
    framework::planning::Plan,
    registry::ledger::{AssignmentLedger, LedgerApplyValidationError, LedgerError},
};
use dock_alloc_core::{
    SolverVariable,
    space::{SpaceInterval, SpacePosition},
    time::TimeInterval,
};
use dock_alloc_model::prelude::*;
use std::fmt::{Debug, Display};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverStateApplyError {
    Quay(QuaySpaceIntervalOutOfBoundsError),
    LedgerError(LedgerError),
}

impl From<QuaySpaceIntervalOutOfBoundsError> for SolverStateApplyError {
    fn from(value: QuaySpaceIntervalOutOfBoundsError) -> Self {
        SolverStateApplyError::Quay(value)
    }
}

impl From<LedgerError> for SolverStateApplyError {
    fn from(value: LedgerError) -> Self {
        SolverStateApplyError::LedgerError(value)
    }
}

impl std::fmt::Display for SolverStateApplyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SolverStateApplyError::Quay(e) => write!(f, "Quay error: {}", e),
            SolverStateApplyError::LedgerError(e) => write!(f, "Ledger error: {}", e),
        }
    }
}

impl std::error::Error for SolverStateApplyError {}

#[derive(Debug, Clone, PartialEq)]
pub struct SolverState<'p, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    problem: &'p Problem<T, C>,
    ledger: AssignmentLedger<'p, T, C>,
    berth: BerthOccupancy<T, Q>,
}

impl<'p, T, C, Q> SolverState<'p, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    #[inline]
    pub fn new(
        problem: &'p Problem<T, C>,
        ledger: AssignmentLedger<'p, T, C>,
        berth: BerthOccupancy<T, Q>,
    ) -> Self {
        Self {
            problem,
            ledger,
            berth,
        }
    }

    #[inline]
    pub fn ledger(&self) -> &AssignmentLedger<'p, T, C> {
        &self.ledger
    }

    #[inline]
    pub fn berth(&self) -> &BerthOccupancy<T, Q> {
        &self.berth
    }

    #[inline]
    pub fn problem(&self) -> &'p Problem<T, C> {
        self.problem
    }
}

impl<'p, T, C, Q> SolverState<'p, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead + QuayWrite,
{
    pub fn apply_plan<'a>(
        &mut self,
        plan: &'a Plan<'p, T, C>,
    ) -> Result<(), SolverStateApplyError> {
        self.ledger.apply(plan.ledger_commit())?;
        self.berth.apply(plan.berth_commit())?;
        Ok(())
    }
}

impl<'p, T, C, Q> TryFrom<&'p Problem<T, C>> for SolverState<'p, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead + QuayWrite,
{
    type Error = QuaySpaceIntervalOutOfBoundsError;

    fn try_from(problem: &'p Problem<T, C>) -> Result<Self, Self::Error> {
        let ledger = AssignmentLedger::from(problem);
        let berth = BerthOccupancy::try_from(problem)?;
        Ok(Self::new(problem, ledger, berth))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FeasibleSolverState<'p, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    problem: &'p Problem<T, C>,
    ledger: AssignmentLedger<'p, T, C>,
    berth: BerthOccupancy<T, Q>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolverStateOverlapError<T: SolverVariable> {
    a: RequestId,
    b: RequestId,
    intersection: SpaceTimeRectangle<T>,
}

impl<T: SolverVariable> SolverStateOverlapError<T> {
    #[inline]
    pub fn new(a: RequestId, b: RequestId, intersection: SpaceTimeRectangle<T>) -> Self {
        Self { a, b, intersection }
    }

    #[inline]
    pub fn a(&self) -> RequestId {
        self.a
    }

    #[inline]
    pub fn b(&self) -> RequestId {
        self.b
    }

    #[inline]
    pub fn intersection(&self) -> &SpaceTimeRectangle<T> {
        &self.intersection
    }
}

impl<T: SolverVariable + Display> std::fmt::Display for SolverStateOverlapError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignments for requests {} and {} overlap in space-time at {}",
            self.a, self.b, self.intersection
        )
    }
}

impl<T: SolverVariable + Display + Debug> std::error::Error for SolverStateOverlapError<T> {}

impl<T> From<SolutionValidationError<T>> for FeasibleStateError<T>
where
    T: SolverVariable + std::fmt::Display + std::fmt::Debug,
{
    fn from(e: SolutionValidationError<T>) -> Self {
        match e {
            SolutionValidationError::AssignmentBeforeArrivalTime(inner) => {
                FeasibleStateError::AssignmentBeforeArrivalTime(inner)
            }
            SolutionValidationError::Overlap(inner) => {
                let a = inner.request_a();
                let b = inner.request_b();
                let time_a: TimeInterval<T> = inner.time_a();
                let time_b: TimeInterval<T> = inner.time_b();
                let space_a: SpaceInterval = inner.space_a();
                let space_b: SpaceInterval = inner.space_b();
                let ti = time_a
                    .intersection(&time_b)
                    .expect("model reported overlap but time intersection is None");
                let si = space_a
                    .intersection(&space_b)
                    .expect("model reported overlap but space intersection is None");
                let rect = SpaceTimeRectangle::new(si, ti);
                FeasibleStateError::Overlap(SolverStateOverlapError::new(a, b, rect))
            }
            SolutionValidationError::AssignmentOutsideSpaceWindow(
                assignment_outside_space_window_error,
            ) => FeasibleStateError::AssignmentOutsideSpaceWindow(
                assignment_outside_space_window_error,
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FeasibleStateError<T: SolverVariable> {
    AssignmentBeforeArrivalTime(AssignmentBeforeArrivalTimeError<T>),
    AssignmentOutsideSpaceWindow(AssignmentOutsideSpaceWindowError),
    AssignmentExceedsQuay(AssignmentExceedsQuayError),
    Overlap(SolverStateOverlapError<T>),
    UnassignedRequests(Vec<RequestId>),
}

impl<T: SolverVariable> From<AssignmentBeforeArrivalTimeError<T>> for FeasibleStateError<T> {
    fn from(value: AssignmentBeforeArrivalTimeError<T>) -> Self {
        FeasibleStateError::AssignmentBeforeArrivalTime(value)
    }
}

impl<T: SolverVariable> From<AssignmentOutsideSpaceWindowError> for FeasibleStateError<T> {
    fn from(value: AssignmentOutsideSpaceWindowError) -> Self {
        FeasibleStateError::AssignmentOutsideSpaceWindow(value)
    }
}

impl<T: SolverVariable> From<AssignmentExceedsQuayError> for FeasibleStateError<T> {
    fn from(value: AssignmentExceedsQuayError) -> Self {
        FeasibleStateError::AssignmentExceedsQuay(value)
    }
}

impl<T: SolverVariable> From<SolverStateOverlapError<T>> for FeasibleStateError<T> {
    fn from(value: SolverStateOverlapError<T>) -> Self {
        FeasibleStateError::Overlap(value)
    }
}

impl<T: SolverVariable + Display + Debug> std::fmt::Display for FeasibleStateError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FeasibleStateError::AssignmentBeforeArrivalTime(e) => {
                write!(f, "{}", e)
            }
            FeasibleStateError::AssignmentOutsideSpaceWindow(e) => {
                write!(f, "{}", e)
            }
            FeasibleStateError::AssignmentExceedsQuay(e) => {
                write!(f, "{}", e)
            }
            FeasibleStateError::Overlap(e) => write!(f, "{}", e),
            FeasibleStateError::UnassignedRequests(reqs) => {
                let reqs_str = reqs
                    .iter()
                    .map(|r| r.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "The following requests are unassigned: {}", reqs_str)
            }
        }
    }
}

impl<T: SolverVariable + Display + Debug> std::error::Error for FeasibleStateError<T> {}

impl<'p, T, C, Q> FeasibleSolverState<'p, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    #[inline]
    pub fn new(
        problem: &'p Problem<T, C>,
        ledger: AssignmentLedger<'p, T, C>,
        berth: BerthOccupancy<T, Q>,
    ) -> Result<Self, FeasibleStateError<T>> {
        validate_ledger_solution(problem, &ledger)?;

        Ok(Self {
            problem,
            ledger,
            berth,
        })
    }

    #[inline]
    pub fn problem(&self) -> &'p Problem<T, C> {
        self.problem
    }

    #[inline]
    pub fn ledger(&self) -> &AssignmentLedger<'p, T, C> {
        &self.ledger
    }

    #[inline]
    pub fn berth(&self) -> &BerthOccupancy<T, Q> {
        &self.berth
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MismatchedOperationsAmountsError {
    unassigned_amount: usize,
    assigned_amount: usize,
}

impl MismatchedOperationsAmountsError {
    #[inline]
    pub fn new(unassigned_amount: usize, assigned_amount: usize) -> Self {
        Self {
            unassigned_amount,
            assigned_amount,
        }
    }

    #[inline]
    pub fn unassigned_amount(&self) -> usize {
        self.unassigned_amount
    }

    #[inline]
    pub fn assigned_amount(&self) -> usize {
        self.assigned_amount
    }
}

impl std::fmt::Display for MismatchedOperationsAmountsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Mismatched amounts: unassigned amount is {}, but assigned amount is {}",
            self.unassigned_amount, self.assigned_amount
        )
    }
}

impl std::error::Error for MismatchedOperationsAmountsError {}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FeasibleSolverStateApplyError<T: SolverVariable> {
    Quay(QuaySpaceIntervalOutOfBoundsError),
    Ledger(LedgerApplyValidationError<T>),
    MismatchedAmounts(MismatchedOperationsAmountsError),
    Infeasible(FeasibleStateError<T>),
}

impl<T: SolverVariable + Display + Debug> std::fmt::Display for FeasibleSolverStateApplyError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FeasibleSolverStateApplyError::Quay(e) => write!(f, "Quay error: {e}"),
            FeasibleSolverStateApplyError::Ledger(e) => write!(f, "Ledger error: {e}"),
            FeasibleSolverStateApplyError::MismatchedAmounts(e) => write!(f, "{e}"),
            FeasibleSolverStateApplyError::Infeasible(e) => write!(f, "{e}"),
        }
    }
}

impl<T: SolverVariable> From<QuaySpaceIntervalOutOfBoundsError>
    for FeasibleSolverStateApplyError<T>
{
    fn from(value: QuaySpaceIntervalOutOfBoundsError) -> Self {
        FeasibleSolverStateApplyError::Quay(value)
    }
}

impl<T: SolverVariable> From<LedgerApplyValidationError<T>> for FeasibleSolverStateApplyError<T> {
    fn from(value: LedgerApplyValidationError<T>) -> Self {
        FeasibleSolverStateApplyError::Ledger(value)
    }
}

impl<T: SolverVariable + Display + Debug> std::error::Error for FeasibleSolverStateApplyError<T> {}

impl<'p, T, C, Q> FeasibleSolverState<'p, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead + QuayWrite,
{
    pub fn apply_plan_validated(
        &mut self,
        plan: &Plan<'p, T, C>,
    ) -> Result<(), FeasibleSolverStateApplyError<T>> {
        let a = plan.ledger_commit().amount_assigned();
        let u = plan.ledger_commit().amount_unassigned();
        if a != u {
            return Err(FeasibleSolverStateApplyError::MismatchedAmounts(
                MismatchedOperationsAmountsError::new(u, a),
            ));
        }

        let mut tmp_ledger = self.ledger.clone();
        tmp_ledger
            .apply_validated(plan.ledger_commit())
            .map_err(FeasibleSolverStateApplyError::Ledger)?;

        // single call does 1–5 (no berth):
        validate_ledger_solution(self.problem, &tmp_ledger)
            .map_err(FeasibleSolverStateApplyError::Infeasible)?;

        // commit for real
        self.ledger
            .apply_validated(plan.ledger_commit())
            .expect("ledger validation already done, so this should not fail. It is unrecoverable if it does.");
        self.berth
            .apply(plan.berth_commit())
            .map_err(FeasibleSolverStateApplyError::Quay)?;

        Ok(())
    }
}

impl<'p, T, C, Q> TryFrom<FeasibleSolverState<'p, T, C, Q>> for SolverState<'p, T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    type Error = FeasibleStateError<T>;

    fn try_from(value: FeasibleSolverState<'p, T, C, Q>) -> Result<Self, Self::Error> {
        Ok(Self::new(value.problem, value.ledger, value.berth))
    }
}

impl<'p, T, C, Q> From<FeasibleSolverState<'p, T, C, Q>> for SolutionRef<'p, T, C>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead,
{
    fn from(value: FeasibleSolverState<'p, T, C, Q>) -> Self {
        value.ledger.into()
    }
}

pub trait ConstructiveSolver<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    type SolveError;

    fn build_state<'p>(
        &mut self,
        problem: &'p Problem<T, C>,
    ) -> Result<FeasibleSolverState<'p, T, C, Q>, Self::SolveError>;
}

pub trait Solver<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead + QuayWrite,
{
    type SolveError;

    fn solve<'p>(
        &mut self,
        problem: &'p Problem<T, C>,
    ) -> Result<SolutionRef<'p, T, C>, Self::SolveError>;
}

fn validate_ledger_solution<'p, T, C>(
    problem: &'p Problem<T, C>,
    ledger: &AssignmentLedger<'p, T, C>,
) -> Result<(), FeasibleStateError<T>>
where
    T: SolverVariable,
    C: SolverVariable,
{
    {
        let committed = ledger.committed();
        let mut missing = Vec::new();
        for r in problem.movables().iter() {
            if !committed.contains_key(&r.typed_id()) {
                missing.push(r.id());
            }
        }
        if !missing.is_empty() {
            return Err(FeasibleStateError::UnassignedRequests(missing));
        }
    }

    let quay_len = problem.quay_length();
    let quay_bounds = problem.quay_interval();

    #[derive(Clone)]
    struct Rect<Tm: SolverVariable> {
        id: RequestId,
        t: TimeInterval<Tm>,
        s: SpaceInterval,
    }
    let mut rects: Vec<Rect<T>> = Vec::new();

    for fa in problem.iter_fixed_assignments() {
        let rq = fa.request();

        let t0 = fa.start_time();
        let t1 = t0 + rq.processing_duration();
        let s0 = fa.start_position();
        let s1 = SpacePosition::new(s0.value() + rq.length().value());
        let s_iv = SpaceInterval::new(s0, s1);

        if t0 < rq.arrival_time() {
            return Err(FeasibleStateError::AssignmentBeforeArrivalTime(
                AssignmentBeforeArrivalTimeError::new(rq.id(), rq.arrival_time(), t0),
            ));
        }

        let windows = rq.feasible_space_windows();
        if !windows.iter().any(|w| w.contains_interval(&s_iv)) {
            return Err(FeasibleStateError::AssignmentOutsideSpaceWindow(
                AssignmentOutsideSpaceWindowError::new(rq.id(), windows.to_vec(), s_iv),
            ));
        }

        if !quay_bounds.contains_interval(&s_iv) {
            return Err(FeasibleStateError::AssignmentExceedsQuay(
                AssignmentExceedsQuayError::new(rq.id(), quay_len, s_iv),
            ));
        }

        rects.push(Rect {
            id: rq.id(),
            t: TimeInterval::new(t0, t1),
            s: s_iv,
        });
    }

    for ma in ledger.iter_movable_assignments() {
        let rq = ma.request();

        let t0 = ma.start_time();
        let t1 = t0 + rq.processing_duration();
        let s0 = ma.start_position();
        let s1 = SpacePosition::new(s0.value() + rq.length().value());
        let s_iv = SpaceInterval::new(s0, s1);

        if t0 < rq.arrival_time() {
            return Err(FeasibleStateError::AssignmentBeforeArrivalTime(
                AssignmentBeforeArrivalTimeError::new(rq.id(), rq.arrival_time(), t0),
            ));
        }

        let windows = rq.feasible_space_windows();
        if !windows.iter().any(|w| w.contains_interval(&s_iv)) {
            return Err(FeasibleStateError::AssignmentOutsideSpaceWindow(
                AssignmentOutsideSpaceWindowError::new(rq.id(), windows.to_vec(), s_iv),
            ));
        }

        if !quay_bounds.contains_interval(&s_iv) {
            return Err(FeasibleStateError::AssignmentExceedsQuay(
                AssignmentExceedsQuayError::new(rq.id(), quay_len, s_iv),
            ));
        }

        rects.push(Rect {
            id: rq.id(),
            t: TimeInterval::new(t0, t1),
            s: s_iv,
        });
    }

    rects.sort_by_key(|r| r.t.start().value());
    let mut active: Vec<Rect<T>> = Vec::new();

    for cur in rects {
        active.retain(|x| x.t.end() > cur.t.start());

        for other in &active {
            if other.t.intersects(&cur.t) && other.s.intersects(&cur.s) {
                let ti = other.t.intersection(&cur.t).unwrap();
                let si = other.s.intersection(&cur.s).unwrap();
                let (a, b) = if other.id.value() <= cur.id.value() {
                    (other.id, cur.id)
                } else {
                    (cur.id, other.id)
                };
                return Err(FeasibleStateError::Overlap(SolverStateOverlapError::new(
                    a,
                    b,
                    SpaceTimeRectangle::new(si, ti),
                )));
            }
        }

        active.push(cur);
    }

    Ok(())
}

#[cfg(test)]
mod ledger_commit_tests {
    use crate::registry::commit::LedgerOverlayCommit;
    use crate::registry::operations::Operation as LedgerOp;
    type T = i64;
    type C = i64;

    #[test]
    fn ledger_commit_amounts_round_trip() {
        let ops: Vec<LedgerOp<'static, T, C>> = Vec::new(); // or real ops if useful
        let lc = LedgerOverlayCommit::new(ops, 3, 2);
        assert_eq!(lc.amount_unassigned(), 3);
        assert_eq!(lc.amount_assigned(), 2);
        assert!(lc.operations().is_empty());
    }
}

#[cfg(test)]
mod validate_tests {
    use super::*;
    use dock_alloc_core::{
        cost::Cost,
        space::{SpaceInterval, SpaceLength, SpacePosition},
        time::{TimeDelta, TimePoint},
    };

    type Tm = i64;
    type Cm = i64;

    fn req_movable(
        id: u64,
        len: usize,
        arrival: i64,
        proc_t: i64,
        sw_start: usize,
        sw_end: usize,
    ) -> Request<Movable, Tm, Cm> {
        Request::<Movable, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimePoint::new(arrival),
            TimeDelta::new(proc_t),
            SpacePosition::new(sw_start), // preferred start (not validated here)
            Cost::new(1),
            Cost::new(1),
            vec![SpaceInterval::new(
                SpacePosition::new(sw_start),
                SpacePosition::new(sw_end),
            )],
        )
        .expect("valid movable request")
    }

    #[test]
    fn validate_ok_non_overlapping() {
        // quay: [0, 100)
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        // full-space windows
        let r1 = req_movable(1, 10, 0, 5, 0, 100);
        let r2 = req_movable(2, 10, 0, 5, 0, 100);
        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        // r1 at t=0, s=[0,10)
        let req1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        ledger
            .commit_assignment(req1, TimePoint::new(0), SpacePosition::new(0))
            .unwrap();

        // r2 at t=0, s=[20,30) — same time, disjoint space ⇒ OK
        let req2 = problem
            .get_movable(MovableRequestId::from(r2.id()))
            .unwrap();
        ledger
            .commit_assignment(req2, TimePoint::new(0), SpacePosition::new(20))
            .unwrap();

        assert!(validate_ledger_solution(&problem, &ledger).is_ok());
    }

    #[test]
    fn validate_unassigned_err() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(50));
        let r1 = req_movable(1, 10, 0, 5, 0, 50);
        let r2 = req_movable(2, 10, 0, 5, 0, 50);
        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        let req1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        ledger
            .commit_assignment(req1, TimePoint::new(0), SpacePosition::new(0))
            .unwrap();
        // r2 left unassigned

        let err = validate_ledger_solution(&problem, &ledger).unwrap_err();
        match err {
            FeasibleStateError::UnassignedRequests(v) => {
                assert_eq!(v, vec![r2.id()]);
            }
            _ => panic!("expected UnassignedRequests, got {err}"),
        }
    }

    #[test]
    fn validate_exceeds_quay_err() {
        // quay length 30
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(30));
        let r1 = req_movable(1, 15, 0, 5, 0, 30);
        b.add_movable_request(r1.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        // place starting at s=20 ⇒ [20,35) spills beyond quay=30
        let req1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        ledger
            .commit_assignment(req1, TimePoint::new(0), SpacePosition::new(20))
            .unwrap();

        let err = validate_ledger_solution(&problem, &ledger).unwrap_err();
        matches!(err, FeasibleStateError::AssignmentExceedsQuay(_));
    }

    #[test]
    fn validate_before_arrival_err() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        // arrival at t=10
        let r1 = req_movable(1, 10, 10, 5, 0, 100);
        b.add_movable_request(r1.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        // start earlier than arrival (t=5)
        let req1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        ledger
            .commit_assignment(req1, TimePoint::new(5), SpacePosition::new(0))
            .unwrap();

        let err = validate_ledger_solution(&problem, &ledger).unwrap_err();
        matches!(err, FeasibleStateError::AssignmentBeforeArrivalTime(_));
    }

    #[test]
    fn validate_outside_space_window_movable_err() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        // feasible window [50,80)
        let r1 = req_movable(1, 10, 0, 5, 50, 80);
        b.add_movable_request(r1.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        // assign at s=[0,10) ⇒ outside feasible window
        let req1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        ledger
            .commit_assignment(req1, TimePoint::new(0), SpacePosition::new(0))
            .unwrap();

        let err = validate_ledger_solution(&problem, &ledger).unwrap_err();
        matches!(err, FeasibleStateError::AssignmentOutsideSpaceWindow(_));
    }

    #[test]
    fn validate_overlap_err() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable(1, 10, 0, 5, 0, 100);
        let r2 = req_movable(2, 10, 0, 5, 0, 100);
        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        // both at t=0..5; spaces [0,10) and [5,15) ⇒ overlap
        let m1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let m2 = problem
            .get_movable(MovableRequestId::from(r2.id()))
            .unwrap();
        ledger
            .commit_assignment(m1, TimePoint::new(0), SpacePosition::new(0))
            .unwrap();
        ledger
            .commit_assignment(m2, TimePoint::new(0), SpacePosition::new(5))
            .unwrap();

        let err = validate_ledger_solution(&problem, &ledger).unwrap_err();
        matches!(err, FeasibleStateError::Overlap(_));
    }

    #[test]
    fn validate_touch_in_time_no_overlap_ok() {
        // Touching in time (end==start) is allowed for half-open intervals
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable(1, 10, 0, 5, 0, 100);
        let r2 = req_movable(2, 10, 0, 5, 0, 100);
        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        let m1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let m2 = problem
            .get_movable(MovableRequestId::from(r2.id()))
            .unwrap();
        ledger
            .commit_assignment(m1, TimePoint::new(0), SpacePosition::new(0))
            .unwrap();
        // second starts exactly when first ends (t=5), same space ⇒ OK
        ledger
            .commit_assignment(m2, TimePoint::new(5), SpacePosition::new(0))
            .unwrap();

        assert!(validate_ledger_solution(&problem, &ledger).is_ok());
    }

    // Add inside `#[cfg(test)] mod validate_tests { ... }`

    fn req_movable_multi(
        id: u64,
        len: usize,
        arrival: i64,
        proc_t: i64,
        windows: &[(usize, usize)],
    ) -> Request<Movable, Tm, Cm> {
        let sw: Vec<SpaceInterval> = windows
            .iter()
            .map(|&(lo, hi)| SpaceInterval::new(SpacePosition::new(lo), SpacePosition::new(hi)))
            .collect();
        Request::<Movable, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimePoint::new(arrival),
            TimeDelta::new(proc_t),
            SpacePosition::new(windows[0].0), // target not validated here
            Cost::new(1),
            Cost::new(1),
            sw,
        )
        .expect("valid movable request")
    }

    fn req_fixed_multi(
        id: u64,
        len: usize,
        arrival: i64,
        proc_t: i64,
        windows: &[(usize, usize)],
    ) -> Request<Fixed, Tm, Cm> {
        let sw: Vec<SpaceInterval> = windows
            .iter()
            .map(|&(lo, hi)| SpaceInterval::new(SpacePosition::new(lo), SpacePosition::new(hi)))
            .collect();
        Request::<Fixed, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimePoint::new(arrival),
            TimeDelta::new(proc_t),
            SpacePosition::new(windows[0].0), // target placeholder
            Cost::new(1),
            Cost::new(1),
            sw,
        )
        .expect("valid fixed request")
    }

    #[test]
    fn validate_ok_movable_assigns_in_first_of_two_windows() {
        // windows: [0,10) and [30,50), len=5 -> place in first
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(60));
        let r = req_movable_multi(1, 5, 0, 4, &[(0, 10), (30, 50)]);
        b.add_movable_request(r.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        let req = problem.get_movable(MovableRequestId::from(r.id())).unwrap();
        // Assign at s=[4,9) inside first window
        ledger
            .commit_assignment(req, TimePoint::new(0), SpacePosition::new(4))
            .unwrap();

        assert!(validate_ledger_solution(&problem, &ledger).is_ok());
    }

    #[test]
    fn validate_ok_movable_assigns_in_second_of_two_windows() {
        // same two windows, assign in second
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(60));
        let r = req_movable_multi(1, 5, 0, 4, &[(0, 10), (30, 50)]);
        b.add_movable_request(r.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        let req = problem.get_movable(MovableRequestId::from(r.id())).unwrap();
        // Assign at s=[44,49) inside [30,50)
        ledger
            .commit_assignment(req, TimePoint::new(0), SpacePosition::new(44))
            .unwrap();

        assert!(validate_ledger_solution(&problem, &ledger).is_ok());
    }

    #[test]
    fn validate_err_movable_spanning_gap_between_windows() {
        // Each window individually long enough (20 and 20). Request len=15.
        // Place at s=10 -> band [10,25) exceeds first window end (20) => invalid.
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(80));
        let r = req_movable_multi(1, 15, 0, 3, &[(0, 20), (30, 50)]);
        b.add_movable_request(r.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        let req = problem.get_movable(MovableRequestId::from(r.id())).unwrap();

        // This band crosses out of the first window; not contained in any single window.
        ledger
            .commit_assignment(req, TimePoint::new(0), SpacePosition::new(10))
            .unwrap();

        let err = validate_ledger_solution(&problem, &ledger).unwrap_err();
        matches!(err, FeasibleStateError::AssignmentOutsideSpaceWindow(_));
    }

    #[test]
    fn validate_ok_two_movables_same_time_different_windows_no_overlap() {
        // r1 allowed only in [0,10), r2 only in [30,50). Both start at t=0, no space overlap.
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(60));
        let r1 = req_movable_multi(1, 8, 0, 5, &[(0, 10)]);
        let r2 = req_movable_multi(2, 8, 0, 5, &[(30, 50)]);
        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);
        let m1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let m2 = problem
            .get_movable(MovableRequestId::from(r2.id()))
            .unwrap();

        ledger
            .commit_assignment(m1, TimePoint::new(0), SpacePosition::new(2))
            .unwrap(); // [2,10)
        ledger
            .commit_assignment(m2, TimePoint::new(0), SpacePosition::new(40))
            .unwrap(); // [40,48)

        assert!(validate_ledger_solution(&problem, &ledger).is_ok());
    }

    #[test]
    fn validate_ok_boundary_touch_at_window_end() {
        // window [20,30), len=5 -> start at 25 gives [25,30) touching end (OK: half-open)
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(60));
        let r = req_movable_multi(1, 5, 0, 2, &[(20, 30)]);
        b.add_movable_request(r.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        let req = problem.get_movable(MovableRequestId::from(r.id())).unwrap();
        ledger
            .commit_assignment(req, TimePoint::new(0), SpacePosition::new(25))
            .unwrap();

        assert!(validate_ledger_solution(&problem, &ledger).is_ok());
    }

    #[test]
    fn validate_err_boundary_past_window_end() {
        // window [20,30), len=5 -> start at 26 => [26,31) exceeds window (must fail)
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(60));
        let r = req_movable_multi(1, 5, 0, 2, &[(20, 30)]);
        b.add_movable_request(r.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        let req = problem.get_movable(MovableRequestId::from(r.id())).unwrap();
        ledger
            .commit_assignment(req, TimePoint::new(0), SpacePosition::new(26))
            .unwrap();

        let err = validate_ledger_solution(&problem, &ledger).unwrap_err();
        matches!(err, FeasibleStateError::AssignmentOutsideSpaceWindow(_));
    }

    #[test]
    fn validate_ok_fixed_in_one_of_many_windows() {
        // fixed request with three windows; preassigned in the third is valid
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(80));
        let rf = req_fixed_multi(99, 6, 0, 4, &[(0, 10), (20, 30), (50, 70)]);
        let a =
            Assignment::<Fixed, _, _>::new(rf.clone(), SpacePosition::new(62), TimePoint::new(0)); // [62,68) ⊂ [50,70)
        b.add_preassigned(a).unwrap();

        // also add one movable to satisfy "missing assignment" checks later when used standalone
        let r = req_movable_multi(1, 6, 0, 4, &[(0, 10), (50, 70)]);
        b.add_movable_request(r.clone()).unwrap();

        let problem = b.build();
        // Commit the movable so validation doesn't fail for unassigned movables
        let mut ledger = AssignmentLedger::from(&problem);
        let m = problem.get_movable(MovableRequestId::from(r.id())).unwrap();
        ledger
            .commit_assignment(m, TimePoint::new(0), SpacePosition::new(0))
            .unwrap();

        assert!(validate_ledger_solution(&problem, &ledger).is_ok());
    }
}
