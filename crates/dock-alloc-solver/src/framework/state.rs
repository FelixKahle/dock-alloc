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
    time::{TimeInterval, TimePoint},
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

#[derive(Clone, Debug)]
struct Item<T: SolverVariable> {
    req_id: RequestId,
    rect: SpaceTimeRectangle<T>,
    arrival_time: TimePoint<T>,
    feasible_space_window: SpaceInterval,
}

impl<T: SolverVariable> Item<T> {
    fn new(
        req_id: RequestId,
        rect: SpaceTimeRectangle<T>,
        arrival_time: TimePoint<T>,
        feasible_space_window: SpaceInterval,
    ) -> Self {
        Self {
            req_id,
            rect,
            arrival_time,
            feasible_space_window,
        }
    }
}

fn rect_for_assignment<K, T, C>(a: AssignmentRef<'_, K, T, C>) -> SpaceTimeRectangle<T>
where
    K: Kind,
    T: SolverVariable,
    C: SolverVariable,
{
    let t0 = a.start_time();
    let t1 = t0 + a.request().processing_duration();
    let s0 = a.start_position();
    let s1 = SpacePosition::new(s0.value() + a.request().length().value());
    SpaceTimeRectangle::new(SpaceInterval::new(s0, s1), TimeInterval::new(t0, t1))
}

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
        Self::validate_state(&SolverState {
            problem,
            ledger: ledger.clone(),
            berth: berth.clone(),
        })?;

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

    fn validate_state(state: &SolverState<'p, T, C, Q>) -> Result<(), FeasibleStateError<T>> {
        validate(state.problem, &state.ledger, &state.berth)
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

#[derive(Debug, PartialEq, Eq)]
pub enum FeasibleSolverStateApplyError<T: SolverVariable> {
    Quay(QuaySpaceIntervalOutOfBoundsError),
    Ledger(LedgerApplyValidationError<T>),
    MismatchedAmounts(MismatchedOperationsAmountsError),
}

impl<T: SolverVariable + Clone> Clone for FeasibleSolverStateApplyError<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Quay(arg0) => Self::Quay(arg0.clone()),
            Self::Ledger(arg0) => Self::Ledger(arg0.clone()),
            Self::MismatchedAmounts(arg0) => Self::MismatchedAmounts(arg0.clone()),
        }
    }
}

impl<T: SolverVariable + Display + Debug> std::fmt::Display for FeasibleSolverStateApplyError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FeasibleSolverStateApplyError::Quay(e) => write!(f, "Quay error: {}", e),
            FeasibleSolverStateApplyError::Ledger(e) => write!(f, "Ledger error: {}", e),
            FeasibleSolverStateApplyError::MismatchedAmounts(e) => write!(f, "{}", e),
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

        {
            let mut tmp_ledger = self.ledger.clone();
            tmp_ledger
                .apply_validated(plan.ledger_commit())
                .map_err(FeasibleSolverStateApplyError::Ledger)?;
        }

        self.ledger
            .apply_validated(plan.ledger_commit())
            .expect("Cannot recover from partial ledger apply. This should not happen if validation passed.");

        // The berth apply is assumed to be valid if the ledger apply was valid.
        // The berth only carries occupancy information, and does not a transactional
        // nature like the ledger.
        // Something is either free or occupied.
        self.berth.apply(plan.berth_commit())?;

        Ok(())
    }

    pub fn validate(&self) -> Result<(), FeasibleStateError<T>> {
        validate(self.problem, &self.ledger, &self.berth)
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

fn validate<'p, T, C, Q>(
    problem: &'p Problem<T, C>,
    ledger: &AssignmentLedger<'p, T, C>,
    berth: &BerthOccupancy<T, Q>,
) -> Result<(), FeasibleStateError<T>>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    let committed = ledger.committed();
    let mut missing: Vec<RequestId> = Vec::new();
    for mid in problem.movables().iter().map(|r| r.typed_id()) {
        if !committed.contains_key(&mid) {
            missing.push(RequestId::from(mid));
        }
    }
    if !missing.is_empty() {
        return Err(FeasibleStateError::UnassignedRequests(missing));
    }

    let quay_len = problem.quay_length();
    let mut items: Vec<Item<T>> = Vec::new();

    for fa in problem.iter_fixed_assignments() {
        let aref = AssignmentRef::new(fa.request(), fa.start_position(), fa.start_time());
        items.push(Item::new(
            fa.id(),
            rect_for_assignment(aref),
            fa.request().arrival_time(),
            fa.request().feasible_space_window(),
        ));
    }

    for ma in ledger.iter_movable_assignments() {
        let aref = AssignmentRef::new(ma.request(), ma.start_position(), ma.start_time());
        items.push(Item::new(
            ma.id(),
            rect_for_assignment(aref),
            ma.request().arrival_time(),
            ma.request().feasible_space_window(),
        ));
    }

    for it in &items {
        let (sint, tint) = it.rect.into_inner();

        if tint.start() < it.arrival_time {
            return Err(FeasibleStateError::AssignmentBeforeArrivalTime(
                AssignmentBeforeArrivalTimeError::new(it.req_id, it.arrival_time, tint.start()),
            ));
        }

        if !it.feasible_space_window.contains_interval(&sint) {
            return Err(FeasibleStateError::AssignmentOutsideSpaceWindow(
                AssignmentOutsideSpaceWindowError::new(it.req_id, it.feasible_space_window, sint),
            ));
        }

        let quay_bounds = berth.quay_space_interval();
        if !quay_bounds.contains_interval(&sint) {
            return Err(FeasibleStateError::AssignmentExceedsQuay(
                AssignmentExceedsQuayError::new(it.req_id, quay_len, sint),
            ));
        }

        match berth.is_occupied(&it.rect) {
            Ok(true) => {} // good
            Ok(false) => {
                return Err(FeasibleStateError::AssignmentOutsideSpaceWindow(
                    AssignmentOutsideSpaceWindowError::new(
                        it.req_id,
                        it.feasible_space_window,
                        sint,
                    ),
                ));
            }
            Err(_) => {
                return Err(FeasibleStateError::AssignmentExceedsQuay(
                    AssignmentExceedsQuayError::new(it.req_id, quay_len, sint),
                ));
            }
        }
    }

    let mut order: Vec<usize> = (0..items.len()).collect();
    order.sort_by_key(|&i| items[i].rect.time().start().value());

    let mut active: Vec<usize> = Vec::new();
    let sort_active_by_end = |v: &mut Vec<usize>| {
        v.sort_by(|&i, &j| {
            items[i]
                .rect
                .time()
                .end()
                .value()
                .cmp(&items[j].rect.time().end().value())
        });
    };

    for &i in &order {
        let t_start_i = items[i].rect.time().start();

        sort_active_by_end(&mut active);
        let mut keep_from = 0;
        for (k, &idx) in active.iter().enumerate() {
            if items[idx].rect.time().end() > t_start_i {
                keep_from = k;
                break;
            } else {
                keep_from = k + 1;
            }
        }
        if keep_from > 0 {
            active.drain(0..keep_from);
        }

        for &j in &active {
            if let Some(inter) = items[i].rect.intersection(&items[j].rect) {
                let (ra, rb) = if items[i].req_id.value() <= items[j].req_id.value() {
                    (items[i].req_id, items[j].req_id)
                } else {
                    (items[j].req_id, items[i].req_id)
                };
                return Err(FeasibleStateError::Overlap(SolverStateOverlapError::new(
                    ra, rb, inter,
                )));
            }
        }

        active.push(i);
    }

    Ok(())
}

#[cfg(test)]
mod ledger_commit_tests {
    use crate::registry::commit::LedgerOverlayCommit;
    use crate::registry::operations::Operation as LedgerOp; // build ops as needed
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
