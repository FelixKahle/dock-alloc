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
        prelude::BerthOccupancy,
        quay::{QuayRead, QuaySpaceIntervalOutOfBoundsError, QuayWrite},
    },
    domain::SpaceTimeRectangle,
    planning::Plan,
    registry::ledger::{AssignmentLedger, LedgerError},
};
use dock_alloc_core::domain::{SpaceInterval, SpacePosition, TimeInterval};
use dock_alloc_model::{
    AssignmentExceedsQuayError, AssignmentOutsideSpaceWindowError,
    AssignmentOutsideTimeWindowError, AssignmentRef, Problem, RequestId, SolutionRef,
};
use num_traits::{PrimInt, Signed, Zero};
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

pub struct SolverState<'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    problem: &'p Problem<T, C>,
    ledger: AssignmentLedger<'p, T, C>,
    berth: BerthOccupancy<T, Q>,
}

impl<'p, T, C, Q> SolverState<'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
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

    pub fn ledger(&self) -> &AssignmentLedger<'p, T, C> {
        &self.ledger
    }

    pub fn berth(&self) -> &BerthOccupancy<T, Q> {
        &self.berth
    }

    pub fn problem(&self) -> &'p Problem<T, C> {
        self.problem
    }
}

impl<'p, T, C, Q> SolverState<'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
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
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead + QuayWrite,
{
    type Error = QuaySpaceIntervalOutOfBoundsError;

    fn try_from(problem: &'p Problem<T, C>) -> Result<Self, Self::Error> {
        let ledger = AssignmentLedger::from(problem);
        let berth = BerthOccupancy::try_from(problem)?;
        Ok(Self::new(problem, ledger, berth))
    }
}

pub struct FeasibleSolverState<'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    problem: &'p Problem<T, C>,
    ledger: AssignmentLedger<'p, T, C>,
    berth: BerthOccupancy<T, Q>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolverStateOverlapError<T: PrimInt + Signed> {
    a: RequestId,
    b: RequestId,
    intersection: SpaceTimeRectangle<T>,
}

impl<T: PrimInt + Signed> SolverStateOverlapError<T> {
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

impl<T: PrimInt + Signed + Display> std::fmt::Display for SolverStateOverlapError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignments for requests {} and {} overlap in space-time at {}",
            self.a, self.b, self.intersection
        )
    }
}

impl<T: PrimInt + Signed + Display + Debug> std::error::Error for SolverStateOverlapError<T> {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FeasibleStateError<T: PrimInt + Signed> {
    AssignmentOutsideTimeWindow(AssignmentOutsideTimeWindowError<T>),
    AssignmentOutsideSpaceWindow(AssignmentOutsideSpaceWindowError),
    AssignmentExceedsQuay(AssignmentExceedsQuayError),
    Overlap(SolverStateOverlapError<T>),
    UnassignedRequests(Vec<RequestId>),
}

impl<T: PrimInt + Signed> From<AssignmentOutsideTimeWindowError<T>> for FeasibleStateError<T> {
    fn from(value: AssignmentOutsideTimeWindowError<T>) -> Self {
        FeasibleStateError::AssignmentOutsideTimeWindow(value)
    }
}

impl<T: PrimInt + Signed> From<AssignmentOutsideSpaceWindowError> for FeasibleStateError<T> {
    fn from(value: AssignmentOutsideSpaceWindowError) -> Self {
        FeasibleStateError::AssignmentOutsideSpaceWindow(value)
    }
}

impl<T: PrimInt + Signed> From<AssignmentExceedsQuayError> for FeasibleStateError<T> {
    fn from(value: AssignmentExceedsQuayError) -> Self {
        FeasibleStateError::AssignmentExceedsQuay(value)
    }
}

impl<T: PrimInt + Signed> From<SolverStateOverlapError<T>> for FeasibleStateError<T> {
    fn from(value: SolverStateOverlapError<T>) -> Self {
        FeasibleStateError::Overlap(value)
    }
}

impl<T: PrimInt + Signed + Display + Debug> std::fmt::Display for FeasibleStateError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FeasibleStateError::AssignmentOutsideTimeWindow(e) => {
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

impl<T: PrimInt + Signed + Display + Debug> std::error::Error for FeasibleStateError<T> {}

#[derive(Clone, Debug)]
struct Item<T: PrimInt + Signed> {
    req_id: RequestId,
    rect: SpaceTimeRectangle<T>,
    feasible_time_window: TimeInterval<T>,
    feasible_space_window: SpaceInterval,
}

impl<T: PrimInt + Signed> Item<T> {
    fn new(
        req_id: RequestId,
        rect: SpaceTimeRectangle<T>,
        feasible_time_window: TimeInterval<T>,
        feasible_space_window: SpaceInterval,
    ) -> Self {
        Self {
            req_id,
            rect,
            feasible_time_window,
            feasible_space_window,
        }
    }
}

fn rect_for_assignment<K, T, C>(a: AssignmentRef<'_, K, T, C>) -> SpaceTimeRectangle<T>
where
    K: dock_alloc_model::Kind,
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    let t0 = a.start_time();
    let t1 = t0 + a.request().processing_duration();
    let s0 = a.start_position();
    let s1 = SpacePosition::new(s0.value() + a.request().length().value());
    SpaceTimeRectangle::new(SpaceInterval::new(s0, s1), TimeInterval::new(t0, t1))
}

impl<'p, T, C, Q> FeasibleSolverState<'p, T, C, Q>
where
    T: PrimInt + Signed + Zero,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    #[inline]
    pub fn new(
        problem: &'p Problem<T, C>,
        ledger: AssignmentLedger<'p, T, C>,
        berth: BerthOccupancy<T, Q>,
    ) -> Result<Self, FeasibleStateError<T>> {
        Self::validate(&SolverState {
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

    fn validate(state: &SolverState<'p, T, C, Q>) -> Result<(), FeasibleStateError<T>> {
        let committed = state.ledger().committed(); // HashMap<MovableRequestId, _>
        let mut missing: Vec<RequestId> = Vec::new();

        for &mid in state.problem().movables().keys() {
            if !committed.contains_key(&mid) {
                missing.push(RequestId::from(mid));
            }
        }

        if !missing.is_empty() {
            return Err(FeasibleStateError::UnassignedRequests(missing));
        }

        let quay_len = state.problem().quay_length();
        let mut items: Vec<Item<T>> = Vec::new();

        for fa in state.problem().iter_fixed_assignments() {
            let aref = dock_alloc_model::AssignmentRef::new(
                fa.request(),
                fa.start_position(),
                fa.start_time(),
            );
            items.push(Item::new(
                fa.id(),
                rect_for_assignment(aref),
                fa.request().feasible_time_window(),
                fa.request().feasible_space_window(),
            ));
        }

        for ma in state.ledger().iter_movable_assignments() {
            let aref = dock_alloc_model::AssignmentRef::new(
                ma.request(),
                ma.start_position(),
                ma.start_time(),
            );
            items.push(Item::new(
                ma.id(),
                rect_for_assignment(aref),
                ma.request().feasible_time_window(),
                ma.request().feasible_space_window(),
            ));
        }

        for it in &items {
            let (sint, tint) = it.rect.into_inner();

            if !it.feasible_time_window.contains_interval(&tint) {
                return Err(FeasibleStateError::AssignmentOutsideTimeWindow(
                    AssignmentOutsideTimeWindowError::new(it.req_id, it.feasible_time_window, tint),
                ));
            }

            if !it.feasible_space_window.contains_interval(&sint) {
                return Err(FeasibleStateError::AssignmentOutsideSpaceWindow(
                    AssignmentOutsideSpaceWindowError::new(
                        it.req_id,
                        it.feasible_space_window,
                        sint,
                    ),
                ));
            }

            let quay_bounds = state.berth().quay_space_interval();
            if !quay_bounds.contains_interval(&sint) {
                return Err(FeasibleStateError::AssignmentExceedsQuay(
                    AssignmentExceedsQuayError::new(it.req_id, state.problem().quay_length(), sint),
                ));
            }

            match state.berth().is_occupied(&it.rect) {
                Ok(true) => {}
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
        let active_sorted_by_end = |v: &mut Vec<usize>| {
            v.sort_by(|&i, &j| {
                let ei = items[i].rect.time().end().value();
                let ej = items[j].rect.time().end().value();
                ei.cmp(&ej)
            })
        };

        for &i in &order {
            let t_start_i = items[i].rect.time().start();
            active_sorted_by_end(&mut active);
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
                let a = &items[i];
                let b = &items[j];

                if let Some(inter) = a.rect.intersection(&b.rect) {
                    let (ra, rb) = if a.req_id.value() <= b.req_id.value() {
                        (a.req_id, b.req_id)
                    } else {
                        (b.req_id, a.req_id)
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
}

impl<'p, T, C, Q> FeasibleSolverState<'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead + QuayWrite,
{
    pub fn apply_plan(&mut self, plan: &'p Plan<T, C>) -> Result<(), SolverStateApplyError> {
        self.ledger.apply(plan.ledger_commit())?;
        self.berth.apply(plan.berth_commit())?;
        Ok(())
    }
}

impl<'p, T, C, Q> TryFrom<FeasibleSolverState<'p, T, C, Q>> for SolverState<'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    type Error = FeasibleStateError<T>;

    fn try_from(value: FeasibleSolverState<'p, T, C, Q>) -> Result<Self, Self::Error> {
        Ok(Self::new(value.problem, value.ledger, value.berth))
    }
}

impl<'p, T, C, Q> From<FeasibleSolverState<'p, T, C, Q>> for SolutionRef<'p, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead,
{
    fn from(value: FeasibleSolverState<'p, T, C, Q>) -> Self {
        value.ledger.into()
    }
}

pub trait ConstructiveSolver<T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    type SolveError;

    fn build_state<'p>(
        &self,
        problem: &'p Problem<T, C>,
    ) -> Result<FeasibleSolverState<'p, T, C, Q>, Self::SolveError>;
}

pub trait Solver<T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead + QuayWrite,
{
    type SolveError;

    fn solve<'p>(
        &self,
        problem: &'p Problem<T, C>,
    ) -> Result<SolutionRef<'p, T, C>, Self::SolveError>;
}
