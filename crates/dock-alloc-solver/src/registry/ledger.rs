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

use crate::registry::{
    commit::LedgerOverlayCommit, operations::Operation, overlay::AssignmentLedgerOverlay,
};
use dock_alloc_core::{
    SolverVariable,
    space::{SpaceInterval, SpacePosition},
    time::TimePoint,
};
use dock_alloc_model::prelude::*;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub struct AssignmentLedger<'a, T: SolverVariable, C: SolverVariable> {
    problem: &'a Problem<T, C>,
    committed: HashMap<MovableRequestId, AssignmentRef<'a, Movable, T, C>>,
}

impl<'a, T, C> From<&'a Problem<T, C>> for AssignmentLedger<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    fn from(problem: &'a Problem<T, C>) -> Self {
        Self {
            problem,
            committed: HashMap::new(),
        }
    }
}

/// Errors that can occur during ledger operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LedgerError {
    /// Attempted to commit an assignment that is already committed.
    AlreadyCommitted,
    /// Attempted to uncommit an assignment that is not currently committed.
    NotCommitted,
}

impl std::fmt::Display for LedgerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LedgerError::AlreadyCommitted => write!(f, "Assignment already committed"),
            LedgerError::NotCommitted => write!(f, "Assignment not committed"),
        }
    }
}

impl std::error::Error for LedgerError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LedgerApplyValidationError<T: SolverVariable> {
    Ledger(LedgerError),
    AssignmentBeforeArrivalTime(AssignmentBeforeArrivalTimeError<T>),
    AssignmentOutsideSpaceWindow(AssignmentOutsideSpaceWindowError),
}

impl<T: SolverVariable + std::fmt::Display> std::fmt::Display for LedgerApplyValidationError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LedgerApplyValidationError::Ledger(e) => write!(f, "{e}"),
            LedgerApplyValidationError::AssignmentBeforeArrivalTime(e) => write!(f, "{e}"),
            LedgerApplyValidationError::AssignmentOutsideSpaceWindow(e) => write!(f, "{e}"),
        }
    }
}

impl<T: SolverVariable + std::fmt::Display + std::fmt::Debug> std::error::Error
    for LedgerApplyValidationError<T>
{
}

impl<'a, T, C> AssignmentLedger<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    pub fn new(problem: &'a Problem<T, C>) -> Self {
        Self {
            problem,
            committed: HashMap::new(),
        }
    }

    #[inline]
    pub fn problem(&self) -> &'a Problem<T, C> {
        self.problem
    }

    #[inline]
    pub fn committed(&self) -> &HashMap<MovableRequestId, AssignmentRef<'a, Movable, T, C>> {
        &self.committed
    }

    #[inline]
    pub fn get_movable_assignment(
        &self,
        id: &MovableRequestId,
    ) -> Option<&AssignmentRef<'a, Movable, T, C>> {
        self.committed.get(id)
    }

    #[inline]
    pub fn commit_assignment(
        &mut self,
        req: &'a Request<Movable, T, C>,
        start_time: TimePoint<T>,
        start_position: SpacePosition,
    ) -> Result<AssignmentRef<'a, Movable, T, C>, LedgerError> {
        let id = req.typed_id();
        if self.committed.contains_key(&id) {
            return Err(LedgerError::AlreadyCommitted);
        }

        let assignment = AssignmentRef::new(req, start_position, start_time);
        self.committed.insert(id, assignment);
        Ok(assignment)
    }

    #[inline]
    pub fn uncommit_assignment(
        &mut self,
        assignment: &AssignmentRef<'a, Movable, T, C>,
    ) -> Result<AssignmentRef<'a, Movable, T, C>, LedgerError> {
        self.committed
            .remove(&assignment.typed_id())
            .ok_or(LedgerError::NotCommitted)
    }

    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = FixedRequestId> + '_ {
        self.problem.preassigned().iter().map(|r| r.typed_id())
    }

    #[inline]
    pub fn iter_fixed_assignments(
        &self,
    ) -> impl Iterator<Item = AssignmentRef<'a, Fixed, T, C>> + '_ {
        self.problem.preassigned().iter().map(|a| a.as_ref())
    }

    #[inline]
    pub fn iter_movable_handles(&self) -> impl Iterator<Item = &MovableRequestId> + '_ {
        self.committed.keys()
    }

    #[inline]
    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = &AssignmentRef<'a, Movable, T, C>> + '_ {
        self.committed.values()
    }

    #[inline]
    pub fn iter_committed(&self) -> impl Iterator<Item = &AssignmentRef<'a, Movable, T, C>> {
        self.committed.values()
    }

    #[inline]
    pub fn iter_unassigned_requests(&self) -> impl Iterator<Item = &Request<Movable, T, C>> + '_ {
        self.problem
            .movables()
            .iter()
            .filter(move |req| !self.committed.contains_key(&req.typed_id()))
    }

    #[inline]
    pub fn iter_assigned_requests(&self) -> impl Iterator<Item = &Request<Movable, T, C>> + '_ {
        self.problem
            .movables()
            .iter()
            .filter(move |req| self.committed.contains_key(&req.typed_id()))
    }

    #[inline]
    pub fn iter_assignments(&self) -> impl Iterator<Item = AnyAssignmentRef<'_, T, C>> + '_ {
        let fixed_iter = self
            .problem
            .preassigned()
            .iter()
            .map(AnyAssignmentRef::from);
        let movable_iter = self.committed.values().map(AnyAssignmentRef::from);
        fixed_iter.chain(movable_iter)
    }

    #[inline]
    pub fn push_operation(&mut self, op: Operation<'a, T, C>) -> Result<(), LedgerError> {
        match op {
            Operation::Assign(assign_op) => {
                let assignment = assign_op.assignment();
                self.commit_assignment(
                    assignment.request(),
                    assignment.start_time(),
                    assignment.start_position(),
                )?;
            }
            Operation::Unassign(unassign_op) => {
                let assignment = unassign_op.assignment();
                self.uncommit_assignment(assignment)?;
            }
        }
        Ok(())
    }

    #[inline]
    pub fn apply(&mut self, commit: &LedgerOverlayCommit<'a, T, C>) -> Result<(), LedgerError> {
        for op in commit.operations() {
            self.push_operation(op.clone())?;
        }
        Ok(())
    }

    #[inline]
    pub fn push_operation_validated(
        &mut self,
        op: Operation<'a, T, C>,
    ) -> Result<(), LedgerApplyValidationError<T>> {
        match op {
            Operation::Assign(assign_op) => {
                let assignment = assign_op.assignment();
                Self::validate_assignment_in_request_windows(assignment)?;
                self.commit_assignment(
                    assignment.request(),
                    assignment.start_time(),
                    assignment.start_position(),
                )
                .map_err(LedgerApplyValidationError::Ledger)?;
            }
            Operation::Unassign(unassign_op) => {
                let assignment = unassign_op.assignment();
                self.uncommit_assignment(assignment)
                    .map_err(LedgerApplyValidationError::Ledger)?;
            }
        }
        Ok(())
    }

    #[inline]
    pub fn apply_validated(
        &mut self,
        commit: &LedgerOverlayCommit<'a, T, C>,
    ) -> Result<(), LedgerApplyValidationError<T>> {
        for op in commit.operations() {
            self.push_operation_validated(op.clone())?;
        }
        Ok(())
    }

    #[inline]
    pub fn overlay(&self) -> AssignmentLedgerOverlay<'_, 'a, '_, T, C> {
        AssignmentLedgerOverlay::new(self)
    }

    #[inline]
    pub(crate) fn validate_assignment_in_request_windows(
        assignment: &AssignmentRef<'a, Movable, T, C>,
    ) -> Result<(), LedgerApplyValidationError<T>> {
        let r = assignment.request();
        let t0 = assignment.start_time();
        let s0 = assignment.start_position();
        let s1 = SpacePosition::new(s0.value() + r.length().value());
        let s_iv = SpaceInterval::new(s0, s1);

        let arrival_time = r.arrival_time();
        if t0 < arrival_time {
            return Err(LedgerApplyValidationError::AssignmentBeforeArrivalTime(
                AssignmentBeforeArrivalTimeError::new(r.id(), arrival_time, t0),
            ));
        }

        let windows = r.feasible_space_windows();
        if !windows.iter().any(|w| w.contains_interval(&s_iv)) {
            return Err(LedgerApplyValidationError::AssignmentOutsideSpaceWindow(
                AssignmentOutsideSpaceWindowError::new(r.id(), windows.to_vec(), s_iv),
            ));
        }

        Ok(())
    }
}

impl<'a, 'l, T, C> From<&'l AssignmentLedger<'a, T, C>> for SolutionRef<'l, T, C>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
{
    fn from(val: &'l AssignmentLedger<'a, T, C>) -> Self {
        let decisions: HashMap<RequestId, AnyAssignmentRef<'l, T, C>> =
            val.iter_assignments().map(|a| (a.id(), a)).collect();
        SolutionRef::from_assignments(decisions)
    }
}

impl<'a, T, C> From<AssignmentLedger<'a, T, C>> for SolutionRef<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
{
    fn from(val: AssignmentLedger<'a, T, C>) -> Self {
        let decisions: HashMap<RequestId, AnyAssignmentRef<'a, T, C>> = {
            let mut decisions = HashMap::new();
            for assignment in val.problem().iter_fixed_assignments() {
                let assignment_ref = AnyAssignmentRef::from(assignment.as_ref());
                decisions.insert(assignment_ref.id(), assignment_ref);
            }
            for assignment in val.committed().values() {
                let assignment_ref = AnyAssignmentRef::from(*assignment);
                decisions.insert(assignment_ref.id(), assignment_ref);
            }
            decisions
        };
        SolutionRef::from_assignments(decisions)
    }
}

#[cfg(test)]
mod ledger_overlay_tests {
    use super::*;
    use dock_alloc_core::{
        cost::Cost,
        space::{SpaceInterval, SpaceLength},
        time::TimeDelta,
    };

    type Tm = i64;
    type Cm = i64;

    fn req_movable_ok(
        id: u64,
        len: usize,
        t0: i64,
        proc_t: i64,
        s0: usize,
        s1: usize,
    ) -> Request<Movable, Tm, Cm> {
        Request::<Movable, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimePoint::new(t0),
            TimeDelta::new(proc_t),
            SpacePosition::new(s0),
            Cost::new(1),
            Cost::new(1),
            vec![SpaceInterval::new(
                SpacePosition::new(s0),
                SpacePosition::new(s1),
            )],
        )
        .expect("valid movable request")
    }

    fn req_fixed_ok(
        id: u64,
        len: usize,
        t0: i64,
        proc_t: i64,
        s0: usize,
        s1: usize,
    ) -> Request<Fixed, Tm, Cm> {
        Request::<Fixed, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimePoint::new(t0),
            TimeDelta::new(proc_t),
            SpacePosition::new(s0),
            Cost::new(1),
            Cost::new(1),
            vec![SpaceInterval::new(
                SpacePosition::new(s0),
                SpacePosition::new(s1),
            )],
        )
        .expect("valid fixed request")
    }

    fn ids<I: Iterator<Item = RequestId>>(it: I) -> Vec<RequestId> {
        let mut v: Vec<_> = it.collect();
        v.sort_by_key(|id| id.value());
        v
    }

    #[test]
    fn test_ledger_initial_iterators_ok() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 0, 5, 0, 100);
        let r2 = req_movable_ok(2, 10, 0, 5, 0, 100);
        let r3 = req_movable_ok(3, 10, 0, 5, 0, 100);
        let r_fixed = req_fixed_ok(10, 10, 0, 5, 0, 100);

        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();
        b.add_movable_request(r3.clone()).unwrap();

        let fixed_a =
            Assignment::<Fixed, _, _>::new(r_fixed.clone(), SpacePosition::new(60), 0.into());
        b.add_preassigned(fixed_a).unwrap();

        let problem = b.build();
        let ledger = AssignmentLedger::from(&problem);

        // fixed via handles (now &FixedRequestId -> RequestId)
        let fixed_ids = ids(ledger.iter_fixed_handles().map(|h| (h).into()));
        assert_eq!(fixed_ids, vec![RequestId::new(10)]);
        assert_eq!(ledger.iter_fixed_assignments().count(), 1);

        assert_eq!(ledger.iter_movable_handles().count(), 0);
        assert_eq!(ledger.iter_movable_assignments().count(), 0);

        // &Request<Movable> -> RequestId directly
        let unassigned_ids = ids(ledger.iter_unassigned_requests().map(|r| r.id()));
        assert_eq!(unassigned_ids, vec![r1.id(), r2.id(), r3.id()]);
        let assigned_ids = ids(ledger.iter_assigned_requests().map(|r| r.id()));
        assert!(assigned_ids.is_empty());

        // all visible assignments = fixed only (erased view)
        let all_a_ids = ids(ledger.iter_assignments().map(|a| a.request().id()));
        assert_eq!(all_a_ids, vec![r_fixed.id()]);
    }

    #[test]
    fn test_ledger_commit_and_iterators_update() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 0, 5, 0, 100);
        let r2 = req_movable_ok(2, 10, 0, 5, 0, 100);
        let r3 = req_movable_ok(3, 10, 0, 5, 0, 100);
        let r_fixed = req_fixed_ok(10, 10, 0, 5, 0, 100);

        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();
        b.add_movable_request(r3.clone()).unwrap();
        b.add_preassigned(Assignment::<Fixed, _, _>::new(
            r_fixed.clone(),
            SpacePosition::new(60),
            TimePoint::new(0),
        ))
        .unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);
        let mov = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let _ma1 = ledger
            .commit_assignment(mov, 0.into(), 0.into())
            .expect("commit r1");

        // &MovableRequestId -> RequestId
        let mov_ids = ids(ledger.iter_movable_handles().map(|h| (*h).into()));
        assert_eq!(mov_ids, vec![r1.id()]);

        let unassigned_ids = ids(ledger.iter_unassigned_requests().map(|r| r.id()));
        assert_eq!(unassigned_ids, vec![r2.id(), r3.id()]);
        let assigned_ids = ids(ledger.iter_assigned_requests().map(|r| r.id()));
        assert_eq!(assigned_ids, vec![r1.id()]);

        let all_a_ids = ids(ledger.iter_assignments().map(|a| a.request().id()));
        assert_eq!(all_a_ids, {
            let mut v = vec![r_fixed.id(), r1.id()];
            v.sort_by_key(|id| id.value());
            v
        });
    }

    // helper: build an assignment ref for a movable request
    fn asg<'r>(
        r: &'r Request<Movable, Tm, Cm>,
        pos: usize,
        time: i64,
    ) -> AssignmentRef<'r, Movable, Tm, Cm> {
        AssignmentRef::new(r, SpacePosition::new(pos), TimePoint::new(time))
    }

    #[test]
    fn test_overlay_assign_then_into_commit_and_apply_updates_ledger() {
        // Problem with two movables; ledger initially empty.
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 0, 5, 0, 100);
        let r2 = req_movable_ok(2, 10, 0, 5, 0, 100);
        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        // Stage an assignment for r1 in the overlay.
        let mut ov = ledger.overlay();
        let req1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .expect("movable r1 exists");
        ov.commit_assignment(req1, TimePoint::new(0), SpacePosition::new(10))
            .expect("stage commit r1");

        // Convert overlay to an owned commit and apply to the ledger.
        let commit = ov.into_commit();
        ledger.apply(&commit).expect("apply overlay commit");

        // r1 is now committed in the base ledger; r2 remains unassigned.
        let assigned_ids = ids(ledger.iter_assigned_requests().map(|r| r.id()));
        assert_eq!(assigned_ids, vec![r1.id()]);

        let unassigned_ids = ids(ledger.iter_unassigned_requests().map(|r| r.id()));
        assert_eq!(unassigned_ids, vec![r2.id()]);
    }

    #[test]
    fn test_overlay_unassign_then_into_commit_and_apply_updates_ledger() {
        // Problem with one movable; ledger starts with r1 committed.
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 0, 5, 0, 100);
        b.add_movable_request(r1.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        let mov1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let _ = ledger
            .commit_assignment(mov1, TimePoint::new(0), SpacePosition::new(0))
            .expect("commit r1 in base");

        // Build overlay on top; pick the branded base assignment via overlay iterator.
        let mut ov = ledger.overlay();
        let branded_base = ov
            .iter_movable_assignments()
            .next()
            .expect("overlay should see base assignment");
        ov.uncommit_assignment(&branded_base)
            .expect("stage uncommit r1");

        // Turn into commit and apply to base.
        let commit = ov.into_commit();
        ledger.apply(&commit).expect("apply overlay commit");

        // r1 no longer committed.
        assert!(ledger.iter_assigned_requests().next().is_none());
        let unassigned_ids = ids(ledger.iter_unassigned_requests().map(|r| r.id()));
        assert_eq!(unassigned_ids, vec![r1.id()]);
    }

    #[test]
    fn test_overlay_move_then_into_commit_and_apply_updates_ledger() {
        // Problem with one movable; ledger starts with r1 committed at (pos=0, time=0).
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 0, 5, 0, 100);
        b.add_movable_request(r1.clone()).unwrap();
        let problem = b.build();

        let mut ledger = AssignmentLedger::from(&problem);
        let mov1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let _ = ledger
            .commit_assignment(mov1, TimePoint::new(0), SpacePosition::new(0))
            .expect("commit r1 in base");

        // Overlay: get branded "old", then stage a move to (pos=30, time=10).
        let mut ov = ledger.overlay();
        let branded_old = ov
            .iter_movable_assignments()
            .next()
            .expect("overlay should see base assignment");

        let new_asg = asg(&r1, 30, 10);
        let _staged_new = ov
            .move_assignment(&branded_old, new_asg)
            .expect("stage move r1");

        // Convert to commit and apply to base ledger.
        let commit = ov.into_commit();
        ledger.apply(&commit).expect("apply overlay commit");

        // Verify the new placement is in the ledger.
        let a = ledger
            .iter_movable_assignments()
            .next()
            .expect("moved assignment present");
        assert_eq!(a.request().id(), r1.id());
        assert_eq!(a.start_position(), SpacePosition::new(30));
        assert_eq!(a.start_time(), TimePoint::new(10));
    }
}
