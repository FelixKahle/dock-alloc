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

use dock_alloc_model::{Assignment, Fixed, Problem, RequestId, Solution};
use num_traits::{PrimInt, Signed};
use std::{
    collections::{BTreeMap, HashMap},
    marker::PhantomData,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MovableHandle<'brand> {
    id: RequestId,
    _phantom: PhantomData<&'brand ()>,
}

impl<'brand> MovableHandle<'brand> {
    #[inline]
    pub fn id(self) -> RequestId {
        self.id
    }
}

impl<'brand> std::fmt::Display for MovableHandle<'brand> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MovableHandle({})", self.id)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FixedHandle<'brand> {
    id: RequestId,
    _phantom: PhantomData<&'brand ()>,
}

impl<'brand> FixedHandle<'brand> {
    #[inline]
    pub fn id(self) -> RequestId {
        self.id
    }
}

impl<'brand> std::fmt::Display for FixedHandle<'brand> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FixedHandle({})", self.id)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Movable<'brand, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    assignment: Assignment<T, C>,
    handle: MovableHandle<'brand>,
    _phantom: PhantomData<&'brand ()>,
}

impl<'brand, T: PrimInt + Signed, C: PrimInt + Signed> Movable<'brand, T, C> {
    #[inline]
    pub fn assignment(&self) -> Assignment<T, C> {
        self.assignment
    }

    #[inline]
    pub fn handle(&self) -> MovableHandle<'brand> {
        self.handle
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.handle.id()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentLedger<'brand, 'a, T: PrimInt + Signed, C: PrimInt + Signed> {
    problem: &'a Problem<T, C>,
    committed: HashMap<RequestId, Movable<'brand, T, C>>,
    _phantom: PhantomData<&'brand ()>,
}

impl<'brand, 'a, T, C> From<&'a Problem<T, C>> for AssignmentLedger<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(problem: &'a Problem<T, C>) -> Self {
        Self {
            problem,
            committed: HashMap::new(),
            _phantom: PhantomData,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LedgerError {
    AlreadyCommitted,
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

impl<'brand, 'a, T, C> AssignmentLedger<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    pub fn new(problem: &'a Problem<T, C>) -> Self {
        Self {
            problem,
            committed: HashMap::new(),
            _phantom: PhantomData,
        }
    }

    #[inline]
    pub fn problem(&self) -> &'a Problem<T, C> {
        self.problem
    }

    #[inline]
    pub fn committed(&self) -> &HashMap<RequestId, Movable<'brand, T, C>> {
        &self.committed
    }

    pub fn commit(&mut self, ma: Movable<'brand, T, C>) -> Result<(), LedgerError> {
        let id = ma.id();
        if self.committed.contains_key(&id) {
            return Err(LedgerError::AlreadyCommitted);
        }
        debug_assert!(self.problem.unassigned().contains_key(&id));
        self.committed.insert(id, ma);
        Ok(())
    }

    pub fn uncommit(
        &mut self,
        mh: MovableHandle<'brand>,
    ) -> Result<Movable<'brand, T, C>, LedgerError> {
        self.committed
            .remove(&mh.id())
            .ok_or(LedgerError::NotCommitted)
    }

    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = FixedHandle<'brand>> + '_ {
        self.problem.preassigned().keys().map(|&rid| FixedHandle {
            id: rid,
            _phantom: PhantomData,
        })
    }

    #[inline]
    pub fn iter_fixed_assignments(&self) -> impl Iterator<Item = &Fixed<T, C>> + '_ {
        self.problem.preassigned().values()
    }

    #[inline]
    pub fn iter_movable_handles(&self) -> impl Iterator<Item = MovableHandle<'brand>> + '_ {
        self.committed.keys().map(|&rid| MovableHandle {
            id: rid,
            _phantom: PhantomData,
        })
    }

    #[inline]
    pub fn iter_movable_assignments(&self) -> impl Iterator<Item = &Movable<'brand, T, C>> + '_ {
        self.committed.values()
    }

    #[inline]
    pub fn iter_committed(&self) -> impl Iterator<Item = &Movable<'brand, T, C>> {
        self.committed.values()
    }

    pub fn iter_assignments(&self) -> impl Iterator<Item = Assignment<T, C>> + '_ {
        let fixed_iter = self
            .problem
            .preassigned()
            .values()
            .map(|fixed| *fixed.assignment());

        let movable_iter = self.committed.values().map(|ma| ma.assignment());
        fixed_iter.chain(movable_iter)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentOverlay<'brand, 'a, 'l, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    ledger: &'l AssignmentLedger<'brand, 'a, T, C>,
    staged_commits: BTreeMap<RequestId, Movable<'brand, T, C>>,
    staged_uncommits: BTreeMap<RequestId, MovableHandle<'brand>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StageError {
    AlreadyCommittedInBase(RequestId),
    AlreadyStagedCommit(RequestId),
    AlreadyStagedUncommit(RequestId),
    NotCommittedInBase(RequestId),
}

impl std::fmt::Display for StageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StageError::AlreadyCommittedInBase(id) => {
                write!(
                    f,
                    "Assignment with id {} already committed in base ledger",
                    id
                )
            }
            StageError::AlreadyStagedCommit(id) => {
                write!(f, "Assignment with id {} already staged for commit", id)
            }
            StageError::AlreadyStagedUncommit(id) => {
                write!(f, "Assignment with id {} already staged for uncommit", id)
            }
            StageError::NotCommittedInBase(id) => {
                write!(f, "Assignment with id {} not committed in base ledger", id)
            }
        }
    }
}

impl std::error::Error for StageError {}

impl<'brand, 'a, 'l, T, C> AssignmentOverlay<'brand, 'a, 'l, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    pub fn new(ledger: &'l AssignmentLedger<'brand, 'a, T, C>) -> Self {
        Self {
            ledger,
            staged_commits: BTreeMap::new(),
            staged_uncommits: BTreeMap::new(),
        }
    }

    pub fn commit(&mut self, ma: Movable<'brand, T, C>) -> Result<(), StageError> {
        let id = ma.id();
        if self.ledger.committed().contains_key(&id) {
            return Err(StageError::AlreadyCommittedInBase(id));
        }
        if let Some(existing) = self.staged_commits.get(&id) {
            if *existing == ma {
                return Ok(());
            } else {
                return Err(StageError::AlreadyStagedCommit(id));
            }
        }
        self.staged_uncommits.remove(&id);
        self.staged_commits.insert(id, ma);
        Ok(())
    }

    pub fn uncommit(
        &mut self,
        mh: MovableHandle<'brand>,
    ) -> Result<Movable<'brand, T, C>, StageError> {
        let id = mh.id();
        if let Some(ma) = self.staged_commits.remove(&id) {
            return Ok(ma);
        }
        if self.staged_uncommits.contains_key(&id) {
            return Err(StageError::AlreadyStagedUncommit(id));
        }
        let ma = *self
            .ledger
            .committed()
            .get(&id)
            .ok_or(StageError::NotCommittedInBase(id))?;

        self.staged_uncommits.insert(id, mh);
        Ok(ma)
    }

    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = FixedHandle<'brand>> + '_ {
        self.ledger.iter_fixed_handles()
    }

    #[inline]
    pub fn iter_fixed_assignments(&self) -> impl Iterator<Item = &Fixed<T, C>> + '_ {
        self.ledger.iter_fixed_assignments()
    }

    #[inline]
    pub fn iter_movable_handles(&self) -> impl Iterator<Item = MovableHandle<'brand>> + '_ {
        let base_visible = self
            .ledger
            .iter_committed()
            .filter(move |ma| {
                let id = ma.id();
                !self.staged_uncommits.contains_key(&id) && !self.staged_commits.contains_key(&id)
            })
            .map(|ma| ma.handle());

        let staged = self.staged_commits.values().map(|ma| ma.handle());
        base_visible.chain(staged)
    }

    #[inline]
    pub fn iter_movable_assignments(&self) -> impl Iterator<Item = &Movable<'brand, T, C>> + '_ {
        let base_visible = self.ledger.iter_movable_assignments().filter(move |ma| {
            let id = ma.id();
            !self.staged_uncommits.contains_key(&id) && !self.staged_commits.contains_key(&id)
        });

        let staged = self.staged_commits.values();
        base_visible.chain(staged)
    }

    #[inline]
    pub fn iter_staged_commits(&self) -> impl Iterator<Item = &Movable<'brand, T, C>> {
        self.staged_commits.values()
    }

    #[inline]
    pub fn iter_staged_uncommits(&self) -> impl Iterator<Item = &MovableHandle<'brand>> {
        self.staged_uncommits.values()
    }

    pub fn iter_assignments(&self) -> impl Iterator<Item = &Assignment<T, C>> + '_ {
        let fixed = self
            .ledger
            .problem()
            .preassigned()
            .values()
            .map(|fx| fx.assignment());
        let base = self
            .ledger
            .iter_committed()
            .filter(move |ma| {
                let id = ma.id();
                !self.staged_uncommits.contains_key(&id) && !self.staged_commits.contains_key(&id)
            })
            .map(|ma| &ma.assignment);
        let staged = self.staged_commits.values().map(|ma| &ma.assignment);
        fixed.chain(base).chain(staged)
    }
}

impl<'brand, 'a, T, C> From<&AssignmentLedger<'brand, 'a, T, C>> for Solution<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
{
    fn from(ledger: &AssignmentLedger<'brand, 'a, T, C>) -> Self {
        let decisions: HashMap<_, _> = ledger
            .iter_assignments()
            .map(|a| (a.request().id(), a))
            .collect();
        Solution::from_assignments(decisions)
    }
}

#[cfg(test)]
mod overlay_ledger_tests {
    use super::*;
    use dock_alloc_core::domain::{
        Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
    };
    use dock_alloc_model::{Fixed, Request};
    use std::collections::{BTreeSet, HashSet};

    type T = i64;
    type C = i64;

    fn req_ok(id: u64) -> Request<T, C> {
        // generous, always-valid windows
        let len = 4usize;
        let proc = 3i64;
        let t0 = 0i64;
        let t1 = 1_000i64;
        let s0 = 0usize;
        let s1 = 1_000usize;

        Request::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimeDelta::new(proc),
            SpacePosition::new(10), // target pos (arbitrary)
            Cost::new(1),
            Cost::new(1),
            TimeInterval::new(TimePoint::new(t0), TimePoint::new(t1)),
            SpaceInterval::new(SpacePosition::new(s0), SpacePosition::new(s1)),
        )
        .expect("valid request")
    }

    fn asg(req: Request<T, C>, start_pos: usize, start_time: i64) -> Assignment<T, C> {
        Assignment::new(
            req,
            SpacePosition::new(start_pos),
            TimePoint::new(start_time),
        )
    }

    fn mhandle<'b>(rid: u64) -> MovableHandle<'b> {
        MovableHandle {
            id: RequestId::new(rid),
            _phantom: PhantomData,
        }
    }

    fn movable<'b>(
        rid: u64,
        start_pos: usize,
        start_time: i64,
    ) -> (Request<T, C>, Movable<'b, T, C>) {
        let r = req_ok(rid);
        let a = asg(r, start_pos, start_time);
        let ma = Movable {
            assignment: a,
            handle: mhandle::<'b>(rid),
            _phantom: PhantomData,
        };
        (r, ma)
    }

    fn problem_with_unassigned(ids: &[u64]) -> Problem<T, C> {
        let mut b = dock_alloc_model::ProblemBuilder::<T, C>::new(SpaceLength::new(2_000));
        for &id in ids {
            b.add_unassigned_request(req_ok(id)).unwrap();
        }
        b.build()
    }

    fn problem_with_unassigned_and_fixed(
        unassigned: &[u64],
        fixed: &[(u64, usize, i64)],
    ) -> Problem<T, C> {
        let mut b = dock_alloc_model::ProblemBuilder::<T, C>::new(SpaceLength::new(2_000));
        for &id in unassigned {
            b.add_unassigned_request(req_ok(id)).unwrap();
        }
        for &(id, spos, t0) in fixed {
            let r = req_ok(id);
            let a = asg(r, spos, t0);
            b.add_preassigned(Fixed::new(a)).unwrap();
        }
        b.build()
    }

    fn ids_from_assignments(it: impl Iterator<Item = Assignment<T, C>>) -> BTreeSet<RequestId> {
        it.map(|a| a.request().id()).collect()
    }

    fn ids_from_assignment_refs<'x>(
        it: impl Iterator<Item = &'x Assignment<T, C>>,
    ) -> BTreeSet<RequestId> {
        it.map(|a| a.request().id()).collect()
    }

    fn ids_from_solution<T, C>(sol: &Solution<T, C>) -> BTreeSet<RequestId>
    where
        T: PrimInt + Signed + TryFrom<usize>,
        C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
    {
        sol.decisions().keys().copied().collect::<BTreeSet<_>>()
    }

    #[test]
    fn ledger_commit_and_uncommit_happy_path() {
        let prob = problem_with_unassigned(&[1]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        // Build movable for rid=1 that exists in problem.unassigned
        let (_r, ma) = movable::<'static>(1, 5, 10);

        // Commit ok
        assert!(ledger.commit(ma).is_ok());
        assert_eq!(ledger.committed().len(), 1);

        // Uncommit ok and returns same MA
        let returned = ledger.uncommit(mhandle::<'static>(1)).unwrap();
        assert_eq!(returned, ma);
        assert!(ledger.committed().is_empty());
    }

    #[test]
    fn ledger_uncommit_errors_if_missing() {
        let prob = problem_with_unassigned(&[]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);
        let err = ledger.uncommit(mhandle::<'static>(42)).unwrap_err();
        assert!(matches!(err, LedgerError::NotCommitted));
    }

    #[test]
    fn ledger_commit_errors_if_already_present() {
        let prob = problem_with_unassigned(&[7]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);
        let (_r, ma) = movable::<'static>(7, 1, 0);
        ledger.commit(ma).unwrap();
        let err = ledger.commit(ma).unwrap_err();
        assert!(matches!(err, LedgerError::AlreadyCommitted));
    }

    #[test]
    fn ledger_iter_assignments_includes_fixed_and_committed() {
        // fixed: 100; unassigned: 1,2
        let prob = problem_with_unassigned_and_fixed(&[1, 2], &[(100, 20, 0)]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);
        // commit rid=1
        let (_r1, ma1) = movable::<'static>(1, 3, 0);
        ledger.commit(ma1).unwrap();

        let got = ids_from_assignments(ledger.iter_assignments());
        assert!(got.contains(&RequestId::new(100))); // fixed
        assert!(got.contains(&RequestId::new(1))); // committed
        assert!(!got.contains(&RequestId::new(2))); // still unassigned
    }

    #[test]
    fn overlay_commit_idempotent_and_conflict_on_same_rid_different_assignment() {
        let prob = problem_with_unassigned(&[1]);
        let ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);
        let mut ov = AssignmentOverlay::new(&ledger);

        // Two different assignments for the same rid
        let (_r, ma_a) = movable::<'static>(1, 5, 10);
        let (_r2, ma_b_different) = movable::<'static>(1, 6, 10); // different start pos

        // First time → ok
        assert!(ov.commit(ma_a).is_ok());
        // Idempotent re-commit of identical value → ok
        assert!(ov.commit(ma_a).is_ok());
        // Different assignment for same rid → StageError::AlreadyStagedCommit
        let err = ov.commit(ma_b_different).unwrap_err();
        assert!(matches!(err, StageError::AlreadyStagedCommit(id) if id == RequestId::new(1)));
    }

    #[test]
    fn overlay_uncommit_removes_staged_commit_without_tombstone() {
        let prob = problem_with_unassigned(&[2]);
        let ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);
        let mut ov = AssignmentOverlay::new(&ledger);

        let (_r, ma) = movable::<'static>(2, 7, 1);
        ov.commit(ma).unwrap();

        // uncommit pops staged commit and returns it
        let returned = ov.uncommit(mhandle::<'static>(2)).unwrap();
        assert_eq!(returned, ma);

        // another uncommit now fails (not in base; not staged anymore)
        let err = ov.uncommit(mhandle::<'static>(2)).unwrap_err();
        assert!(matches!(err, StageError::NotCommittedInBase(id) if id == RequestId::new(2)));
    }

    #[test]
    fn overlay_uncommit_on_base_creates_tombstone_and_prevents_double_uncommit() {
        // base has rid=3 committed
        let prob = problem_with_unassigned(&[3]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);
        let (_r, ma) = movable::<'static>(3, 2, 0);
        ledger.commit(ma).unwrap();

        let mut ov = AssignmentOverlay::new(&ledger);

        // First uncommit → returns base MA, and tombstones it in overlay
        let ret = ov.uncommit(mhandle::<'static>(3)).unwrap();
        assert_eq!(ret, ma);

        // Second uncommit on same id → AlreadyStagedUncommit
        let err = ov.uncommit(mhandle::<'static>(3)).unwrap_err();
        assert!(matches!(err, StageError::AlreadyStagedUncommit(id) if id == RequestId::new(3)));
    }

    #[test]
    fn overlay_commit_fails_if_already_committed_in_base() {
        let prob = problem_with_unassigned(&[4]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);
        let (_r, ma) = movable::<'static>(4, 9, 0);
        ledger.commit(ma).unwrap();

        let mut ov = AssignmentOverlay::new(&ledger);
        let err = ov.commit(ma).unwrap_err();
        assert!(matches!(err, StageError::AlreadyCommittedInBase(id) if id == RequestId::new(4)));
    }

    #[test]
    fn overlay_iter_assignments_merges_fixed_plus_base_minus_tombstones_plus_staged() {
        // fixed: 100; base committed: 10,11; overlay tombstones 10; overlay stages 12
        let prob = problem_with_unassigned_and_fixed(&[10, 11, 12], &[(100, 30, 0)]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        let (_r10, ma10) = movable::<'static>(10, 1, 0);
        let (_r11, ma11) = movable::<'static>(11, 2, 0);
        let (_r12, ma12) = movable::<'static>(12, 3, 0);

        ledger.commit(ma10).unwrap();
        ledger.commit(ma11).unwrap();

        let mut ov = AssignmentOverlay::new(&ledger);
        // hide 10 via tombstone
        ov.uncommit(mhandle::<'static>(10)).unwrap();
        // stage 12
        ov.commit(ma12).unwrap();

        let got = ids_from_assignment_refs(ov.iter_assignments());
        let expect: BTreeSet<_> = [100u64, 11u64, 12u64]
            .into_iter()
            .map(RequestId::new)
            .collect();

        assert_eq!(
            got, expect,
            "view should be fixed ∪ (base \\ tombstones) ∪ staged"
        );
    }

    #[test]
    fn overlay_iterators_expose_staged_sets() {
        let prob = problem_with_unassigned(&[5, 6]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        let (_r5, ma5) = movable::<'static>(5, 1, 0);
        let (_r6, ma6) = movable::<'static>(6, 2, 0);
        ledger.commit(ma6).unwrap();

        let mut ov = AssignmentOverlay::new(&ledger);
        ov.commit(ma5).unwrap();
        ov.uncommit(mhandle::<'static>(6)).unwrap();

        let staged_commit_ids: HashSet<_> = ov.iter_staged_commits().map(|ma| ma.id()).collect();
        let staged_uncommit_ids: HashSet<_> = ov.iter_staged_uncommits().map(|h| h.id()).collect();

        assert!(staged_commit_ids.contains(&RequestId::new(5)));
        assert!(staged_uncommit_ids.contains(&RequestId::new(6)));
    }

    #[test]
    fn overlay_commit_after_tombstone_currently_disallowed() {
        let prob = problem_with_unassigned(&[9]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        let (_r, ma) = movable::<'static>(9, 1, 0);
        ledger.commit(ma).unwrap();

        let mut ov = AssignmentOverlay::new(&ledger);
        ov.uncommit(mhandle::<'static>(9)).unwrap();

        let (_r_new, ma_new) = movable::<'static>(9, 5, 10);
        let err = ov.commit(ma_new).unwrap_err();
        assert!(matches!(err, StageError::AlreadyCommittedInBase(id) if id == RequestId::new(9)));
    }

    #[test]
    fn stage_error_messages_are_human_readable() {
        let id = RequestId::new(77);
        assert_eq!(
            format!("{}", StageError::AlreadyCommittedInBase(id)),
            "Assignment with id RequestId(77) already committed in base ledger"
        );
        assert_eq!(
            format!("{}", StageError::AlreadyStagedCommit(id)),
            "Assignment with id RequestId(77) already staged for commit"
        );
        assert_eq!(
            format!("{}", StageError::AlreadyStagedUncommit(id)),
            "Assignment with id RequestId(77) already staged for uncommit"
        );
        assert_eq!(
            format!("{}", StageError::NotCommittedInBase(id)),
            "Assignment with id RequestId(77) not committed in base ledger"
        );
    }

    #[test]
    fn ledger_iter_fixed_handles_and_assignments_match_problem() {
        // fixed: 100, 101
        let prob = problem_with_unassigned_and_fixed(&[], &[(100, 5, 0), (101, 10, 0)]);
        let ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        // Handles
        let handle_ids: BTreeSet<_> = ledger.iter_fixed_handles().map(|h| h.id()).collect();
        let expected: BTreeSet<_> = [100u64, 101u64].into_iter().map(RequestId::new).collect();
        assert_eq!(handle_ids, expected);

        // Assignments (&Fixed<T,C> → &Assignment<T,C>)
        let asg_ids: BTreeSet<_> = ledger
            .iter_fixed_assignments()
            .map(|fx| fx.assignment().request().id())
            .collect();
        assert_eq!(asg_ids, expected);
    }

    #[test]
    fn ledger_iter_movable_handles_and_assignments_after_commits() {
        // unassigned: 1,2
        let prob = problem_with_unassigned(&[1, 2]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        let (_r1, ma1) = movable::<'static>(1, 3, 0);
        let (_r2, ma2) = movable::<'static>(2, 7, 1);
        ledger.commit(ma1).unwrap();
        ledger.commit(ma2).unwrap();

        // Handles (values)
        let handle_ids: BTreeSet<_> = ledger.iter_movable_handles().map(|h| h.id()).collect();
        let expected: BTreeSet<_> = [1u64, 2u64].into_iter().map(RequestId::new).collect();
        assert_eq!(handle_ids, expected);

        // Movable assignments (&Movable)
        let ma_ids: BTreeSet<_> = ledger
            .iter_movable_assignments()
            .map(|ma| ma.id())
            .collect();
        assert_eq!(ma_ids, expected);
    }

    #[test]
    fn overlay_iter_fixed_handles_and_assignments_delegate_to_ledger() {
        // fixed: 100, 101
        let prob = problem_with_unassigned_and_fixed(&[], &[(100, 5, 0), (101, 10, 0)]);
        let ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);
        let ov = AssignmentOverlay::new(&ledger);

        let ov_handle_ids: BTreeSet<_> = ov.iter_fixed_handles().map(|h| h.id()).collect();
        let led_handle_ids: BTreeSet<_> = ledger.iter_fixed_handles().map(|h| h.id()).collect();
        assert_eq!(ov_handle_ids, led_handle_ids);

        let ov_fx_ids: BTreeSet<_> = ov
            .iter_fixed_assignments()
            .map(|fx| fx.assignment().request().id())
            .collect();
        let led_fx_ids: BTreeSet<_> = ledger
            .iter_fixed_assignments()
            .map(|fx| fx.assignment().request().id())
            .collect();
        assert_eq!(ov_fx_ids, led_fx_ids);
    }

    #[test]
    fn overlay_iter_movable_handles_respect_overlay_view() {
        // base commits: 10; staged commit: 12; tombstone: 10
        let prob = problem_with_unassigned(&[10, 12]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);
        let (_r10, ma10) = movable::<'static>(10, 1, 0);
        let (_r12, ma12) = movable::<'static>(12, 3, 0);
        ledger.commit(ma10).unwrap();

        let mut ov = AssignmentOverlay::new(&ledger);
        ov.uncommit(mhandle::<'static>(10)).unwrap(); // hide base 10
        ov.commit(ma12).unwrap(); // show staged 12

        let handle_ids: BTreeSet<_> = ov.iter_movable_handles().map(|h| h.id()).collect();
        let expected: BTreeSet<_> = [12u64].into_iter().map(RequestId::new).collect();
        assert_eq!(handle_ids, expected);
    }

    #[test]
    fn overlay_iter_movable_assignments_respect_overlay_view() {
        // base commits: 10; staged commit: 12; tombstone: 10
        let prob = problem_with_unassigned(&[10, 12]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);
        let (_r10, ma10) = movable::<'static>(10, 1, 0);
        let (_r12, ma12) = movable::<'static>(12, 3, 0);
        ledger.commit(ma10).unwrap();

        let mut ov = AssignmentOverlay::new(&ledger);
        ov.uncommit(mhandle::<'static>(10)).unwrap();
        ov.commit(ma12).unwrap();

        let ids: BTreeSet<_> = ov.iter_movable_assignments().map(|ma| ma.id()).collect();
        let expected: BTreeSet<_> = [12u64].into_iter().map(RequestId::new).collect();
        assert_eq!(ids, expected);
    }

    #[test]
    fn overlay_iter_movable_handles_union_when_no_tombstone() {
        // base has 20 committed; overlay stages 21 (no tombstones) => {20, 21}
        let prob = problem_with_unassigned(&[20, 21]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        let (_r20, ma20) = movable::<'static>(20, 2, 0);
        let (_r21, ma21) = movable::<'static>(21, 4, 0);

        ledger.commit(ma20).unwrap();

        let mut ov = AssignmentOverlay::new(&ledger);
        ov.commit(ma21).unwrap();

        let ids: BTreeSet<_> = ov.iter_movable_handles().map(|h| h.id()).collect();
        let expected: BTreeSet<_> = [20u64, 21u64].into_iter().map(RequestId::new).collect();
        assert_eq!(ids, expected);
    }

    #[test]
    fn ledger_into_solution_includes_fixed_and_committed() {
        // fixed: 100; unassigned: 1,2 -> commit(1)
        let prob = problem_with_unassigned_and_fixed(&[1, 2], &[(100, 20, 0)]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        let (_r1, ma1) = movable::<'static>(1, 3, 0);
        ledger.commit(ma1).unwrap();

        // Build via From<&Ledger>
        let sol: Solution<T, C> = (&ledger).into();

        // Expect fixed(100) + committed(1)
        let ids = ids_from_solution(&sol);
        let expect: BTreeSet<_> = [100u64, 1u64].into_iter().map(RequestId::new).collect();
        assert_eq!(ids, expect);
    }
}
