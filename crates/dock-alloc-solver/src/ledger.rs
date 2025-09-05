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

use dock_alloc_core::domain::{
    Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use dock_alloc_model::{
    Assignment, FixedAssignment, MoveableRequest, Problem, Request, RequestId, Solution,
};
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
    fn new(id: RequestId) -> Self {
        Self {
            id,
            _phantom: PhantomData,
        }
    }

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
    fn new(id: RequestId) -> Self {
        Self {
            id,
            _phantom: PhantomData,
        }
    }

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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BrandedMoveableRequest<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    inner: &'a MoveableRequest<T, C>,
    handle: MovableHandle<'brand>,
    _phantom: PhantomData<&'brand ()>,
}

impl<'brand, 'a, T, C> BrandedMoveableRequest<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(inner: &'a MoveableRequest<T, C>) -> Self {
        Self {
            inner,
            handle: MovableHandle::new(inner.request().id()),
            _phantom: PhantomData,
        }
    }

    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.inner.request().length()
    }

    #[inline]
    pub fn arrival_time(&self) -> TimePoint<T> {
        self.inner.request().arrival_time()
    }

    #[inline]
    pub fn processing_duration(&self) -> TimeDelta<T> {
        self.inner.request().processing_duration()
    }

    #[inline]
    pub fn target_position(&self) -> SpacePosition {
        self.inner.request().target_position()
    }

    #[inline]
    pub fn cost_per_delay(&self) -> Cost<C> {
        self.inner.request().cost_per_delay()
    }

    #[inline]
    pub fn cost_per_position_deviation(&self) -> Cost<C> {
        self.inner.request().cost_per_position_deviation()
    }

    #[inline]
    pub fn feasible_time_window(&self) -> TimeInterval<T> {
        self.inner.request().feasible_time_window()
    }

    #[inline]
    pub fn feasible_space_window(&self) -> SpaceInterval {
        self.inner.request().feasible_space_window()
    }

    #[inline]
    pub fn request(&self) -> &'a Request<T, C> {
        self.inner.request()
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BrandedMoveableAssignment<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    assignment: Assignment<'a, T, C>,
    handle: MovableHandle<'brand>,
    _phantom: PhantomData<&'brand ()>,
}

impl<'brand, 'a, T, C> BrandedMoveableAssignment<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(assignment: Assignment<'a, T, C>, handle: MovableHandle<'brand>) -> Self {
        Self {
            assignment,
            handle,
            _phantom: PhantomData,
        }
    }

    #[inline]
    pub fn assignment(&'_ self) -> &'_ Assignment<'_, T, C> {
        &self.assignment
    }

    pub fn start_position(&self) -> SpacePosition {
        self.assignment.start_position()
    }

    pub fn start_time(&self) -> TimePoint<T> {
        self.assignment.start_time()
    }

    pub fn length(&self) -> SpaceLength {
        self.assignment.request().length()
    }

    pub fn processing_duration(&self) -> TimeDelta<T> {
        self.assignment.request().processing_duration()
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
    problem: &'a Problem<'a, T, C>,
    committed: HashMap<RequestId, BrandedMoveableAssignment<'brand, 'a, T, C>>,
    _phantom: PhantomData<&'brand ()>,
}

impl<'brand, 'a, T, C> From<&'a Problem<'a, T, C>> for AssignmentLedger<'brand, 'a, T, C>
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

/// Errors that can occur during ledger operations.
///
/// These errors represent the different failure modes when committing or uncommitting
/// assignments in the ledger.
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
    pub fn problem(&self) -> &'a Problem<'a, T, C> {
        self.problem
    }

    #[inline]
    pub fn committed(&self) -> &HashMap<RequestId, BrandedMoveableAssignment<'brand, 'a, T, C>> {
        &self.committed
    }

    #[inline]
    pub fn commit_assignment(
        &mut self,
        assignment: &Assignment<'a, T, C>,
    ) -> Result<BrandedMoveableAssignment<'brand, 'a, T, C>, LedgerError> {
        let id = assignment.request().id();
        if self.committed.contains_key(&id) {
            return Err(LedgerError::AlreadyCommitted);
        }

        debug_assert!(self.problem.unassigned().contains_key(&id));

        let h = MovableHandle::new(id);
        let ma = BrandedMoveableAssignment::new(assignment.clone(), h);
        self.committed.insert(id, ma.clone());
        Ok(ma)
    }

    #[inline]
    pub fn uncommit_assignment(
        &mut self,
        assignment: &'brand BrandedMoveableAssignment<'brand, 'a, T, C>,
    ) -> Result<BrandedMoveableAssignment<'brand, 'a, T, C>, LedgerError> {
        self.committed
            .remove(&assignment.id())
            .ok_or(LedgerError::NotCommitted)
    }

    #[inline]
    pub fn apply(&mut self, overlay: AssignmentLedgerOverlay<'brand, 'a, '_, T, C>) {
        debug_assert!(
            std::ptr::eq(self as *const _, overlay.ledger as *const _),
            "attempted to apply an overlay built from a different ledger"
        );
        for (id, _) in overlay.staged_uncommits.into_iter() {
            if !overlay.staged_commits.contains_key(&id) {
                let _ = self.committed.remove(&id);
            }
        }
        for (id, ma) in overlay.staged_commits.into_iter() {
            let _prev = self.committed.insert(id, ma);
        }
    }

    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = FixedHandle<'brand>> + '_ {
        self.problem
            .preassigned()
            .keys()
            .map(|&rid| FixedHandle::new(rid))
    }

    #[inline]
    pub fn iter_fixed_assignments(
        &self,
    ) -> impl Iterator<Item = &'_ FixedAssignment<'_, T, C>> + '_ {
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
    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = &BrandedMoveableAssignment<'brand, 'a, T, C>> + '_ {
        self.committed.values()
    }

    #[inline]
    pub fn iter_committed(
        &self,
    ) -> impl Iterator<Item = &BrandedMoveableAssignment<'brand, 'a, T, C>> {
        self.committed.values()
    }

    #[inline]
    pub fn iter_unassigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMoveableRequest<'brand, 'a, T, C>> + '_ {
        self.problem
            .unassigned()
            .values()
            .filter(move |req| !self.committed.contains_key(&req.request().id()))
            .map(|req| BrandedMoveableRequest::<'brand, 'a, T, C>::new(req))
    }

    #[inline]
    pub fn iter_assigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMoveableRequest<'brand, 'a, T, C>> + '_ {
        self.problem
            .unassigned()
            .values()
            .filter(move |req| self.committed.contains_key(&req.request().id()))
            .map(|req| BrandedMoveableRequest::<'brand, 'a, T, C>::new(req))
    }

    #[inline]
    pub fn iter_assignments(&self) -> impl Iterator<Item = &'_ Assignment<'_, T, C>> + '_ {
        let fixed_iter = self
            .problem
            .preassigned()
            .values()
            .map(|fixed| fixed.assignment());

        let movable_iter = self.committed.values().map(|ma| ma.assignment());
        fixed_iter.chain(movable_iter)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentLedgerOverlay<'brand, 'a, 'l, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    ledger: &'l AssignmentLedger<'brand, 'a, T, C>,
    staged_commits: BTreeMap<RequestId, BrandedMoveableAssignment<'brand, 'a, T, C>>,
    staged_uncommits: BTreeMap<RequestId, MovableHandle<'brand>>,
}

/// Errors that can occur during overlay staging operations.
///
/// These errors represent the different failure modes when staging commits
/// or uncommits in an assignment overlay.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StageError {
    /// Attempted to stage a commit for a request that is already committed in the base ledger.
    AlreadyCommittedInBase(RequestId),
    /// Attempted to stage a commit for a request that already has a different staged commit.
    AlreadyStagedCommit(RequestId),
    /// Attempted to stage an uncommit for a request that already has a staged uncommit.
    AlreadyStagedUncommit(RequestId),
    /// Attempted to stage an uncommit for a request that is not committed in the base ledger.
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

impl<'brand, 'a, 'l, T, C> AssignmentLedgerOverlay<'brand, 'a, 'l, T, C>
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

    pub fn commit_assignment(
        &mut self,
        assignment: &Assignment<'a, T, C>,
    ) -> Result<BrandedMoveableAssignment<'brand, 'a, T, C>, StageError> {
        let id = assignment.request().id();
        let base_has = self.ledger.committed().contains_key(&id);
        let tombstoned = self.staged_uncommits.contains_key(&id);

        if base_has && !tombstoned {
            return Err(StageError::AlreadyCommittedInBase(id));
        }

        let new_ma = BrandedMoveableAssignment {
            assignment: assignment.clone(),
            handle: MovableHandle {
                id,
                _phantom: PhantomData,
            },
            _phantom: PhantomData,
        };

        if let Some(existing) = self.staged_commits.get(&id) {
            if *existing == new_ma {
                return Ok(existing.clone());
            }
            return Err(StageError::AlreadyStagedCommit(id));
        }

        self.staged_uncommits.remove(&id);
        self.staged_commits.insert(id, new_ma.clone());
        Ok(new_ma)
    }

    #[inline]
    pub fn uncommit_assignment(
        &mut self,
        ma_ref: &'brand BrandedMoveableAssignment<'brand, 'a, T, C>,
    ) -> Result<BrandedMoveableAssignment<'brand, 'a, T, C>, StageError> {
        let id = ma_ref.id();
        if let Some(staged) = self.staged_commits.remove(&id) {
            return Ok(staged);
        }

        if self.staged_uncommits.contains_key(&id) {
            return Err(StageError::AlreadyStagedUncommit(id));
        }

        let from_base = self
            .ledger
            .committed()
            .get(&id)
            .cloned()
            .ok_or(StageError::NotCommittedInBase(id))?;

        self.staged_uncommits.insert(id, ma_ref.handle());
        Ok(from_base)
    }

    pub fn move_assignment(
        &mut self,
        old: &'brand BrandedMoveableAssignment<'brand, 'a, T, C>,
        new_asg: Assignment<'a, T, C>,
    ) -> Result<BrandedMoveableAssignment<'brand, 'a, T, C>, StageError> {
        self.uncommit_assignment(old)?;
        self.commit_assignment(&new_asg)
    }

    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = FixedHandle<'brand>> + '_ {
        self.ledger.iter_fixed_handles()
    }

    #[inline]
    pub fn iter_fixed_assignments(
        &'_ self,
    ) -> impl Iterator<Item = &'_ FixedAssignment<'_, T, C>> + '_ {
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
    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = &BrandedMoveableAssignment<'brand, 'a, T, C>> + '_ {
        let base_visible = self.ledger.iter_movable_assignments().filter(move |ma| {
            let id = ma.id();
            !self.staged_uncommits.contains_key(&id) && !self.staged_commits.contains_key(&id)
        });

        let staged = self.staged_commits.values();
        base_visible.chain(staged)
    }

    #[inline]
    pub fn iter_staged_commits(
        &self,
    ) -> impl Iterator<Item = &BrandedMoveableAssignment<'brand, 'a, T, C>> {
        self.staged_commits.values()
    }

    #[inline]
    pub fn iter_staged_uncommits(&self) -> impl Iterator<Item = &MovableHandle<'brand>> {
        self.staged_uncommits.values()
    }

    pub fn iter_assignments(&'_ self) -> impl Iterator<Item = &'_ Assignment<'_, T, C>> + '_ {
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

    pub fn iter_unassigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMoveableRequest<'brand, 'a, T, C>> + '_ {
        self.ledger
            .problem
            .unassigned()
            .values()
            .filter(move |req| {
                let id = req.request().id();
                let base_has = self.ledger.committed.contains_key(&id);
                let staged_commit = self.staged_commits.contains_key(&id);
                let tombstoned = self.staged_uncommits.contains_key(&id);

                (!base_has || tombstoned) && !staged_commit
            })
            .map(|req| BrandedMoveableRequest::<'brand, 'a, T, C>::new(req))
    }

    pub fn iter_assigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMoveableRequest<'brand, 'a, T, C>> + '_ {
        self.ledger
            .problem
            .unassigned()
            .values()
            .filter(move |req| {
                let id = req.request().id();
                (self.ledger.committed.contains_key(&id)
                    && !self.staged_uncommits.contains_key(&id))
                    || self.staged_commits.contains_key(&id)
            })
            .map(|req| BrandedMoveableRequest::<'brand, 'a, T, C>::new(req))
    }
}

impl<'brand, 'a, T, C> Into<Solution<T, C>> for &AssignmentLedger<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
{
    fn into(self) -> Solution<T, C> {
        let decisions: HashMap<RequestId, Assignment<'static, T, C>> = self
            .iter_assignments()
            .map(|a| (a.request().id(), a.clone().into_owned()))
            .collect();
        Solution::from_assignments(decisions)
    }
}

impl<'brand, 'p, T, C> Into<Solution<T, C>> for &AssignmentLedgerOverlay<'brand, 'p, '_, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
{
    fn into(self) -> Solution<T, C> {
        let decisions: HashMap<RequestId, Assignment<'static, T, C>> = self
            .iter_assignments()
            .map(|a| (a.request().id(), a.clone().into_owned()))
            .collect();
        Solution::from_assignments(decisions)
    }
}

#[cfg(test)]
mod ledger_overlay_tests {
    use super::*;
    use dock_alloc_core::domain::{
        Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
    };
    use dock_alloc_model::{ProblemBuilder, Request};

    // ---------- helpers ----------

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

    fn ids<I: Iterator<Item = RequestId>>(it: I) -> Vec<RequestId> {
        let mut v: Vec<_> = it.collect();
        v.sort_by_key(|id| id.value());
        v
    }

    fn assert_id_sets_eq(mut a: Vec<RequestId>, mut b: Vec<RequestId>) {
        a.sort_by_key(|x| x.value());
        b.sort_by_key(|x| x.value());
        assert_eq!(a, b);
    }

    #[test]
    fn ledger_initial_iterators_ok() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
        let r1 = req_ok(1, 10, 5, 0, 100, 0, 100);
        let r2 = req_ok(2, 10, 5, 0, 100, 0, 100);
        let r3 = req_ok(3, 10, 5, 0, 100, 0, 100);
        let r_fixed = req_ok(10, 10, 5, 0, 100, 0, 100);

        b.add_unassigned_request(r1.clone()).unwrap();
        b.add_unassigned_request(r2.clone()).unwrap();
        b.add_unassigned_request(r3.clone()).unwrap();

        let fixed_a = Assignment::owned(r_fixed.clone(), SpacePosition::new(60), TimePoint::new(0));
        b.add_preassigned(FixedAssignment::new(fixed_a)).unwrap();

        let problem = b.build();
        let ledger = AssignmentLedger::from(&problem);

        let fixed_ids = ids(ledger.iter_fixed_handles().map(|h| h.id()));
        assert_eq!(fixed_ids, vec![RequestId::new(10)]);
        assert_eq!(ledger.iter_fixed_assignments().count(), 1);

        assert_eq!(ledger.iter_movable_handles().count(), 0);
        assert_eq!(ledger.iter_movable_assignments().count(), 0);

        let unassigned_ids = ids(ledger.iter_unassigned_requests().map(|mr| mr.id()));
        assert_eq!(unassigned_ids, vec![r1.id(), r2.id(), r3.id()]);
        let assigned_ids = ids(ledger.iter_assigned_requests().map(|mr| mr.id()));
        assert!(assigned_ids.is_empty());

        // all visible assignments = fixed only
        let all_a_ids = ids(ledger.iter_assignments().map(|a| a.request().id()));
        assert_eq!(all_a_ids, vec![r_fixed.id()]);
    }

    #[test]
    fn ledger_commit_and_iterators_update() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
        let r1 = req_ok(1, 10, 5, 0, 100, 0, 100);
        let r2 = req_ok(2, 10, 5, 0, 100, 0, 100);
        let r3 = req_ok(3, 10, 5, 0, 100, 0, 100);
        let r_fixed = req_ok(10, 10, 5, 0, 100, 0, 100);

        b.add_unassigned_request(r1.clone()).unwrap();
        b.add_unassigned_request(r2.clone()).unwrap();
        b.add_unassigned_request(r3.clone()).unwrap();
        b.add_preassigned(FixedAssignment::new(Assignment::owned(
            r_fixed.clone(),
            SpacePosition::new(60),
            TimePoint::new(0),
        )))
        .unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        let a1 = asg(&r1, 0, 0);
        let _ma1 = ledger.commit_assignment(&a1).expect("commit r1");

        let mov_ids = ids(ledger.iter_movable_handles().map(|h| h.id()));
        assert_eq!(mov_ids, vec![r1.id()]);

        let unassigned_ids = ids(ledger.iter_unassigned_requests().map(|mr| mr.id()));
        assert_eq!(unassigned_ids, vec![r2.id(), r3.id()]);
        let assigned_ids = ids(ledger.iter_assigned_requests().map(|mr| mr.id()));
        assert_eq!(assigned_ids, vec![r1.id()]);

        let all_a_ids = ids(ledger.iter_assignments().map(|a| a.request().id()));
        assert_eq!(all_a_ids, {
            let mut v = vec![r_fixed.id(), r1.id()];
            v.sort_by_key(|id| id.value());
            v
        });
    }

    #[test]
    fn overlay_uncommit_makes_request_unassigned_in_overlay_view() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
        let r1 = req_ok(1, 10, 5, 0, 100, 0, 100);
        let r2 = req_ok(2, 10, 5, 0, 100, 0, 100);
        let r_fixed = req_ok(10, 10, 5, 0, 100, 0, 100);

        b.add_unassigned_request(r1.clone()).unwrap();
        b.add_unassigned_request(r2.clone()).unwrap();
        b.add_preassigned(FixedAssignment::new(Assignment::owned(
            r_fixed.clone(),
            SpacePosition::new(60),
            TimePoint::new(0),
        )))
        .unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        let _ = ledger.commit_assignment(&asg(&r1, 0, 0)).unwrap();
        let _ = ledger.commit_assignment(&asg(&r2, 20, 0)).unwrap();

        let mut ov = AssignmentLedgerOverlay::new(&ledger);

        let base_ma1 = ledger.committed().get(&r1.id()).unwrap();
        let _ = ov.uncommit_assignment(base_ma1).expect("stage uncommit r1");

        let unassigned_ids = ids(ov.iter_unassigned_requests().map(|mr| mr.id()));
        assert!(unassigned_ids.contains(&r1.id()));

        let assigned_ids = ids(ov.iter_assigned_requests().map(|mr| mr.id()));
        assert!(assigned_ids.contains(&r2.id()));
        assert!(!assigned_ids.contains(&r1.id()));

        let visible_movable = ids(ov.iter_movable_handles().map(|h| h.id()));
        assert_eq!(visible_movable, vec![r2.id()]);

        let staged_uncommit = ids(ov.iter_staged_uncommits().map(|h| h.id()));
        assert_eq!(staged_uncommit, vec![r1.id()]);
        assert_eq!(ov.iter_staged_commits().count(), 0);
    }

    #[test]
    fn overlay_commit_hides_request_from_unassigned_in_overlay_view() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
        let r1 = req_ok(1, 10, 5, 0, 100, 0, 100);
        let r2 = req_ok(2, 10, 5, 0, 100, 0, 100);
        let r3 = req_ok(3, 10, 5, 0, 100, 0, 100);

        b.add_unassigned_request(r1.clone()).unwrap();
        b.add_unassigned_request(r2.clone()).unwrap();
        b.add_unassigned_request(r3.clone()).unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        let _ = ledger.commit_assignment(&asg(&r1, 0, 0)).unwrap();

        let mut ov = AssignmentLedgerOverlay::new(&ledger);
        let _ = ov
            .commit_assignment(&asg(&r2, 20, 0))
            .expect("stage commit r2");

        // unassigned in overlay should be {r3}
        let unassigned_ids = ids(ov.iter_unassigned_requests().map(|mr| mr.id()));
        assert_eq!(unassigned_ids, vec![r3.id()]);

        // assigned in overlay includes r1 (base) and r2 (staged)
        let assigned_ids = ids(ov.iter_assigned_requests().map(|mr| mr.id()));
        assert_eq!(assigned_ids, vec![r1.id(), r2.id()]);

        // visible movables in overlay: r1 + r2
        let mov_ids = ids(ov.iter_movable_handles().map(|h| h.id()));
        assert_eq!(mov_ids, vec![r1.id(), r2.id()]);
    }

    #[test]
    fn overlay_move_same_id_tombstones_then_readds_with_new_assignment() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
        let r1 = req_ok(1, 10, 5, 0, 100, 0, 100);

        b.add_unassigned_request(r1.clone()).unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        // base commit r1 at (0,0)
        let _ = ledger.commit_assignment(&asg(&r1, 0, 0)).unwrap();

        let mut ov = AssignmentLedgerOverlay::new(&ledger);
        let base_ma1 = ledger.committed().get(&r1.id()).unwrap();
        let new_asg = asg(&r1, 30, 10);
        let staged_ma = ov
            .move_assignment(base_ma1, new_asg.clone())
            .expect("stage move r1");

        // r1 is assigned in overlay (via staged commit)
        let unassigned_ids = ids(ov.iter_unassigned_requests().map(|mr| mr.id()));
        assert!(!unassigned_ids.contains(&r1.id()));

        let assigned_ids = ids(ov.iter_assigned_requests().map(|mr| mr.id()));
        assert!(assigned_ids.contains(&r1.id()));

        // net effect: no tombstone remains, only the new staged commit
        let staged_uncommit = ids(ov.iter_staged_uncommits().map(|h| h.id()));
        assert_eq!(staged_uncommit, Vec::<RequestId>::new());
        let staged_commit = ids(ov.iter_staged_commits().map(|ma| ma.id()));
        assert_eq!(staged_commit, vec![r1.id()]);

        // staged assignment matches new position/time
        assert_eq!(
            staged_ma.assignment().start_position(),
            SpacePosition::new(30)
        );
        assert_eq!(staged_ma.assignment().start_time(), TimePoint::new(10));
    }

    #[test]
    fn overlay_commit_conflict_when_already_in_base() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
        let r1 = req_ok(1, 10, 5, 0, 100, 0, 100);
        b.add_unassigned_request(r1.clone()).unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        let a1 = asg(&r1, 0, 0);
        let _ = ledger.commit_assignment(&a1).unwrap();

        let mut ov = AssignmentLedgerOverlay::new(&ledger);
        let err = ov.commit_assignment(&a1).unwrap_err();
        assert!(matches!(err, StageError::AlreadyCommittedInBase(id) if id == r1.id()));
    }

    #[test]
    fn overlay_uncommit_conflict_when_not_in_base() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
        let r1 = req_ok(1, 10, 5, 0, 100, 0, 100);
        b.add_unassigned_request(r1.clone()).unwrap();

        let problem = b.build();
        let ledger = AssignmentLedger::from(&problem);

        // dummy MA for r1 (not in base)
        let dummy_ma = BrandedMoveableAssignment {
            assignment: asg(&r1, 0, 0),
            handle: MovableHandle {
                id: r1.id(),
                _phantom: PhantomData,
            },
            _phantom: PhantomData,
        };

        let mut ov = AssignmentLedgerOverlay::new(&ledger);
        let err = ov.uncommit_assignment(&dummy_ma).unwrap_err();
        assert!(matches!(err, StageError::NotCommittedInBase(id) if id == r1.id()));
    }

    #[test]
    fn overlay_double_stage_rules() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
        let r1 = req_ok(1, 10, 5, 0, 100, 0, 100);
        b.add_unassigned_request(r1.clone()).unwrap();

        let problem = b.build();
        let ledger = AssignmentLedger::from(&problem);
        let mut ov = AssignmentLedgerOverlay::new(&ledger);

        // stage commit once
        let a1 = asg(&r1, 0, 0);
        let _ = ov.commit_assignment(&a1).expect("first staged commit");

        let _ = ov.commit_assignment(&a1).expect("same staged commit ok");

        let a1_alt = asg(&r1, 10, 0);
        let err = ov.commit_assignment(&a1_alt).unwrap_err();
        assert!(matches!(err, StageError::AlreadyStagedCommit(id) if id == r1.id()));

        // uncommit the staged id -> clears staged commit
        let staged = ov.iter_staged_commits().next().unwrap().clone();
        let _ = ov.uncommit_assignment(&staged).expect("stage uncommit");
        // second uncommit -> error
        let err2 = ov.uncommit_assignment(&staged).unwrap_err();
        assert!(matches!(err2, StageError::NotCommittedInBase(id) if id == r1.id()));
    }

    #[test]
    fn into_solution_from_ledger_and_overlay() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
        let r1 = req_ok(1, 10, 5, 0, 100, 0, 100);
        let r2 = req_ok(2, 10, 5, 0, 100, 0, 100);
        let r_fixed = req_ok(10, 10, 5, 0, 100, 0, 100);

        b.add_unassigned_request(r1.clone()).unwrap();
        b.add_unassigned_request(r2.clone()).unwrap();
        b.add_preassigned(FixedAssignment::new(Assignment::owned(
            r_fixed.clone(),
            SpacePosition::new(60),
            TimePoint::new(0),
        )))
        .unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        // base: commit r1
        let _ = ledger.commit_assignment(&asg(&r1, 0, 0)).unwrap();

        // ledger -> solution contains fixed + r1
        let sol_from_ledger: Solution<_, _> = (&ledger).into();
        let ids_from_ledger: Vec<_> = sol_from_ledger.decisions().keys().copied().collect();
        assert_id_sets_eq(ids_from_ledger, vec![r_fixed.id(), r1.id()]);

        // overlay: stage r2 on top
        let mut ov = AssignmentLedgerOverlay::new(&ledger);
        let _ = ov.commit_assignment(&asg(&r2, 20, 0)).unwrap();

        // overlay -> solution contains fixed + r1(base) + r2(staged)
        let sol_from_overlay: Solution<_, _> = (&ov).into();
        let ids_from_overlay: Vec<_> = sol_from_overlay.decisions().keys().copied().collect();
        assert_id_sets_eq(ids_from_overlay, vec![r_fixed.id(), r1.id(), r2.id()]);
    }
}
