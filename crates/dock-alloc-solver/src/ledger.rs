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

use dock_alloc_core::{
    domain::{Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint},
    marker::Brand,
};
use dock_alloc_model::{
    AnyAssignmentRef, Assignment, Fixed, FixedRequestId, Movable, MovableRequestId, Problem,
    Request, RequestId, SolutionRef,
};
use num_traits::{PrimInt, Signed};
use std::collections::{BTreeMap, HashMap};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BrandedMovableRequestId<'brand> {
    id: MovableRequestId,
    _brand: Brand<'brand>,
}

impl<'brand> BrandedMovableRequestId<'brand> {
    #[inline]
    fn new(id: MovableRequestId) -> Self {
        Self {
            id,
            _brand: Brand::new(),
        }
    }

    #[inline]
    pub fn id(self) -> MovableRequestId {
        self.id
    }
}

impl<'brand> std::fmt::Display for BrandedMovableRequestId<'brand> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MovableHandle({})", self.id)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BrandedFixedRequestId<'brand> {
    id: FixedRequestId,
    _brand: Brand<'brand>,
}

impl<'brand> BrandedFixedRequestId<'brand> {
    #[inline]
    fn new(id: FixedRequestId) -> Self {
        Self {
            id,
            _brand: Brand::new(),
        }
    }

    #[inline]
    pub fn id(self) -> FixedRequestId {
        self.id
    }
}

impl<'brand> std::fmt::Display for BrandedFixedRequestId<'brand> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FixedHandle({})", self.id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BrandedMovableRequest<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    inner: &'a Request<Movable, T, C>,
    _brand: Brand<'brand>,
}

impl<'brand, 'a, T, C> BrandedMovableRequest<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(inner: &'a Request<Movable, T, C>) -> Self {
        Self {
            inner,
            _brand: Brand::new(),
        }
    }

    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.inner.length()
    }

    #[inline]
    pub fn arrival_time(&self) -> TimePoint<T> {
        self.inner.arrival_time()
    }

    #[inline]
    pub fn processing_duration(&self) -> TimeDelta<T> {
        self.inner.processing_duration()
    }

    #[inline]
    pub fn target_position(&self) -> SpacePosition {
        self.inner.target_position()
    }

    #[inline]
    pub fn cost_per_delay(&self) -> Cost<C> {
        self.inner.cost_per_delay()
    }

    #[inline]
    pub fn cost_per_position_deviation(&self) -> Cost<C> {
        self.inner.cost_per_position_deviation()
    }

    #[inline]
    pub fn feasible_time_window(&self) -> TimeInterval<T> {
        self.inner.feasible_time_window()
    }

    #[inline]
    pub fn feasible_space_window(&self) -> SpaceInterval {
        self.inner.feasible_space_window()
    }

    #[inline]
    pub fn request(&self) -> &'a Request<Movable, T, C> {
        self.inner
    }

    #[inline]
    pub fn id(&self) -> MovableRequestId {
        self.inner.typed_id()
    }

    #[inline]
    pub fn handle(&self) -> BrandedMovableRequestId<'brand> {
        BrandedMovableRequestId::new(self.id())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BrandedMovableAssignment<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    assignment: Assignment<'a, Movable, T, C>,
    _brand: Brand<'brand>,
}

impl<'brand, 'a, T, C> BrandedMovableAssignment<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(assignment: Assignment<'a, Movable, T, C>) -> Self {
        Self {
            assignment,
            _brand: Brand::new(),
        }
    }

    #[inline]
    pub fn assignment(&'_ self) -> &'_ Assignment<'_, Movable, T, C> {
        &self.assignment
    }

    #[inline]
    pub fn start_position(&self) -> SpacePosition {
        self.assignment.start_position()
    }

    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.assignment.start_time()
    }

    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.assignment.request().length()
    }

    #[inline]
    pub fn processing_duration(&self) -> TimeDelta<T> {
        self.assignment.request().processing_duration()
    }

    #[inline]
    pub fn id(&self) -> MovableRequestId {
        self.assignment().typed_id()
    }

    #[inline]
    pub fn handle(&self) -> BrandedMovableRequestId<'brand> {
        BrandedMovableRequestId::new(self.id())
    }
}

impl<'brand, 'a, T, C> From<BrandedMovableAssignment<'brand, 'a, T, C>>
    for Assignment<'a, Movable, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn from(val: BrandedMovableAssignment<'brand, 'a, T, C>) -> Self {
        val.assignment
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentLedger<'a, T: PrimInt + Signed + 'static, C: PrimInt + Signed + 'static> {
    problem: &'a Problem<T, C>,
    committed: HashMap<MovableRequestId, Assignment<'a, Movable, T, C>>,
}

impl<'a, T, C> From<&'a Problem<T, C>> for AssignmentLedger<'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
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

impl<'a, T, C> AssignmentLedger<'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
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
    pub fn committed(&self) -> &HashMap<MovableRequestId, Assignment<'a, Movable, T, C>> {
        &self.committed
    }

    /// Primary commit: by movable request and placement.
    #[inline]
    pub fn commit_assignment(
        &mut self,
        req: &'a Request<Movable, T, C>,
        start_time: TimePoint<T>,
        start_position: SpacePosition,
    ) -> Result<Assignment<'a, Movable, T, C>, LedgerError> {
        let id = req.typed_id();
        if self.committed.contains_key(&id) {
            return Err(LedgerError::AlreadyCommitted);
        }

        let assignment = Assignment::borrowed(req, start_position, start_time);
        self.committed.insert(id, assignment.clone());
        Ok(assignment)
    }

    #[inline]
    pub fn uncommit_assignment(
        &mut self,
        assignment: &Assignment<'a, Movable, T, C>,
    ) -> Result<Assignment<'a, Movable, T, C>, LedgerError> {
        self.committed
            .remove(&assignment.typed_id())
            .ok_or(LedgerError::NotCommitted)
    }

    #[inline]
    pub fn apply<'brand>(&mut self, overlay: AssignmentLedgerOverlay<'brand, 'a, '_, T, C>)
    where
        'brand: 'a,
    {
        // Ensure the overlay was created from this ledger
        debug_assert!(
            std::ptr::eq(self as *const _, overlay.ledger as *const _),
            "attempted to apply an overlay built from a different ledger"
        );

        for (id, _) in overlay.staged_uncommits.into_iter() {
            if !overlay.staged_commits.contains_key(&id) {
                let _ = self.committed.remove(&id);
            }
        }

        for (id, bma) in overlay.staged_commits.into_iter() {
            let asg: Assignment<'a, Movable, T, C> = bma.into();
            let _prev = self.committed.insert(id, asg);
        }
    }

    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = &FixedRequestId> + '_ {
        self.problem.preassigned().keys()
    }

    #[inline]
    pub fn iter_fixed_assignments(
        &self,
    ) -> impl Iterator<Item = &'_ Assignment<'_, Fixed, T, C>> + '_ {
        self.problem.preassigned().values()
    }

    #[inline]
    pub fn iter_movable_handles(&self) -> impl Iterator<Item = &MovableRequestId> + '_ {
        self.committed.keys()
    }

    #[inline]
    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = &Assignment<'a, Movable, T, C>> + '_ {
        self.committed.values()
    }

    #[inline]
    pub fn iter_committed(&self) -> impl Iterator<Item = &Assignment<'a, Movable, T, C>> {
        self.committed.values()
    }

    #[inline]
    pub fn iter_unassigned_requests(&self) -> impl Iterator<Item = &Request<Movable, T, C>> + '_ {
        self.problem
            .movables()
            .values()
            .filter(move |req| !self.committed.contains_key(&req.typed_id()))
    }

    #[inline]
    pub fn iter_assigned_requests(&self) -> impl Iterator<Item = &Request<Movable, T, C>> + '_ {
        self.problem
            .movables()
            .values()
            .filter(move |req| self.committed.contains_key(&req.typed_id()))
    }

    #[inline]
    pub fn iter_assignments(&self) -> impl Iterator<Item = AnyAssignmentRef<'_, T, C>> + '_ {
        let fixed_iter = self
            .problem
            .preassigned()
            .values()
            .map(AnyAssignmentRef::from);
        let movable_iter = self.committed.values().map(AnyAssignmentRef::from);
        fixed_iter.chain(movable_iter)
    }

    #[inline]
    pub fn overlay(&self) -> AssignmentLedgerOverlay<'_, 'a, '_, T, C> {
        AssignmentLedgerOverlay::new(self)
    }

    #[inline]
    pub fn with_overlay<F, R>(&self, f: F) -> R
    where
        F: for<'brand> FnOnce(&AssignmentLedgerOverlay<'brand, 'a, '_, T, C>) -> R,
    {
        let overlay = AssignmentLedgerOverlay::new(self);
        f(&overlay)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentLedgerOverlay<'brand, 'a, 'l, T, C>
where
    T: PrimInt + Signed + 'static,
    C: PrimInt + Signed + 'static,
{
    ledger: &'l AssignmentLedger<'a, T, C>,
    staged_commits: BTreeMap<MovableRequestId, BrandedMovableAssignment<'brand, 'a, T, C>>,
    staged_uncommits: BTreeMap<MovableRequestId, BrandedMovableRequestId<'brand>>,
    _brand: Brand<'brand>,
}

/// Errors that can occur during overlay staging operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StageError {
    AlreadyCommittedInBase(MovableRequestId),
    AlreadyStagedCommit(MovableRequestId),
    AlreadyStagedUncommit(MovableRequestId),
    NotCommittedInBase(MovableRequestId),
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
    pub fn new(ledger: &'l AssignmentLedger<'a, T, C>) -> Self {
        Self {
            ledger,
            staged_commits: BTreeMap::new(),
            staged_uncommits: BTreeMap::new(),
            _brand: Brand::new(),
        }
    }

    pub fn commit_assignment(
        &mut self,
        req: &'a Request<Movable, T, C>,
        start_time: TimePoint<T>,
        start_position: SpacePosition,
    ) -> Result<BrandedMovableAssignment<'brand, 'a, T, C>, StageError> {
        let id = req.typed_id();

        let base_has = self.ledger.committed().contains_key(&id);
        let tombstoned = self.staged_uncommits.contains_key(&id);
        if base_has && !tombstoned {
            return Err(StageError::AlreadyCommittedInBase(id));
        }

        let asg = Assignment::borrowed(req, start_position, start_time);

        if let Some(existing) = self.staged_commits.get(&id) {
            if existing.assignment == asg {
                return Ok(existing.clone());
            }
            return Err(StageError::AlreadyStagedCommit(id));
        }

        self.staged_uncommits.remove(&id);
        let new_bma = BrandedMovableAssignment::new(asg);
        self.staged_commits.insert(id, new_bma.clone());
        Ok(new_bma)
    }

    #[inline]
    pub fn uncommit_assignment(
        &mut self,
        ma_ref: &'brand BrandedMovableAssignment<'brand, 'a, T, C>,
    ) -> Result<BrandedMovableAssignment<'brand, 'a, T, C>, StageError>
    where
        'l: 'a,
    {
        let id = ma_ref.id();
        if let Some(staged) = self.staged_commits.remove(&id) {
            return Ok(staged);
        }

        if self.staged_uncommits.contains_key(&id) {
            return Err(StageError::AlreadyStagedUncommit(id));
        }

        let asg = {
            let base = self
                .ledger
                .committed()
                .get(&id)
                .ok_or(StageError::NotCommittedInBase(id))?;
            base.clone()
        };
        self.staged_uncommits.insert(id, ma_ref.handle());
        Ok(BrandedMovableAssignment::new(asg))
    }

    /// Move an existing movable assignment to a new placement in the overlay.
    #[inline]
    pub fn move_assignment(
        &mut self,
        old: &'brand BrandedMovableAssignment<'brand, 'a, T, C>,
        new_asg: Assignment<'a, Movable, T, C>,
    ) -> Result<BrandedMovableAssignment<'brand, 'a, T, C>, StageError>
    where
        'l: 'a,
    {
        debug_assert_eq!(
            old.id(),
            new_asg.typed_id(),
            "move_assignment(): request id mismatch"
        );

        self.uncommit_assignment(old)?;
        let mid: MovableRequestId = new_asg.typed_id();
        let req = self
            .ledger
            .problem
            .get_movable(mid)
            .expect("move_assignment: unknown movable request id");
        self.commit_assignment(req, new_asg.start_time(), new_asg.start_position())
    }

    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = BrandedFixedRequestId<'brand>> + '_ {
        self.ledger
            .iter_fixed_handles()
            .map(|id| BrandedFixedRequestId::new(*id))
    }

    #[inline]
    pub fn iter_fixed_assignments(
        &'_ self,
    ) -> impl Iterator<Item = &'_ Assignment<'_, Fixed, T, C>> + '_ {
        self.ledger.iter_fixed_assignments()
    }

    #[inline]
    pub fn iter_movable_handles(
        &self,
    ) -> impl Iterator<Item = BrandedMovableRequestId<'brand>> + '_ {
        let base_visible = self
            .ledger
            .iter_committed()
            .filter(move |ma| {
                let id = ma.typed_id();
                !self.staged_uncommits.contains_key(&id) && !self.staged_commits.contains_key(&id)
            })
            .map(|ma| BrandedMovableRequestId::new(ma.typed_id()));

        let staged = self.staged_commits.values().map(|ma| ma.handle());
        base_visible.chain(staged)
    }

    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = BrandedMovableAssignment<'brand, 'a, T, C>> + '_
    where
        'l: 'a,
    {
        let base_visible = self
            .ledger
            .iter_movable_assignments()
            .filter(move |ma| {
                let id = ma.typed_id();
                !self.staged_uncommits.contains_key(&id) && !self.staged_commits.contains_key(&id)
            })
            .map(|ma| BrandedMovableAssignment::new(ma.clone()));

        let staged = self.staged_commits.values().cloned();
        base_visible.chain(staged)
    }

    #[inline]
    pub fn iter_staged_commits(
        &self,
    ) -> impl Iterator<Item = &BrandedMovableAssignment<'brand, 'a, T, C>> {
        self.staged_commits.values()
    }

    #[inline]
    pub fn iter_staged_uncommits(&self) -> impl Iterator<Item = &BrandedMovableRequestId<'brand>> {
        self.staged_uncommits.values()
    }

    pub fn iter_assignments(&'_ self) -> impl Iterator<Item = AnyAssignmentRef<'_, T, C>> + '_ {
        let fixed = self
            .ledger
            .iter_fixed_assignments()
            .map(AnyAssignmentRef::from);
        let base = self
            .ledger
            .iter_movable_assignments()
            .filter(move |ma| {
                let id = ma.typed_id();
                !self.staged_uncommits.contains_key(&id) && !self.staged_commits.contains_key(&id)
            })
            .map(AnyAssignmentRef::from);
        let staged = self
            .staged_commits
            .values()
            .map(|bma| AnyAssignmentRef::from(bma.assignment()));
        fixed.chain(base).chain(staged)
    }

    pub fn iter_unassigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMovableRequest<'brand, 'a, T, C>> + '_ {
        self.ledger
            .problem
            .movables()
            .values()
            .filter(move |req| {
                let id = req.typed_id();
                let base_has = self.ledger.committed.contains_key(&id);
                let staged_commit = self.staged_commits.contains_key(&id);
                let tombstoned = self.staged_uncommits.contains_key(&id);

                (!base_has || tombstoned) && !staged_commit
            })
            .map(|req| BrandedMovableRequest::<'brand, 'a, T, C>::new(req))
    }

    pub fn iter_assigned_requests(
        &self,
    ) -> impl Iterator<Item = BrandedMovableRequest<'brand, 'a, T, C>> + '_ {
        self.ledger
            .problem
            .movables()
            .values()
            .filter(move |req| {
                let id = req.typed_id();
                (self.ledger.committed.contains_key(&id)
                    && !self.staged_uncommits.contains_key(&id))
                    || self.staged_commits.contains_key(&id)
            })
            .map(|req| BrandedMovableRequest::<'brand, 'a, T, C>::new(req))
    }
}

impl<'a, 'l, T, C> From<&'l AssignmentLedger<'a, T, C>> for SolutionRef<'l, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
{
    fn from(val: &'l AssignmentLedger<'a, T, C>) -> Self {
        let decisions: HashMap<RequestId, AnyAssignmentRef<'l, T, C>> =
            val.iter_assignments().map(|a| (a.id(), a)).collect();
        SolutionRef::from_assignments(decisions)
    }
}

impl<'brand, 'p, 'l, T, C> From<&'l AssignmentLedgerOverlay<'brand, 'p, 'l, T, C>>
    for SolutionRef<'l, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
{
    fn from(val: &'l AssignmentLedgerOverlay<'brand, 'p, 'l, T, C>) -> Self {
        let decisions: HashMap<RequestId, AnyAssignmentRef<'l, T, C>> =
            val.iter_assignments().map(|a| (a.id(), a)).collect();
        SolutionRef::from_assignments(decisions)
    }
}

#[cfg(test)]
mod ledger_overlay_tests {
    use super::*;
    use dock_alloc_core::domain::{
        Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
    };
    use dock_alloc_model::{ProblemBuilder, RequestId};

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

    fn req_fixed_ok(
        id: u64,
        len: usize,
        proc_t: i64,
        t0: i64,
        t1: i64,
        s0: usize,
        s1: usize,
    ) -> Request<Fixed, Tm, Cm> {
        Request::<Fixed, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimeDelta::new(proc_t),
            SpacePosition::new(s0),
            Cost::new(1),
            Cost::new(1),
            TimeInterval::new(TimePoint::new(t0), TimePoint::new(t1)),
            SpaceInterval::new(SpacePosition::new(s0), SpacePosition::new(s1)),
        )
        .expect("valid fixed request")
    }

    fn asg<'r>(
        r: &'r Request<Movable, Tm, Cm>,
        pos: usize,
        time: i64,
    ) -> Assignment<'r, Movable, Tm, Cm> {
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
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 100);
        let r2 = req_movable_ok(2, 10, 5, 0, 100, 0, 100);
        let r3 = req_movable_ok(3, 10, 5, 0, 100, 0, 100);
        let r_fixed = req_fixed_ok(10, 10, 5, 0, 100, 0, 100);

        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();
        b.add_movable_request(r3.clone()).unwrap();

        let fixed_a =
            Assignment::<Fixed, _, _>::owned(r_fixed.clone(), SpacePosition::new(60), 0.into());
        b.add_preassigned(fixed_a).unwrap();

        let problem = b.build();
        let ledger = AssignmentLedger::from(&problem);

        // fixed via handles (now &FixedRequestId -> RequestId)
        let fixed_ids = ids(ledger.iter_fixed_handles().map(|h| (*h).into()));
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
    fn ledger_commit_and_iterators_update() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 100);
        let r2 = req_movable_ok(2, 10, 5, 0, 100, 0, 100);
        let r3 = req_movable_ok(3, 10, 5, 0, 100, 0, 100);
        let r_fixed = req_fixed_ok(10, 10, 5, 0, 100, 0, 100);

        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();
        b.add_movable_request(r3.clone()).unwrap();
        b.add_preassigned(Assignment::<Fixed, _, _>::owned(
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

    #[test]
    fn overlay_uncommit_makes_request_unassigned_in_overlay_view() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 100);
        let r2 = req_movable_ok(2, 10, 5, 0, 100, 0, 100);
        let r_fixed = req_fixed_ok(10, 10, 5, 0, 100, 0, 100);

        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();
        b.add_preassigned(Assignment::<Fixed, _, _>::owned(
            r_fixed.clone(),
            SpacePosition::new(60),
            TimePoint::new(0),
        ))
        .unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        let mov1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let mov2 = problem
            .get_movable(MovableRequestId::from(r2.id()))
            .unwrap();
        let _ = ledger.commit_assignment(mov1, 0.into(), 0.into()).unwrap();
        let _ = ledger.commit_assignment(mov2, 20.into(), 0.into()).unwrap();

        let mut ov = AssignmentLedgerOverlay::new(&ledger);

        // Build a branded assignment for r1 (only the id matters for uncommit)
        let branded_r1 = BrandedMovableAssignment::new(asg(&r1, 0, 0));
        let _ = ov
            .uncommit_assignment(&branded_r1)
            .expect("stage uncommit r1");

        // overlay iterators use branded requests; get RequestId via .request().id()
        let unassigned_ids = ids(ov.iter_unassigned_requests().map(|mr| mr.request().id()));
        assert!(unassigned_ids.contains(&r1.id()));

        let assigned_ids = ids(ov.iter_assigned_requests().map(|mr| mr.request().id()));
        assert!(assigned_ids.contains(&r2.id()));
        assert!(!assigned_ids.contains(&r1.id()));

        // overlay handles are branded; convert to RequestId
        let visible_movable = ids(ov.iter_movable_handles().map(|h| h.id().into()));
        assert_eq!(visible_movable, vec![r2.id()]);

        // staged tombstone set contains r1
        let staged_uncommit = ids(ov.iter_staged_uncommits().map(|h| h.id().into()));
        assert_eq!(staged_uncommit, vec![r1.id()]);
        assert_eq!(ov.iter_staged_commits().count(), 0);
    }

    #[test]
    fn overlay_commit_hides_request_from_unassigned_in_overlay_view() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 100);
        let r2 = req_movable_ok(2, 10, 5, 0, 100, 0, 100);
        let r3 = req_movable_ok(3, 10, 5, 0, 100, 0, 100);

        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();
        b.add_movable_request(r3.clone()).unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        let mov1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let _ = ledger.commit_assignment(mov1, 0.into(), 0.into()).unwrap();

        let mov2 = problem
            .get_movable(MovableRequestId::from(r2.id()))
            .unwrap();
        let mut ov = AssignmentLedgerOverlay::new(&ledger);
        let _ = ov
            .commit_assignment(mov2, 20.into(), 0.into())
            .expect("stage commit r2");

        // unassigned in overlay should be {r3}
        let unassigned_ids = ids(ov.iter_unassigned_requests().map(|mr| mr.request().id()));
        assert_eq!(unassigned_ids, vec![r3.id()]);

        // assigned in overlay includes r1 (base) and r2 (staged)
        let assigned_ids = ids(ov.iter_assigned_requests().map(|mr| mr.request().id()));
        assert_eq!(assigned_ids, vec![r1.id(), r2.id()]);

        // visible movables in overlay: r1 + r2
        let mov_ids = ids(ov.iter_movable_handles().map(|h| h.id().into()));
        assert_eq!(mov_ids, vec![r1.id(), r2.id()]);
    }

    #[test]
    fn overlay_move_same_id_tombstones_then_readds_with_new_assignment() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 100);

        b.add_movable_request(r1.clone()).unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        // base commit r1 at (0,0) — using the assignment-based commit shim
        let mov1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let _ = ledger.commit_assignment(&mov1, 0.into(), 0.into()).unwrap();

        let mut ov = AssignmentLedgerOverlay::new(&ledger);

        // Construct branded "old" for r1 to drive the move
        let base_bma = BrandedMovableAssignment::new(asg(&r1, 0, 0));

        let new_asg = asg(&r1, 30, 10);
        let staged_ma = ov
            .move_assignment(&base_bma, new_asg.clone())
            .expect("stage move r1");

        // r1 is assigned in overlay (via staged commit)
        let unassigned_ids = ids(ov.iter_unassigned_requests().map(|mr| mr.request().id()));
        assert!(!unassigned_ids.contains(&r1.id()));

        let assigned_ids = ids(ov.iter_assigned_requests().map(|mr| mr.request().id()));
        assert!(assigned_ids.contains(&r1.id()));

        // net effect: no tombstone remains, only the new staged commit
        let staged_uncommit = ids(ov.iter_staged_uncommits().map(|h| h.id().into()));
        assert_eq!(staged_uncommit, Vec::<RequestId>::new());
        let staged_commit = ids(ov.iter_staged_commits().map(|ma| ma.id().into()));
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
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 100);
        b.add_movable_request(r1.clone()).unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        let a1 = asg(&r1, 0, 0);

        let mov1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let _ = ledger
            .commit_assignment(mov1, a1.start_time(), a1.start_position())
            .unwrap();

        let req1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let mut ov = AssignmentLedgerOverlay::new(&ledger);
        // overlay commit should see it's already in base
        let err = ov
            .commit_assignment(req1, a1.start_time(), a1.start_position())
            .unwrap_err();
        assert!(
            matches!(err, StageError::AlreadyCommittedInBase(id) if id == MovableRequestId::from(r1.id()))
        );
    }

    #[test]
    fn overlay_uncommit_conflict_when_not_in_base() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 100);
        b.add_movable_request(r1.clone()).unwrap();

        let problem = b.build();
        let ledger = AssignmentLedger::from(&problem);

        // Dummy branded assignment for r1 (not present in base)
        let dummy_ma = BrandedMovableAssignment::new(asg(&r1, 0, 0));

        let mut ov = AssignmentLedgerOverlay::new(&ledger);
        let err = ov.uncommit_assignment(&dummy_ma).unwrap_err();
        assert!(
            matches!(err, StageError::NotCommittedInBase(id) if id == MovableRequestId::from(r1.id()))
        );
    }

    #[test]
    fn overlay_double_stage_rules() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 100);
        b.add_movable_request(r1.clone()).unwrap();

        let problem = b.build();
        let ledger = AssignmentLedger::from(&problem);
        let mut ov = AssignmentLedgerOverlay::new(&ledger);

        let req1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();

        // stage commit once
        let a1 = asg(&r1, 0, 0);
        let _ = ov
            .commit_assignment(req1, a1.start_time(), a1.start_position())
            .expect("first staged commit");

        // stage the exact same assignment again -> ok (idempotent)
        let _ = ov
            .commit_assignment(req1, a1.start_time(), a1.start_position())
            .expect("same staged commit ok");

        // stage a different one for the same id -> error
        let a1_alt = asg(&r1, 10, 0);
        let err = ov
            .commit_assignment(req1, a1_alt.start_time(), a1_alt.start_position())
            .unwrap_err();
        assert!(
            matches!(err, StageError::AlreadyStagedCommit(id) if id == MovableRequestId::from(r1.id()))
        );

        // uncommit the staged id -> clears staged commit
        let staged = ov.iter_staged_commits().next().unwrap().clone();
        let _ = ov.uncommit_assignment(&staged).expect("stage uncommit");

        // second uncommit -> error (not in base, no staged)
        let err2 = ov.uncommit_assignment(&staged).unwrap_err();
        assert!(
            matches!(err2, StageError::NotCommittedInBase(id) if id == MovableRequestId::from(r1.id()))
        );
    }

    #[test]
    fn into_solution_from_ledger_and_overlay() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 100);
        let r2 = req_movable_ok(2, 10, 5, 0, 100, 0, 100);
        let r_fixed = req_fixed_ok(10, 10, 5, 0, 100, 0, 100);

        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();
        b.add_preassigned(Assignment::<Fixed, _, _>::owned(
            r_fixed.clone(),
            SpacePosition::new(60),
            TimePoint::new(0),
        ))
        .unwrap();

        let problem = b.build();
        let mut ledger = AssignmentLedger::from(&problem);

        // base: commit r1 (assignment-based commit shim)
        let mov1 = problem
            .get_movable(MovableRequestId::from(r1.id()))
            .unwrap();
        let _ = ledger.commit_assignment(mov1, 0.into(), 0.into()).unwrap();

        // ledger -> solution contains fixed + r1
        let sol_from_ledger: SolutionRef<_, _> = (&ledger).into();
        let ids_from_ledger: Vec<_> = sol_from_ledger.decisions().keys().copied().collect();
        assert_id_sets_eq(ids_from_ledger, vec![r_fixed.id(), r1.id()]);

        // overlay: stage r2 on top
        let mut ov = AssignmentLedgerOverlay::new(&ledger);
        let req2 = problem
            .get_movable(MovableRequestId::from(r2.id()))
            .unwrap();
        let _ = ov.commit_assignment(req2, 0.into(), 20.into()).unwrap();

        // overlay -> solution contains fixed + r1(base) + r2(staged)
        let sol_from_overlay: SolutionRef<_, _> = (&ov).into();
        let ids_from_overlay: Vec<_> = sol_from_overlay.decisions().keys().copied().collect();
        assert_id_sets_eq(ids_from_overlay, vec![r_fixed.id(), r1.id(), r2.id()]);
    }
}
