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

use dock_alloc_core::domain::{SpacePosition, TimePoint};
use dock_alloc_model::{
    AnyAssignmentRef, AssignmentRef, Fixed, FixedRequestId, Movable, MovableRequestId, Problem,
    Request, RequestId, SolutionRef,
};
use num_traits::{PrimInt, Signed};
use std::collections::{BTreeMap, HashMap};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentLedger<'a, T: PrimInt + Signed, C: PrimInt + Signed> {
    problem: &'a Problem<T, C>,
    committed: HashMap<MovableRequestId, AssignmentRef<'a, Movable, T, C>>,
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
    pub fn committed(&self) -> &HashMap<MovableRequestId, AssignmentRef<'a, Movable, T, C>> {
        &self.committed
    }

    /// Primary commit: by movable request and placement.
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
    pub fn apply(&mut self, overlay: AssignmentLedgerOverlay<'a, '_, T, C>) {
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

        for (id, asg) in overlay.staged_commits.into_iter() {
            let _prev = self.committed.insert(id, asg);
        }
    }

    #[inline]
    pub fn iter_fixed_ids(&self) -> impl Iterator<Item = &FixedRequestId> + '_ {
        self.problem.preassigned().keys()
    }

    #[inline]
    pub fn iter_fixed_assignments(
        &self,
    ) -> impl Iterator<Item = AssignmentRef<'a, Fixed, T, C>> + '_ {
        self.problem.preassigned().values().map(|a| a.as_ref())
    }

    #[inline]
    pub fn iter_movable_ids(&self) -> impl Iterator<Item = &MovableRequestId> + '_ {
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
            .map(|a| a.as_ref())
            .map(AnyAssignmentRef::from);
        let movable_iter = self.committed.values().copied().map(AnyAssignmentRef::from);
        fixed_iter.chain(movable_iter)
    }

    #[inline]
    pub fn overlay(&self) -> AssignmentLedgerOverlay<'a, '_, T, C> {
        AssignmentLedgerOverlay::new(self)
    }

    #[inline]
    pub fn with_overlay<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&AssignmentLedgerOverlay<'a, '_, T, C>) -> R,
    {
        let overlay = AssignmentLedgerOverlay::new(self);
        f(&overlay)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentLedgerOverlay<'a, 'l, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    ledger: &'l AssignmentLedger<'a, T, C>,
    staged_commits: BTreeMap<MovableRequestId, AssignmentRef<'a, Movable, T, C>>,
    staged_uncommits: BTreeMap<MovableRequestId, MovableRequestId>,
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

impl<'a, 'l, T, C> AssignmentLedgerOverlay<'a, 'l, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    pub fn new(ledger: &'l AssignmentLedger<'a, T, C>) -> Self {
        Self {
            ledger,
            staged_commits: BTreeMap::new(),
            staged_uncommits: BTreeMap::new(),
        }
    }

    #[inline]
    pub fn ledger(&self) -> &'l AssignmentLedger<'a, T, C> {
        self.ledger
    }

    pub fn commit_assignment(
        &mut self,
        req: &'a Request<Movable, T, C>,
        start_time: TimePoint<T>,
        start_position: SpacePosition,
    ) -> Result<AssignmentRef<'a, Movable, T, C>, StageError> {
        let id = req.typed_id();

        let base_has = self.ledger.committed().contains_key(&id);
        let tombstoned = self.staged_uncommits.contains_key(&id);
        if base_has && !tombstoned {
            return Err(StageError::AlreadyCommittedInBase(id));
        }

        let asg = AssignmentRef::new(req, start_position, start_time);

        if let Some(existing) = self.staged_commits.get(&id) {
            if *existing == asg {
                return Ok(*existing);
            }
            return Err(StageError::AlreadyStagedCommit(id));
        }

        self.staged_uncommits.remove(&id);
        self.staged_commits.insert(id, asg);
        Ok(asg)
    }

    #[inline]
    pub fn uncommit_assignment(
        &mut self,
        ma_ref: &AssignmentRef<'a, Movable, T, C>,
    ) -> Result<AssignmentRef<'a, Movable, T, C>, StageError>
    where
        'l: 'a,
    {
        let id = ma_ref.typed_id();
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
            *base
        };
        self.staged_uncommits.insert(id, id);
        Ok(asg)
    }

    /// Move an existing movable assignment to a new placement in the overlay.
    #[inline]
    pub fn move_assignment(
        &mut self,
        old: &AssignmentRef<'a, Movable, T, C>,
        new_asg: AssignmentRef<'a, Movable, T, C>,
    ) -> Result<AssignmentRef<'a, Movable, T, C>, StageError>
    where
        'l: 'a,
    {
        debug_assert_eq!(
            old.id(),
            new_asg.id(),
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
    pub fn iter_fixed_ids(&self) -> impl Iterator<Item = &FixedRequestId> + '_ {
        self.ledger.iter_fixed_ids()
    }

    #[inline]
    pub fn iter_fixed_assignments(
        &'_ self,
    ) -> impl Iterator<Item = AssignmentRef<'a, Fixed, T, C>> + '_ {
        self.ledger.iter_fixed_assignments()
    }

    #[inline]
    pub fn iter_movable_ids(&self) -> impl Iterator<Item = &MovableRequestId> + '_ {
        let base_visible = self.ledger.iter_movable_ids().filter(move |id| {
            !self.staged_uncommits.contains_key(id) && !self.staged_commits.contains_key(id)
        });

        let staged = self.staged_commits.keys();
        base_visible.chain(staged)
    }

    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = AssignmentRef<'a, Movable, T, C>> + '_ {
        let base_visible = self
            .ledger
            .iter_movable_assignments()
            .filter(move |ma| {
                let id = ma.typed_id();
                !self.staged_uncommits.contains_key(&id) && !self.staged_commits.contains_key(&id)
            })
            .copied();

        let staged = self.staged_commits.values().copied();
        base_visible.chain(staged)
    }

    #[inline]
    pub fn iter_staged_commits(&self) -> impl Iterator<Item = &AssignmentRef<'a, Movable, T, C>> {
        self.staged_commits.values()
    }

    #[inline]
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
            .copied()
            .map(AnyAssignmentRef::from);

        let staged = self
            .staged_commits
            .values()
            .copied()
            .map(AnyAssignmentRef::from);
        fixed.chain(base).chain(staged)
    }

    pub fn iter_unassigned_requests(&self) -> impl Iterator<Item = &Request<Movable, T, C>> + '_ {
        self.ledger.problem.movables().values().filter(move |req| {
            let id = req.typed_id();
            let base_has = self.ledger.committed.contains_key(&id);
            let staged_commit = self.staged_commits.contains_key(&id);
            let tombstoned = self.staged_uncommits.contains_key(&id);

            (!base_has || tombstoned) && !staged_commit
        })
    }

    pub fn iter_assigned_requests(&self) -> impl Iterator<Item = &Request<Movable, T, C>> + '_ {
        self.ledger.problem.movables().values().filter(move |req| {
            let id = req.typed_id();
            (self.ledger.committed.contains_key(&id) && !self.staged_uncommits.contains_key(&id))
                || self.staged_commits.contains_key(&id)
        })
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

impl<'p, 'l, T, C> From<&'l AssignmentLedgerOverlay<'p, 'l, T, C>> for SolutionRef<'l, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
{
    fn from(val: &'l AssignmentLedgerOverlay<'p, 'l, T, C>) -> Self {
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
    use dock_alloc_model::{Assignment, ProblemBuilder, RequestId};

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
    ) -> AssignmentRef<'r, Movable, Tm, Cm> {
        AssignmentRef::new(r, SpacePosition::new(pos), TimePoint::new(time))
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
            Assignment::<Fixed, _, _>::new(r_fixed.clone(), SpacePosition::new(60), 0.into());
        b.add_preassigned(fixed_a).unwrap();

        let problem = b.build();
        let ledger = AssignmentLedger::from(&problem);

        // fixed via handles (now &FixedRequestId -> RequestId)
        let fixed_ids = ids(ledger.iter_fixed_ids().map(|h| (*h).into()));
        assert_eq!(fixed_ids, vec![RequestId::new(10)]);
        assert_eq!(ledger.iter_fixed_assignments().count(), 1);

        assert_eq!(ledger.iter_movable_ids().count(), 0);
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
        let mov_ids = ids(ledger.iter_movable_ids().map(|h| (*h).into()));
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
        b.add_preassigned(Assignment::<Fixed, _, _>::new(
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

        // Get the committed assignment for r1 from the ledger
        let committed_r1 = *ledger
            .committed
            .get(&MovableRequestId::from(r1.id()))
            .unwrap();
        let _ = ov
            .uncommit_assignment(&committed_r1)
            .expect("stage uncommit r1");

        // overlay iterators use branded requests; get RequestId via .request().id()
        let unassigned_ids = ids(ov.iter_unassigned_requests().map(|mr| mr.id()));
        assert!(unassigned_ids.contains(&r1.id()));

        let assigned_ids = ids(ov.iter_assigned_requests().map(|mr| mr.id()));
        assert!(assigned_ids.contains(&r2.id()));
        assert!(!assigned_ids.contains(&r1.id()));

        // Check that r1 is staged for uncommit
        assert!(
            ov.staged_uncommits
                .contains_key(&MovableRequestId::from(r1.id()))
        );
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
        let unassigned_ids = ids(ov.iter_unassigned_requests().map(|mr| mr.id()));
        assert_eq!(unassigned_ids, vec![r3.id()]);

        // assigned in overlay includes r1 (base) and r2 (staged)
        let assigned_ids = ids(ov.iter_assigned_requests().map(|mr| mr.id()));
        assert_eq!(assigned_ids, vec![r1.id(), r2.id()]);

        // visible movables in overlay: r1 + r2
        let mov_ids = ids(ov.iter_movable_assignments().map(|a| a.id()));
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

        // Get the committed assignment for r1 from the ledger to drive the move
        let committed_r1 = *ledger
            .committed
            .get(&MovableRequestId::from(r1.id()))
            .unwrap();

        let new_asg = asg(&r1, 30, 10);
        let staged_ma = ov
            .move_assignment(&committed_r1, new_asg.clone())
            .expect("stage move r1");

        // r1 is assigned in overlay (via staged commit)
        let unassigned_ids = ids(ov.iter_unassigned_requests().map(|mr| mr.id()));
        assert!(!unassigned_ids.contains(&r1.id()));

        let assigned_ids = ids(ov.iter_assigned_requests().map(|mr| mr.id()));
        assert!(assigned_ids.contains(&r1.id()));

        // net effect: no tombstone remains, only the new staged commit
        assert!(ov.staged_uncommits.is_empty());
        let staged_commit = ids(ov.iter_staged_commits().map(|ma| ma.id()));
        assert_eq!(staged_commit, vec![r1.id()]);

        // staged assignment matches new position/time
        assert_eq!(staged_ma.start_position(), SpacePosition::new(30));
        assert_eq!(staged_ma.start_time(), TimePoint::new(10));
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

        // Dummy assignment for r1 (not present in base)
        let dummy_ma = asg(&r1, 0, 0);

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
        let staged = *ov.iter_staged_commits().next().unwrap();
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
        b.add_preassigned(Assignment::<Fixed, _, _>::new(
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
