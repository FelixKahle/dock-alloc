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

use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimeDelta, TimePoint};
use dock_alloc_model::{
    Assignment, FixedAssignment, MoveableRequest, Problem, RequestId, Solution,
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MovableAssignment<'brand, 'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    assignment: Assignment<'a, T, C>,
    handle: MovableHandle<'brand>,
    _phantom: PhantomData<&'brand ()>,
}

impl<'brand, 'a, T: PrimInt + Signed, C: PrimInt + Signed> MovableAssignment<'brand, 'a, T, C> {
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
    committed: HashMap<RequestId, MovableAssignment<'brand, 'a, T, C>>,
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
    pub fn committed(&self) -> &HashMap<RequestId, MovableAssignment<'brand, 'a, T, C>> {
        &self.committed
    }

    #[inline]
    pub fn commit_assignment(
        &mut self,
        assignment: &Assignment<'a, T, C>,
    ) -> Result<MovableAssignment<'brand, 'a, T, C>, LedgerError> {
        let id = assignment.request().id();
        if self.committed.contains_key(&id) {
            return Err(LedgerError::AlreadyCommitted);
        }

        debug_assert!(self.problem.unassigned().contains_key(&id));

        let h = MovableHandle {
            id,
            _phantom: PhantomData,
        };
        let ma = MovableAssignment {
            assignment: assignment.clone(),
            handle: h,
            _phantom: PhantomData,
        };
        self.committed.insert(id, ma.clone());
        Ok(ma)
    }

    #[inline]
    pub fn uncommit_assignment(
        &mut self,
        assignment: &'brand MovableAssignment<'brand, 'a, T, C>,
    ) -> Result<MovableAssignment<'brand, 'a, T, C>, LedgerError> {
        self.committed
            .remove(&assignment.id())
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
    ) -> impl Iterator<Item = &MovableAssignment<'brand, 'a, T, C>> + '_ {
        self.committed.values()
    }

    #[inline]
    pub fn iter_committed(&self) -> impl Iterator<Item = &MovableAssignment<'brand, 'a, T, C>> {
        self.committed.values()
    }

    #[inline]
    pub fn iter_unassigned_requests(&self) -> impl Iterator<Item = &MoveableRequest<T, C>> + '_ {
        self.problem
            .unassigned()
            .values()
            .filter(move |req| !self.committed.contains_key(&req.request().id()))
    }

    #[inline]
    pub fn iter_assigned_requests(&self) -> impl Iterator<Item = &MoveableRequest<T, C>> + '_ {
        self.problem
            .unassigned()
            .values()
            .filter(move |req| self.committed.contains_key(&req.request().id()))
    }

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
pub struct AssignmentOverlay<'brand, 'a, 'l, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    ledger: &'l AssignmentLedger<'brand, 'a, T, C>,
    staged_commits: BTreeMap<RequestId, MovableAssignment<'brand, 'a, T, C>>,
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

    pub fn commit_assignment(
        &mut self,
        assignment: &Assignment<'a, T, C>,
    ) -> Result<MovableAssignment<'brand, 'a, T, C>, StageError> {
        let id = assignment.request().id();
        let base_has = self.ledger.committed().contains_key(&id);
        let tombstoned = self.staged_uncommits.contains_key(&id);

        if base_has && !tombstoned {
            return Err(StageError::AlreadyCommittedInBase(id));
        }

        let new_ma = MovableAssignment {
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
        ma_ref: &'brand MovableAssignment<'brand, 'a, T, C>,
    ) -> Result<MovableAssignment<'brand, 'a, T, C>, StageError> {
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
        old: &'brand MovableAssignment<'brand, 'a, T, C>,
        new_asg: Assignment<'a, T, C>,
    ) -> Result<MovableAssignment<'brand, 'a, T, C>, StageError> {
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
    ) -> impl Iterator<Item = &MovableAssignment<'brand, 'a, T, C>> + '_ {
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
    ) -> impl Iterator<Item = &MovableAssignment<'brand, 'a, T, C>> {
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

    pub fn iter_unassigned_requests(&self) -> impl Iterator<Item = &MoveableRequest<T, C>> + '_ {
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
    }

    pub fn iter_assigned_requests(&self) -> impl Iterator<Item = &MoveableRequest<T, C>> + '_ {
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
    }
}

impl<'brand, 'a, T, C> From<&AssignmentLedger<'brand, 'a, T, C>> for Solution<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
{
    fn from(ledger: &AssignmentLedger<'brand, 'a, T, C>) -> Self {
        let decisions: HashMap<RequestId, Assignment<'static, T, C>> = ledger
            .iter_assignments()
            .map(|a| (a.request().id(), a.clone().into_owned()))
            .collect();
        Solution::from_assignments(decisions)
    }
}
