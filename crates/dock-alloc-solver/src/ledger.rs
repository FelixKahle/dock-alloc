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

use dock_alloc_model::{
    Assignment, FixedAssignment, MoveableRequest, Problem, RequestId, Solution,
};
use num_traits::{PrimInt, Signed};
use std::{
    collections::{BTreeMap, HashMap},
    marker::PhantomData,
};

/// A handle to a movable assignment that can be committed to or uncommitted from a ledger.
///
/// This handle provides type-safe access to movable assignments within the context of
/// a specific assignment ledger. The lifetime parameter `'brand` ensures that handles
/// cannot be mixed between different ledger instances.
///
/// Handles are typically obtained from ledger operations and cannot be constructed directly.
/// They serve as a type-safe way to reference specific assignments for uncommit operations.
///
/// # Examples
///
/// ```
/// use dock_alloc_solver::ledger::AssignmentLedger;
/// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
/// use dock_alloc_core::domain::*;
///
/// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
/// let request = Request::new(
///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
/// ).unwrap();
/// builder.add_unassigned_request(request).unwrap();
/// let problem = builder.build();
///
/// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
/// // Handles are obtained from iter_movable_handles() after committing assignments
/// let handles: Vec<_> = ledger.iter_movable_handles().collect();
/// assert_eq!(handles.len(), 0); // No assignments committed yet
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MovableHandle<'brand> {
    id: RequestId,
    _phantom: PhantomData<&'brand ()>,
}

impl<'brand> MovableHandle<'brand> {
    /// Returns the request ID associated with this handle.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(42), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// for handle in ledger.iter_movable_handles() {
    ///     let id = handle.id();
    ///     assert_eq!(id, RequestId::new(42));
    /// }
    /// ```
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

/// A handle to a fixed (pre-assigned) assignment in the problem definition.
///
/// Fixed assignments cannot be modified during solving - they represent constraints
/// that must be respected. The lifetime parameter `'brand` ensures type safety
/// across different ledger instances.
///
/// These handles are obtained from iterators over fixed assignments and provide
/// access to pre-assigned requests that are part of the problem constraints.
///
/// # Examples
///
/// ```
/// use dock_alloc_solver::ledger::AssignmentLedger;
/// use dock_alloc_model::{ProblemBuilder, Request, RequestId, Assignment, FixedAssignment};
/// use dock_alloc_core::domain::*;
///
/// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
/// let request = Request::new(
///     RequestId::new(100), SpaceLength::new(4), TimeDelta::new(3),
///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
/// ).unwrap();
/// let assignment = Assignment::new(request, SpacePosition::new(5), TimePoint::new(10));
/// builder.add_preassigned(FixedAssignment::new(assignment)).unwrap();
/// let problem = builder.build();
///
/// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
/// for handle in ledger.iter_fixed_handles() {
///     assert_eq!(handle.id(), RequestId::new(100));
/// }
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FixedHandle<'brand> {
    id: RequestId,
    _phantom: PhantomData<&'brand ()>,
}

impl<'brand> FixedHandle<'brand> {
    /// Returns the request ID associated with this fixed handle.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId, Assignment, FixedAssignment};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(999), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// let assignment = Assignment::new(request, SpacePosition::new(5), TimePoint::new(10));
    /// builder.add_preassigned(FixedAssignment::new(assignment)).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let handles: Vec<_> = ledger.iter_fixed_handles().collect();
    /// assert_eq!(handles[0].id(), RequestId::new(999));
    /// ```
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

/// A movable assignment that can be committed to or removed from a ledger.
///
/// This represents an assignment that can be dynamically added or removed during
/// the solving process, unlike fixed assignments which are immutable. Each movable
/// assignment has an associated handle for safe manipulation.
///
/// Movable assignments are typically created internally by solver algorithms and
/// committed to ledgers. They contain both the assignment data and a handle for
/// type-safe manipulation.
///
/// # Type Parameters
///
/// * `T` - The time coordinate type (must implement `PrimInt + Signed`)
/// * `C` - The cost type (must implement `PrimInt + Signed`)
///
/// # Examples
///
/// ```
/// use dock_alloc_solver::ledger::AssignmentLedger;
/// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
/// use dock_alloc_core::domain::*;
///
/// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
/// let request = Request::new(
///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
/// ).unwrap();
/// builder.add_unassigned_request(request).unwrap();
/// let problem = builder.build();
///
/// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
/// // Movables are obtained from iter_movable_assignments() after committing
/// let movables: Vec<_> = ledger.iter_movable_assignments().collect();
/// assert_eq!(movables.len(), 0); // No assignments committed yet
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MovableAssignment<'brand, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    assignment: Assignment<T, C>,
    handle: MovableHandle<'brand>,
    _phantom: PhantomData<&'brand ()>,
}

impl<'brand, T: PrimInt + Signed, C: PrimInt + Signed> MovableAssignment<'brand, T, C> {
    /// Returns the assignment associated with this movable.
    ///
    /// The returned assignment contains the complete allocation information
    /// including the request, space position, and time point.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// for movable in ledger.iter_movable_assignments() {
    ///     let assignment = movable.assignment();
    ///     assert_eq!(assignment.request().id(), RequestId::new(1));
    /// }
    /// ```
    #[inline]
    pub fn assignment(&self) -> &Assignment<T, C> {
        &self.assignment
    }

    /// Returns the handle for this movable assignment.
    ///
    /// The handle can be used for type-safe uncommit operations and provides
    /// access to the request ID.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// for movable in ledger.iter_movable_assignments() {
    ///     let handle = movable.handle();
    ///     assert_eq!(handle.id(), RequestId::new(1));
    /// }
    /// ```
    #[inline]
    pub fn handle(&self) -> MovableHandle<'brand> {
        self.handle
    }

    /// Returns the request ID for this movable assignment.
    ///
    /// This is a convenience method equivalent to `self.handle().id()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(42), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// for movable in ledger.iter_movable_assignments() {
    ///     let id = movable.id();
    ///     assert_eq!(id, RequestId::new(42));
    ///     assert_eq!(id, movable.handle().id()); // Equivalent calls
    /// }
    /// ```
    #[inline]
    pub fn id(&self) -> RequestId {
        self.handle.id()
    }
}

/// A ledger that tracks committed movable assignments for a dock allocation problem.
///
/// The assignment ledger maintains a collection of movable assignments that have been
/// committed during the solving process. It provides methods to commit new assignments
/// and uncommit existing ones, while ensuring type safety through branded handles.
///
/// # Type Parameters
///
/// * `'brand` - Lifetime brand that prevents mixing handles between different ledgers
/// * `'a` - Lifetime of the underlying problem reference
/// * `T` - The time coordinate type (must implement `PrimInt + Signed`)
/// * `C` - The cost type (must implement `PrimInt + Signed`)
///
/// # Examples
///
/// ```
/// use dock_alloc_solver::ledger::AssignmentLedger;
/// use dock_alloc_model::{Problem, ProblemBuilder, Request, RequestId};
/// use dock_alloc_core::domain::*;
///
/// // Create a simple problem
/// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
/// let request = Request::new(
///     RequestId::new(1),
///     SpaceLength::new(4),
///     TimeDelta::new(3),
///     SpacePosition::new(10),
///     Cost::new(1),
///     Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
/// ).unwrap();
/// builder.add_unassigned_request(request).unwrap();
/// let problem = builder.build();
///
/// // Create a ledger
/// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
///
/// assert_eq!(ledger.committed().len(), 0);
/// assert!(ledger.problem().unassigned().contains_key(&RequestId::new(1)));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentLedger<'brand, 'a, T: PrimInt + Signed, C: PrimInt + Signed> {
    problem: &'a Problem<T, C>,
    committed: HashMap<RequestId, MovableAssignment<'brand, T, C>>,
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
    /// Creates a new assignment ledger for the given problem.
    ///
    /// The ledger starts empty with no committed assignments. Fixed assignments
    /// from the problem are accessible but cannot be modified.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// assert_eq!(ledger.committed().len(), 0);
    /// ```
    pub fn new(problem: &'a Problem<T, C>) -> Self {
        Self {
            problem,
            committed: HashMap::new(),
            _phantom: PhantomData,
        }
    }

    /// Returns a reference to the underlying problem.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let prob_ref = ledger.problem();
    /// assert!(prob_ref.unassigned().contains_key(&RequestId::new(1)));
    /// ```
    #[inline]
    pub fn problem(&self) -> &'a Problem<T, C> {
        self.problem
    }

    /// Returns a reference to the map of committed assignments.
    ///
    /// The returned map contains all movable assignments that have been
    /// committed to this ledger, indexed by their request IDs.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let committed = ledger.committed();
    /// assert_eq!(committed.len(), 0);
    /// assert!(committed.is_empty());
    /// ```
    #[inline]
    pub fn committed(&self) -> &HashMap<RequestId, MovableAssignment<'brand, T, C>> {
        &self.committed
    }

    /// Commits a movable assignment to the ledger.
    ///
    /// The assignment must correspond to a request that exists in the problem's
    /// unassigned requests and must not already be committed.
    ///
    /// # Errors
    ///
    /// Returns `LedgerError::AlreadyCommitted` if an assignment with the same
    /// request ID is already committed to this ledger.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, LedgerError};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let mut ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// // Since movables can't be created externally, this demonstrates the concept
    /// // In practice, commit() would be called with movables from solver algorithms
    /// assert_eq!(ledger.committed().len(), 0);
    /// ```
    pub fn commit(&mut self, ma: MovableAssignment<'brand, T, C>) -> Result<(), LedgerError> {
        let id = ma.id();
        if self.committed.contains_key(&id) {
            return Err(LedgerError::AlreadyCommitted);
        }
        debug_assert!(self.problem.unassigned().contains_key(&id));
        self.committed.insert(id, ma);
        Ok(())
    }

    /// Uncommits a movable assignment from the ledger.
    ///
    /// Removes the assignment associated with the given handle from the ledger
    /// and returns it. The assignment can then be modified and recommitted if needed.
    ///
    /// # Errors
    ///
    /// Returns `LedgerError::NotCommitted` if no assignment with the given
    /// handle's request ID is currently committed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, LedgerError};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let mut ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// // Since handles can't be created externally, this demonstrates the concept
    /// // In practice, uncommit() would be called with handles from previous operations
    /// assert_eq!(ledger.committed().len(), 0);
    /// ```
    pub fn uncommit(
        &mut self,
        mh: MovableHandle<'brand>,
    ) -> Result<MovableAssignment<'brand, T, C>, LedgerError> {
        self.committed
            .remove(&mh.id())
            .ok_or(LedgerError::NotCommitted)
    }

    pub fn uncommit_assignment(
        &mut self,
        assignment: &'brand MovableAssignment<'brand, T, C>,
    ) -> Result<MovableAssignment<'brand, T, C>, LedgerError> {
        self.uncommit(assignment.handle())
    }

    /// Returns an iterator over handles for all fixed (pre-assigned) assignments.
    ///
    /// Fixed assignments come from the problem definition and cannot be modified.
    /// This iterator provides handles for accessing these assignments.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId, Assignment, FixedAssignment};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(100), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// let assignment = Assignment::new(request, SpacePosition::new(5), TimePoint::new(10));
    /// builder.add_preassigned(FixedAssignment::new(assignment)).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let handles: Vec<_> = ledger.iter_fixed_handles().collect();
    /// assert_eq!(handles.len(), 1);
    /// assert_eq!(handles[0].id(), RequestId::new(100));
    /// ```
    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = FixedHandle<'brand>> + '_ {
        self.problem.preassigned().keys().map(|&rid| FixedHandle {
            id: rid,
            _phantom: PhantomData,
        })
    }

    /// Returns an iterator over all fixed (pre-assigned) assignments.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId, Assignment, FixedAssignment};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(100), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// let assignment = Assignment::new(request, SpacePosition::new(5), TimePoint::new(10));
    /// builder.add_preassigned(FixedAssignment::new(assignment)).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let fixed: Vec<_> = ledger.iter_fixed_assignments().collect();
    /// assert_eq!(fixed.len(), 1);
    /// assert_eq!(fixed[0].assignment().request().id(), RequestId::new(100));
    /// ```
    #[inline]
    pub fn iter_fixed_assignments(&self) -> impl Iterator<Item = &FixedAssignment<T, C>> + '_ {
        self.problem.preassigned().values()
    }

    /// Returns an iterator over handles for all committed movable assignments.
    ///
    /// These handles can be used to uncommit assignments from the ledger.
    /// The iterator will be empty if no assignments have been committed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let handles: Vec<_> = ledger.iter_movable_handles().collect();
    /// assert_eq!(handles.len(), 0); // No assignments committed yet
    /// ```
    #[inline]
    pub fn iter_movable_handles(&self) -> impl Iterator<Item = MovableHandle<'brand>> + '_ {
        self.committed.keys().map(|&rid| MovableHandle {
            id: rid,
            _phantom: PhantomData,
        })
    }

    /// Returns an iterator over all committed movable assignments.
    ///
    /// This provides direct access to the movable assignments that have been
    /// committed to this ledger. Each assignment contains the complete allocation
    /// information and can be used for analysis or further operations.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let movables: Vec<_> = ledger.iter_movable_assignments().collect();
    /// assert_eq!(movables.len(), 0); // No assignments committed yet
    /// ```
    #[inline]
    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = &MovableAssignment<'brand, T, C>> + '_ {
        self.committed.values()
    }

    /// Returns an iterator over all committed movable assignments.
    ///
    /// This is an alias for `iter_movable_assignments()` for backward compatibility.
    /// Use `iter_movable_assignments()` for new code.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let committed: Vec<_> = ledger.iter_committed().collect();
    /// assert_eq!(committed.len(), 0); // No assignments committed yet
    /// ```
    #[inline]
    pub fn iter_committed(&self) -> impl Iterator<Item = &MovableAssignment<'brand, T, C>> {
        self.committed.values()
    }

    /// Returns an iterator over all unassigned movable requests.
    ///
    /// This iterator provides access to requests from the problem definition that have
    /// not been committed to this ledger. These are requests that are available for
    /// assignment in the solving process.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request1 = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// let request2 = Request::new(
    ///     RequestId::new(2), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(20), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request1).unwrap();
    /// builder.add_unassigned_request(request2).unwrap();
    /// let problem = builder.build();
    ///
    /// let mut ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    ///
    /// // Initially all requests are unassigned
    /// let unassigned: Vec<_> = ledger.iter_unassigned_requests()
    ///     .map(|req| req.request().id())
    ///     .collect();
    /// assert_eq!(unassigned.len(), 2);
    /// assert!(unassigned.contains(&RequestId::new(1)));
    /// assert!(unassigned.contains(&RequestId::new(2)));
    /// ```
    #[inline]
    pub fn iter_unassigned_requests(&self) -> impl Iterator<Item = &MoveableRequest<T, C>> + '_ {
        self.problem
            .unassigned()
            .values()
            .filter(move |req| !self.committed.contains_key(&req.request().id()))
    }

    /// Returns an iterator over all assigned movable requests.
    ///
    /// This iterator provides access to requests that have been committed to this
    /// ledger. These are requests that have been assigned positions and times
    /// during the solving process.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request1 = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// let request2 = Request::new(
    ///     RequestId::new(2), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(20), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request1).unwrap();
    /// builder.add_unassigned_request(request2).unwrap();
    /// let problem = builder.build();
    ///
    /// let mut ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    ///
    /// // Initially no requests are assigned
    /// assert_eq!(ledger.iter_assigned_requests().count(), 0);
    ///
    /// // After committing, the request appears in assigned requests
    /// // (In practice, you'd use solver algorithms to create movable assignments)
    /// ```
    #[inline]
    pub fn iter_assigned_requests(&self) -> impl Iterator<Item = &MoveableRequest<T, C>> + '_ {
        self.problem
            .unassigned()
            .values()
            .filter(move |req| self.committed.contains_key(&req.request().id()))
    }

    /// Returns an iterator over all assignments (both fixed and committed movable).
    ///
    /// This combines fixed assignments from the problem definition with movable
    /// assignments that have been committed to this ledger. This provides a complete
    /// view of all assignments in the current state of the ledger.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::AssignmentLedger;
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId, Assignment, FixedAssignment};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    ///
    /// // Add a fixed assignment
    /// let fixed_request = Request::new(
    ///     RequestId::new(100), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// let fixed_assignment = Assignment::new(fixed_request, SpacePosition::new(5), TimePoint::new(10));
    /// builder.add_preassigned(FixedAssignment::new(fixed_assignment)).unwrap();
    ///
    /// // Add an unassigned request
    /// let movable_request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(movable_request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let assignments: Vec<_> = ledger.iter_assignments().collect();
    /// assert_eq!(assignments.len(), 1); // Only the fixed assignment
    /// assert_eq!(assignments[0].request().id(), RequestId::new(100));
    /// ```
    pub fn iter_assignments(&self) -> impl Iterator<Item = &Assignment<T, C>> + '_ {
        let fixed_iter = self
            .problem
            .preassigned()
            .values()
            .map(|fixed| fixed.assignment());

        let movable_iter = self.committed.values().map(|ma| ma.assignment());
        fixed_iter.chain(movable_iter)
    }
}

/// An overlay that stages assignment operations without modifying the underlying ledger.
///
/// The assignment overlay provides a transactional view over a base ledger, allowing
/// you to stage commits and uncommits without immediately applying them. This is useful
/// for exploring different assignment combinations before committing to changes.
///
/// # Type Parameters
///
/// * `'brand` - Lifetime brand for type safety
/// * `'a` - Lifetime of the problem reference
/// * `'l` - Lifetime of the ledger reference
/// * `T` - The time coordinate type (must implement `PrimInt + Signed`)
/// * `C` - The cost type (must implement `PrimInt + Signed`)
///
/// # Examples
///
/// ```
/// use dock_alloc_solver::ledger::{AssignmentLedger, AssignmentOverlay};
/// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
/// use dock_alloc_core::domain::*;
///
/// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
/// let request = Request::new(
///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
/// ).unwrap();
/// builder.add_unassigned_request(request).unwrap();
/// let problem = builder.build();
///
/// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
/// let overlay = AssignmentOverlay::new(&ledger);
///
/// // Overlay starts with same view as base ledger
/// assert_eq!(overlay.iter_staged_commits().count(), 0);
/// assert_eq!(overlay.iter_staged_uncommits().count(), 0);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentOverlay<'brand, 'a, 'l, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    ledger: &'l AssignmentLedger<'brand, 'a, T, C>,
    staged_commits: BTreeMap<RequestId, MovableAssignment<'brand, T, C>>,
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
    /// Creates a new assignment overlay over the given ledger.
    ///
    /// The overlay starts with no staged operations and provides a view
    /// identical to the base ledger until operations are staged.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, AssignmentOverlay};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let overlay = AssignmentOverlay::new(&ledger);
    ///
    /// assert_eq!(overlay.iter_staged_commits().count(), 0);
    /// assert_eq!(overlay.iter_staged_uncommits().count(), 0);
    /// ```
    pub fn new(ledger: &'l AssignmentLedger<'brand, 'a, T, C>) -> Self {
        Self {
            ledger,
            staged_commits: BTreeMap::new(),
            staged_uncommits: BTreeMap::new(),
        }
    }

    /// Stages a commit operation in the overlay.
    ///
    /// This stages the assignment for commit without modifying the base ledger.
    /// If the same assignment is staged multiple times, the operation is idempotent.
    /// If a different assignment for the same request is already staged, an error is returned.
    ///
    /// # Errors
    ///
    /// * `StageError::AlreadyCommittedInBase` - The request is already committed in the base ledger
    /// * `StageError::AlreadyStagedCommit` - A different assignment for this request is already staged
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, AssignmentOverlay, StageError};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let mut overlay = AssignmentOverlay::new(&ledger);
    ///
    /// // Since movables can't be created externally, this demonstrates the concept
    /// assert_eq!(overlay.iter_staged_commits().count(), 0);
    /// ```
    pub fn commit(&mut self, ma: MovableAssignment<'brand, T, C>) -> Result<(), StageError> {
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

    /// Stages an uncommit operation in the overlay.
    ///
    /// If the request has a staged commit, it removes the staged commit and returns it.
    /// If the request is committed in the base ledger, it stages an uncommit operation
    /// and returns the assignment from the base ledger.
    ///
    /// # Errors
    ///
    /// * `StageError::AlreadyStagedUncommit` - An uncommit for this request is already staged
    /// * `StageError::NotCommittedInBase` - The request is not committed in the base ledger
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, AssignmentOverlay};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let mut overlay = AssignmentOverlay::new(&ledger);
    ///
    /// // Since handles can't be created externally, this demonstrates the concept
    /// assert_eq!(overlay.iter_staged_uncommits().count(), 0);
    /// ```
    pub fn uncommit(
        &mut self,
        mh: MovableHandle<'brand>,
    ) -> Result<MovableAssignment<'brand, T, C>, StageError> {
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

    pub fn uncommit_assignment(
        &mut self,
        assignment: &'brand MovableAssignment<'brand, T, C>,
    ) -> Result<MovableAssignment<'brand, T, C>, StageError> {
        self.uncommit(assignment.handle())
    }

    /// Returns an iterator over handles for all fixed assignments.
    ///
    /// This delegates to the underlying ledger since fixed assignments
    /// are immutable and not affected by overlay operations.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, AssignmentOverlay};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId, Assignment, FixedAssignment};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(100), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// let assignment = Assignment::new(request, SpacePosition::new(5), TimePoint::new(10));
    /// builder.add_preassigned(FixedAssignment::new(assignment)).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let overlay = AssignmentOverlay::new(&ledger);
    ///
    /// let handles: Vec<_> = overlay.iter_fixed_handles().collect();
    /// assert_eq!(handles.len(), 1);
    /// assert_eq!(handles[0].id(), RequestId::new(100));
    /// ```
    #[inline]
    pub fn iter_fixed_handles(&self) -> impl Iterator<Item = FixedHandle<'brand>> + '_ {
        self.ledger.iter_fixed_handles()
    }

    /// Returns an iterator over all fixed assignments.
    ///
    /// This delegates to the underlying ledger since fixed assignments
    /// are immutable and not affected by overlay operations.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, AssignmentOverlay};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId, Assignment, FixedAssignment};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(100), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// let assignment = Assignment::new(request, SpacePosition::new(5), TimePoint::new(10));
    /// builder.add_preassigned(FixedAssignment::new(assignment)).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let overlay = AssignmentOverlay::new(&ledger);
    ///
    /// let fixed: Vec<_> = overlay.iter_fixed_assignments().collect();
    /// assert_eq!(fixed.len(), 1);
    /// assert_eq!(fixed[0].assignment().request().id(), RequestId::new(100));
    /// ```
    #[inline]
    pub fn iter_fixed_assignments(&self) -> impl Iterator<Item = &FixedAssignment<T, C>> + '_ {
        self.ledger.iter_fixed_assignments()
    }

    /// Returns an iterator over handles for all visible movable assignments.
    ///
    /// This includes assignments from the base ledger that are not staged for uncommit,
    /// plus assignments that are staged for commit. The result represents the effective
    /// view of movable assignments in this overlay.
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

    /// Returns an iterator over all visible movable assignments.
    ///
    /// This includes assignments from the base ledger that are not staged for uncommit,
    /// plus assignments that are staged for commit. The result represents the effective
    /// view of movable assignments in this overlay.
    #[inline]
    pub fn iter_movable_assignments(
        &self,
    ) -> impl Iterator<Item = &MovableAssignment<'brand, T, C>> + '_ {
        let base_visible = self.ledger.iter_movable_assignments().filter(move |ma| {
            let id = ma.id();
            !self.staged_uncommits.contains_key(&id) && !self.staged_commits.contains_key(&id)
        });

        let staged = self.staged_commits.values();
        base_visible.chain(staged)
    }

    /// Returns an iterator over assignments that are staged for commit.
    ///
    /// These are assignments that have been staged in this overlay but are not
    /// yet committed to the base ledger. They represent pending commits that will
    /// be applied when the overlay is finalized.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, AssignmentOverlay};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let overlay = AssignmentOverlay::new(&ledger);
    /// let staged: Vec<_> = overlay.iter_staged_commits().collect();
    /// assert_eq!(staged.len(), 0); // No staged commits initially
    /// ```
    #[inline]
    pub fn iter_staged_commits(&self) -> impl Iterator<Item = &MovableAssignment<'brand, T, C>> {
        self.staged_commits.values()
    }

    /// Returns an iterator over handles that are staged for uncommit.
    ///
    /// These are handles for assignments that exist in the base ledger but are
    /// staged for removal in this overlay. They represent pending uncommits that
    /// will be applied when the overlay is finalized.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, AssignmentOverlay};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let overlay = AssignmentOverlay::new(&ledger);
    /// let uncommits: Vec<_> = overlay.iter_staged_uncommits().collect();
    /// assert_eq!(uncommits.len(), 0); // No staged uncommits initially
    /// ```
    #[inline]
    pub fn iter_staged_uncommits(&self) -> impl Iterator<Item = &MovableHandle<'brand>> {
        self.staged_uncommits.values()
    }

    /// Returns an iterator over all visible assignments in this overlay.
    ///
    /// This combines:
    /// - Fixed assignments from the problem definition
    /// - Base ledger assignments that are not staged for uncommit
    /// - Assignments that are staged for commit
    ///
    /// The result represents the complete effective view of assignments in this overlay,
    /// showing what the state would be if all staged operations were applied.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, AssignmentOverlay};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId, Assignment, FixedAssignment};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    ///
    /// // Add a fixed assignment
    /// let fixed_request = Request::new(
    ///     RequestId::new(100), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// let fixed_assignment = Assignment::new(fixed_request, SpacePosition::new(5), TimePoint::new(10));
    /// builder.add_preassigned(FixedAssignment::new(fixed_assignment)).unwrap();
    ///
    /// // Add an unassigned request
    /// let movable_request = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(movable_request).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let overlay = AssignmentOverlay::new(&ledger);
    /// let assignments: Vec<_> = overlay.iter_assignments().collect();
    /// assert_eq!(assignments.len(), 1); // Only the fixed assignment
    /// assert_eq!(assignments[0].request().id(), RequestId::new(100));
    /// ```
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

    /// Returns an iterator over all unassigned movable requests in the overlay view.
    ///
    /// This iterator provides access to requests from the problem definition that have
    /// not been committed to the base ledger and not staged for commit in this overlay.
    /// These are requests that are still available for assignment in the overlay's view.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, AssignmentOverlay};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request1 = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// let request2 = Request::new(
    ///     RequestId::new(2), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(20), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request1).unwrap();
    /// builder.add_unassigned_request(request2).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let overlay = AssignmentOverlay::new(&ledger);
    ///
    /// // Initially all requests are unassigned
    /// let unassigned: Vec<_> = overlay.iter_unassigned_requests()
    ///     .map(|req| req.request().id())
    ///     .collect();
    /// assert_eq!(unassigned.len(), 2);
    /// assert!(unassigned.contains(&RequestId::new(1)));
    /// assert!(unassigned.contains(&RequestId::new(2)));
    /// ```
    pub fn iter_unassigned_requests(&self) -> impl Iterator<Item = &MoveableRequest<T, C>> + '_ {
        self.ledger
            .problem
            .unassigned()
            .values()
            .filter(move |req| {
                let id = req.request().id();
                !self.ledger.committed.contains_key(&id) && !self.staged_commits.contains_key(&id)
            })
    }

    /// Returns an iterator over all assigned movable requests in the overlay view.
    ///
    /// This iterator provides access to requests that either:
    /// - Have been committed to the base ledger and not staged for uncommit in this overlay, or
    /// - Have been staged for commit in this overlay.
    ///
    /// The result represents requests that would be considered assigned if all
    /// staged operations in this overlay were applied.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_solver::ledger::{AssignmentLedger, AssignmentOverlay};
    /// use dock_alloc_model::{ProblemBuilder, Request, RequestId};
    /// use dock_alloc_core::domain::*;
    ///
    /// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
    /// let request1 = Request::new(
    ///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// let request2 = Request::new(
    ///     RequestId::new(2), SpaceLength::new(4), TimeDelta::new(3),
    ///     SpacePosition::new(20), Cost::new(1), Cost::new(1),
    ///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
    ///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
    /// ).unwrap();
    /// builder.add_unassigned_request(request1).unwrap();
    /// builder.add_unassigned_request(request2).unwrap();
    /// let problem = builder.build();
    ///
    /// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
    /// let overlay = AssignmentOverlay::new(&ledger);
    ///
    /// // Initially no requests are assigned
    /// assert_eq!(overlay.iter_assigned_requests().count(), 0);
    ///
    /// // After staging commits or with committed assignments in the base ledger
    /// // that aren't staged for uncommit, requests would appear here
    /// ```
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

/// Converts an assignment ledger into a solution.
///
/// This creates a solution containing all assignments (both fixed and committed movable)
/// from the ledger. The solution can be used to represent the current state of the
/// dock allocation problem and provides a complete assignment mapping.
///
/// # Examples
///
/// ```
/// use dock_alloc_solver::ledger::AssignmentLedger;
/// use dock_alloc_model::{ProblemBuilder, Request, RequestId, Assignment, FixedAssignment, Solution};
/// use dock_alloc_core::domain::*;
///
/// let mut builder = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
///
/// // Add a fixed assignment
/// let fixed_request = Request::new(
///     RequestId::new(100), SpaceLength::new(4), TimeDelta::new(3),
///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
/// ).unwrap();
/// let fixed_assignment = Assignment::new(fixed_request, SpacePosition::new(5), TimePoint::new(10));
/// builder.add_preassigned(FixedAssignment::new(fixed_assignment)).unwrap();
///
/// // Add an unassigned request
/// let movable_request = Request::new(
///     RequestId::new(1), SpaceLength::new(4), TimeDelta::new(3),
///     SpacePosition::new(10), Cost::new(1), Cost::new(1),
///     TimeInterval::new(TimePoint::new(0), TimePoint::new(100)),
///     SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
/// ).unwrap();
/// builder.add_unassigned_request(movable_request).unwrap();
/// let problem = builder.build();
///
/// let ledger: AssignmentLedger<'_, '_, i64, i64> = AssignmentLedger::new(&problem);
/// let solution: Solution<i64, i64> = (&ledger).into();
///
/// // Solution contains only the fixed assignment (no movable assignments committed)
/// assert_eq!(solution.decisions().len(), 1);
/// assert!(solution.decisions().contains_key(&RequestId::new(100)));
/// ```
impl<'brand, 'a, T, C> From<&AssignmentLedger<'brand, 'a, T, C>> for Solution<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
{
    fn from(ledger: &AssignmentLedger<'brand, 'a, T, C>) -> Self {
        let decisions: HashMap<_, _> = ledger
            .iter_assignments()
            .map(|a| (a.request().id(), a.clone()))
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
    use dock_alloc_model::{FixedAssignment, Request};
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
    ) -> (Request<T, C>, MovableAssignment<'b, T, C>) {
        let r = req_ok(rid);
        let a = asg(r, start_pos, start_time);
        let ma = MovableAssignment {
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
            b.add_preassigned(FixedAssignment::new(a)).unwrap();
        }
        b.build()
    }

    fn ids_from_assignments<'a>(
        it: impl Iterator<Item = &'a Assignment<T, C>>,
    ) -> BTreeSet<RequestId> {
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

    #[test]
    fn ledger_iter_unassigned_requests_excludes_committed() {
        // unassigned: 1,2,3 -> commit(2)
        let prob = problem_with_unassigned(&[1, 2, 3]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        // Initially all requests are unassigned
        let ids_before: BTreeSet<_> = ledger
            .iter_unassigned_requests()
            .map(|req| req.request().id())
            .collect();
        let expected_before: BTreeSet<_> =
            [1u64, 2u64, 3u64].into_iter().map(RequestId::new).collect();
        assert_eq!(ids_before, expected_before);

        // After committing request 2, it should no longer be in unassigned
        let (_r2, ma2) = movable::<'static>(2, 5, 10);
        ledger.commit(ma2).unwrap();

        let ids_after: BTreeSet<_> = ledger
            .iter_unassigned_requests()
            .map(|req| req.request().id())
            .collect();
        let expected_after: BTreeSet<_> = [1u64, 3u64].into_iter().map(RequestId::new).collect();
        assert_eq!(ids_after, expected_after);
    }

    #[test]
    fn ledger_iter_assigned_requests_includes_only_committed() {
        // unassigned: 1,2,3 -> commit(1)
        let prob = problem_with_unassigned(&[1, 2, 3]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        // Initially no requests are assigned
        let ids_before: BTreeSet<_> = ledger
            .iter_assigned_requests()
            .map(|req| req.request().id())
            .collect();
        assert!(ids_before.is_empty());

        // After committing request 1, only it should be in assigned
        let (_r1, ma1) = movable::<'static>(1, 3, 0);
        ledger.commit(ma1).unwrap();

        let ids_after: BTreeSet<_> = ledger
            .iter_assigned_requests()
            .map(|req| req.request().id())
            .collect();
        let expected_after: BTreeSet<_> = [1u64].into_iter().map(RequestId::new).collect();
        assert_eq!(ids_after, expected_after);
    }

    #[test]
    fn overlay_iter_unassigned_requests_respects_staged_commits() {
        // unassigned: 5,6,7; base commits: 6; overlay stages: 7
        let prob = problem_with_unassigned(&[5, 6, 7]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        // Commit request 6 to the base ledger
        let (_r6, ma6) = movable::<'static>(6, 2, 0);
        ledger.commit(ma6).unwrap();

        let mut overlay = AssignmentOverlay::new(&ledger);

        // Stage a commit for request 7
        let (_r7, ma7) = movable::<'static>(7, 3, 0);
        overlay.commit(ma7).unwrap();

        // Unassigned should only contain request 5
        let ids: BTreeSet<_> = overlay
            .iter_unassigned_requests()
            .map(|req| req.request().id())
            .collect();
        let expected: BTreeSet<_> = [5u64].into_iter().map(RequestId::new).collect();
        assert_eq!(ids, expected);
    }

    #[test]
    fn overlay_iter_assigned_requests_includes_base_and_staged_commits() {
        // unassigned: 10,11,12; base commits: 10; overlay stages: 12, uncommits: 10
        let prob = problem_with_unassigned(&[10, 11, 12]);
        let mut ledger: AssignmentLedger<'static, '_, T, C> = AssignmentLedger::new(&prob);

        // Commit request 10 to the base ledger
        let (_r10, ma10) = movable::<'static>(10, 1, 0);
        ledger.commit(ma10).unwrap();

        let mut overlay = AssignmentOverlay::new(&ledger);

        // Stage an uncommit for request 10
        overlay.uncommit(mhandle::<'static>(10)).unwrap();

        // Stage a commit for request 12
        let (_r12, ma12) = movable::<'static>(12, 3, 0);
        overlay.commit(ma12).unwrap();

        // Assigned should only include request 12 (not 10 because it's staged for uncommit)
        let ids: BTreeSet<_> = overlay
            .iter_assigned_requests()
            .map(|req| req.request().id())
            .collect();
        let expected: BTreeSet<_> = [12u64].into_iter().map(RequestId::new).collect();
        assert_eq!(ids, expected);
    }
}
