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
    domain::Version,
    lens::{AvailabilityView, BerthOccupancyOverlay, FreePlacementIter},
    occ::BerthOccupancy,
    quay::{Quay, QuayRead},
};
use core::marker::PhantomData;
use dock_alloc_core::domain::{SpaceInterval, TimeInterval, TimePoint};
use dock_alloc_core::domain::{SpaceLength, SpacePosition};
use dock_alloc_model::{Assignment, Problem, Request, RequestId};
use num_traits::{PrimInt, Signed};
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OccupancyRect<T: PrimInt + Signed> {
    time: TimeInterval<T>,
    space: SpaceInterval,
}

impl<T: PrimInt + Signed> OccupancyRect<T> {
    #[inline]
    pub fn new(time: TimeInterval<T>, space: SpaceInterval) -> Self {
        Self { time, space }
    }

    #[inline]
    pub fn time(&self) -> &TimeInterval<T> {
        &self.time
    }

    #[inline]
    pub fn space(&self) -> &SpaceInterval {
        &self.space
    }
}

impl<T: PrimInt + Signed> From<(&TimeInterval<T>, &SpaceInterval)> for OccupancyRect<T> {
    fn from(v: (&TimeInterval<T>, &SpaceInterval)) -> Self {
        Self::new(*v.0, *v.1)
    }
}

impl<T: PrimInt + Signed> From<(TimeInterval<T>, SpaceInterval)> for OccupancyRect<T> {
    fn from(v: (TimeInterval<T>, SpaceInterval)) -> Self {
        Self::new(v.0, v.1)
    }
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> From<&Assignment<T, C>> for OccupancyRect<T> {
    fn from(asg: &Assignment<T, C>) -> Self {
        let len = asg.request().length();
        let sp = asg.start_position();
        let space = SpaceInterval::new(sp, SpacePosition::new(sp.value() + len.value()));
        let dur = asg.request().processing_duration();
        let tp = asg.start_time();
        let time = TimeInterval::new(tp, TimePoint::new(tp.value() + dur.value()));
        Self::new(time, space)
    }
}

impl<T: PrimInt + Signed> From<&RequestEdit<T>> for OccupancyRect<T> {
    fn from(re: &RequestEdit<T>) -> Self {
        Self::new(re.time(), re.space())
    }
}

impl<T: PrimInt + Signed + Display> Display for OccupancyRect<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "OccupancyRect(time: {}, space: {})",
            self.time, self.space
        )
    }
}

#[derive(Clone, Debug)]
struct Staging<T: PrimInt + Signed> {
    set_by_req: HashMap<RequestId, OccupancyRect<T>>,
    clear_by_req: HashMap<RequestId, OccupancyRect<T>>,
}

impl<T: PrimInt + Signed> Default for Staging<T> {
    fn default() -> Self {
        Self {
            set_by_req: HashMap::new(),
            clear_by_req: HashMap::new(),
        }
    }
}

impl<T: PrimInt + Signed> Staging<T> {
    #[inline]
    fn put_set(&mut self, req: RequestId, rect: OccupancyRect<T>) -> Option<OccupancyRect<T>> {
        self.set_by_req.insert(req, rect)
    }

    #[inline]
    fn remove_set(&mut self, req: RequestId) -> Option<OccupancyRect<T>> {
        self.set_by_req.remove(&req)
    }

    #[inline]
    fn put_clear(&mut self, req: RequestId, rect: OccupancyRect<T>) -> Option<OccupancyRect<T>> {
        self.clear_by_req.insert(req, rect)
    }
    #[inline]
    fn remove_clear(&mut self, req: RequestId) -> Option<OccupancyRect<T>> {
        self.clear_by_req.remove(&req)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BerthOccupancyChangeOperation<T: PrimInt + Signed> {
    Free(OccupancyRect<T>),
    Occupy(OccupancyRect<T>),
}

impl<T: PrimInt + Signed> BerthOccupancyChangeOperation<T> {
    pub fn rect(&self) -> &OccupancyRect<T> {
        match self {
            BerthOccupancyChangeOperation::Free(p) => p,
            BerthOccupancyChangeOperation::Occupy(p) => p,
        }
    }
}

impl<T: PrimInt + Signed + Display> Display for BerthOccupancyChangeOperation<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BerthOccupancyChangeOperation::Free(p) => write!(f, "Free({})", p),
            BerthOccupancyChangeOperation::Occupy(p) => write!(f, "Occupy({})", p),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RequestEdit<T: PrimInt + Signed> {
    id: RequestId,
    time: TimeInterval<T>,
    space: SpaceInterval,
}

impl<T: PrimInt + Signed> RequestEdit<T> {
    #[inline]
    pub fn new(id: RequestId, time: TimeInterval<T>, space: SpaceInterval) -> Self {
        Self { id, time, space }
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn time(&self) -> TimeInterval<T> {
        self.time
    }

    #[inline]
    pub fn space(&self) -> SpaceInterval {
        self.space
    }
}

impl<T: PrimInt + Signed + Display> Display for RequestEdit<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "RequestEdit(id: {}, time: {}, space: {})",
            self.id, self.time, self.space
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AssignEdit<T: PrimInt + Signed> {
    Set(RequestEdit<T>),
    Clear(RequestId),
}

impl<T: PrimInt + Signed> AssignEdit<T> {
    pub fn request_id(&self) -> RequestId {
        match self {
            AssignEdit::Set(e) => e.id(),
            AssignEdit::Clear(id) => *id,
        }
    }
}

impl<T: PrimInt + Signed + Display> Display for AssignEdit<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AssignEdit::Set(e) => write!(f, "Set({})", e),
            AssignEdit::Clear(id) => write!(f, "Clear({})", id),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Footprint<T: PrimInt + Signed> {
    time: TimeInterval<T>,
    space: SpaceInterval,
}

impl<T: PrimInt + Signed> Default for Footprint<T> {
    fn default() -> Self {
        Self {
            time: TimeInterval::default(),
            space: SpaceInterval::default(),
        }
    }
}

impl<T: PrimInt + Signed> Footprint<T> {
    #[inline]
    fn new(time: TimeInterval<T>, space: SpaceInterval) -> Self {
        Self { time, space }
    }

    #[inline]
    pub fn time(&self) -> TimeInterval<T> {
        self.time
    }

    #[inline]
    pub fn space(&self) -> SpaceInterval {
        self.space
    }
}

#[inline]
fn time_hull<T: PrimInt + Signed>(a: &TimeInterval<T>, b: &TimeInterval<T>) -> TimeInterval<T> {
    let start = std::cmp::min_by(a.start(), b.start(), |x, y| x.value().cmp(&y.value()));
    let end = std::cmp::max_by(a.end(), b.end(), |x, y| x.value().cmp(&y.value()));
    TimeInterval::new(start, end)
}

#[inline]
fn space_hull(a: &SpaceInterval, b: &SpaceInterval) -> SpaceInterval {
    let start = std::cmp::min_by(a.start(), b.start(), |x, y| x.value().cmp(&y.value()));
    let end = std::cmp::max_by(a.end(), b.end(), |x, y| x.value().cmp(&y.value()));
    SpaceInterval::new(start, end)
}

impl<T: PrimInt + Signed> From<&[BerthOccupancyChangeOperation<T>]> for Footprint<T> {
    fn from(ops: &[BerthOccupancyChangeOperation<T>]) -> Self {
        ops.iter()
            .map(|op| op.rect())
            .map(|d| (*d.time(), *d.space()))
            .reduce(|(t1, s1), (t2, s2)| (time_hull(&t1, &t2), space_hull(&s1, &s2)))
            .map(|(time, space)| Footprint::new(time, space))
            .unwrap_or_default()
    }
}

impl<T: PrimInt + Signed> From<&OccupancyRect<T>> for Footprint<T> {
    fn from(op: &OccupancyRect<T>) -> Self {
        Footprint::new(*op.time(), *op.space())
    }
}

impl<T: PrimInt + Signed> From<&BerthOccupancyChangeOperation<T>> for Footprint<T> {
    fn from(op: &BerthOccupancyChangeOperation<T>) -> Self {
        match op {
            BerthOccupancyChangeOperation::Free(d) | BerthOccupancyChangeOperation::Occupy(d) => {
                Footprint::from(d)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Plan<T: PrimInt + Signed> {
    operations: Vec<BerthOccupancyChangeOperation<T>>,
    edits: Vec<AssignEdit<T>>,
    version: Version,
    footprint: Footprint<T>,
}

impl<T: PrimInt + Signed> Plan<T> {
    pub fn new(
        operations: Vec<BerthOccupancyChangeOperation<T>>,
        edits: Vec<AssignEdit<T>>,
        version: Version,
    ) -> Self {
        let footprint = Footprint::from(operations.as_slice());
        Self {
            operations,
            edits,
            version,
            footprint,
        }
    }
    #[inline]
    pub fn operations(&self) -> &[BerthOccupancyChangeOperation<T>] {
        &self.operations
    }

    #[inline]
    pub fn edits(&self) -> &[AssignEdit<T>] {
        &self.edits
    }

    #[inline]
    pub fn version(&self) -> Version {
        self.version
    }

    #[inline]
    pub fn fp(&self) -> Footprint<T> {
        self.footprint
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.operations.is_empty() && self.edits.is_empty()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BerthOccupancySlot<T: PrimInt + Signed> {
    start_time: TimePoint<T>,
    space: SpaceInterval,
}

impl<T: PrimInt + Signed> BerthOccupancySlot<T> {
    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }
    #[inline]
    pub fn space(&self) -> SpaceInterval {
        self.space
    }
}

impl<T: PrimInt + Signed + Display> Display for BerthOccupancySlot<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Slot(start_time: {}, space: {})",
            self.start_time, self.space
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PlanError {
    UnknownRequest(RequestId),
    Locked(RequestId),
    SlotStale(RequestId),
    Overlap,
    NoBaselineAssignment(RequestId),
}

impl Display for PlanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlanError::UnknownRequest(id) => write!(f, "unknown request: {}", id),
            PlanError::Locked(id) => write!(f, "request is locked/pre-assigned: {}", id),
            PlanError::SlotStale(id) => write!(f, "slot stale or infeasible for request: {}", id),
            PlanError::Overlap => write!(f, "operation would cause an overlap"),
            PlanError::NoBaselineAssignment(id) => {
                write!(f, "no baseline assignment to clear for request: {}", id)
            }
        }
    }
}

impl std::error::Error for PlanError {}

#[derive(Clone, Copy, Debug)]
pub struct Planner;

impl Display for Planner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Planner")
    }
}

impl Planner {
    #[inline]
    pub fn scope<T, C, Q, R>(
        berth: &BerthOccupancy<T, Q>,
        problem: &Problem<T, C>,
        func: impl for<'brand> FnOnce(ProposeCtx<'brand, T, C, Q>) -> R,
    ) -> R
    where
        T: PrimInt + Signed,
        C: PrimInt + Signed,
        Q: Quay,
    {
        func(ProposeCtx {
            berth,
            problem,
            stamp: Version::default(),
            _brand: PhantomData,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MovableHandle<'brand> {
    id: RequestId,
    _b: PhantomData<&'brand ()>,
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
    _b: PhantomData<&'brand ()>,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProposeCtx<'brand, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    berth: &'brand BerthOccupancy<T, Q>,
    problem: &'brand Problem<T, C>,
    stamp: Version,
    _brand: PhantomData<&'brand mut &'brand ()>,
}

impl<'brand, T, C, Q> ProposeCtx<'brand, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    pub fn new(berth: &'brand BerthOccupancy<T, Q>, problem: &'brand Problem<T, C>) -> Self {
        Self {
            berth,
            problem,
            stamp: Version::default(),
            _brand: PhantomData,
        }
    }

    #[inline]
    pub fn berth(&self) -> &'brand BerthOccupancy<T, Q> {
        self.berth
    }

    #[inline]
    pub fn problem(&self) -> &'brand Problem<T, C> {
        self.problem
    }

    #[inline]
    pub fn request(&self, id: RequestId) -> Result<&Request<T, C>, PlanError> {
        if let Some(r) = self.problem.unassigned().get(&id) {
            return Ok(r);
        }
        if let Some(fx) = self.problem.preassigned().get(&id) {
            return Ok(fx.assignment().request());
        }
        Err(PlanError::UnknownRequest(id))
    }

    #[inline]
    pub fn baseline_assignment(
        &self,
        id: RequestId,
    ) -> Result<Option<&Assignment<T, C>>, PlanError> {
        if self.problem.unassigned().contains_key(&id) {
            return Ok(None);
        }
        if let Some(fx) = self.problem.preassigned().get(&id) {
            return Ok(Some(fx.assignment()));
        }
        Err(PlanError::UnknownRequest(id))
    }

    #[inline]
    pub fn is_locked(&self, id: RequestId) -> Result<bool, PlanError> {
        if self.problem.unassigned().contains_key(&id) {
            return Ok(false);
        }
        if self.problem.preassigned().contains_key(&id) {
            return Ok(true);
        }
        Err(PlanError::UnknownRequest(id))
    }

    #[inline]
    pub fn job_time_window(&self, id: RequestId) -> Result<&TimeInterval<T>, PlanError> {
        Ok(self.request(id)?.feasible_time_window())
    }

    #[inline]
    pub fn job_space_window(&self, id: RequestId) -> Result<&SpaceInterval, PlanError> {
        Ok(self.request(id)?.feasible_space_window())
    }

    #[inline]
    pub fn movable_handles(&'brand self) -> impl Iterator<Item = MovableHandle<'brand>> + 'brand {
        self.problem
            .unassigned()
            .keys()
            .copied()
            .map(|id| MovableHandle {
                id,
                _b: PhantomData,
            })
    }

    #[inline]
    pub fn fixed_handles(&'brand self) -> impl Iterator<Item = FixedHandle<'brand>> + 'brand {
        self.problem
            .preassigned()
            .keys()
            .copied()
            .map(|id| FixedHandle {
                id,
                _b: PhantomData,
            })
    }

    #[inline]
    pub fn movable_requests(
        &'brand self,
    ) -> impl Iterator<Item = (MovableHandle<'brand>, &'brand Request<T, C>)> + 'brand {
        self.problem.unassigned().iter().map(|(&id, req)| {
            (
                MovableHandle {
                    id,
                    _b: PhantomData,
                },
                req,
            )
        })
    }

    #[inline]
    pub fn fixed_assignments(
        &'brand self,
    ) -> impl Iterator<Item = (FixedHandle<'brand>, &'brand Assignment<T, C>)> + 'brand {
        self.problem.preassigned().iter().map(|(&id, fx)| {
            (
                FixedHandle {
                    id,
                    _b: PhantomData,
                },
                fx.assignment(),
            )
        })
    }

    #[inline]
    pub fn movable_handle(&self, id: RequestId) -> Result<MovableHandle<'brand>, PlanError> {
        if self.problem.unassigned().contains_key(&id) {
            Ok(MovableHandle {
                id,
                _b: PhantomData,
            })
        } else if self.problem.preassigned().contains_key(&id) {
            Err(PlanError::Locked(id))
        } else {
            Err(PlanError::UnknownRequest(id))
        }
    }

    #[inline]
    pub fn fixed_handle(&self, id: RequestId) -> Result<FixedHandle<'brand>, PlanError> {
        if self.problem.preassigned().contains_key(&id) {
            Ok(FixedHandle {
                id,
                _b: PhantomData,
            })
        } else {
            Err(PlanError::UnknownRequest(id))
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Tentative<'brand, T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    a: Assignment<T, C>,
    _b: PhantomData<&'brand ()>,
}

impl<'brand, T, C> Tentative<'brand, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    pub fn assignment(&self) -> &Assignment<T, C> {
        &self.a
    }

    #[inline]
    pub fn new_branded(a: Assignment<T, C>) -> Self {
        Self { a, _b: PhantomData }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FreeSlot<T: PrimInt + Signed> {
    start_time: TimePoint<T>,
    free_run: SpaceInterval,
}

impl<T: PrimInt + Signed> FreeSlot<T> {
    #[inline]
    fn new(start_time: TimePoint<T>, free_run: SpaceInterval) -> Self {
        Self {
            start_time,
            free_run,
        }
    }

    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }

    #[inline]
    pub fn free_run(&self) -> SpaceInterval {
        self.free_run
    }
}

impl<T: PrimInt + Signed + Display> Display for FreeSlot<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "FreeSlot(start_time: {}, free_run: {})",
            self.start_time, self.free_run
        )
    }
}

pub struct Explorer<'ctx, 'ovl, 'ed, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
{
    ctx: &'ctx ProposeCtx<'ctx, T, C, Q>,
    overlay: &'ovl BerthOccupancyOverlay<T>,
    edits: &'ed [AssignEdit<T>],
}

impl<'ctx, 'ovl, 'ed, T, C, Q> Display for Explorer<'ctx, 'ovl, 'ed, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Explorer")
    }
}

impl<'ctx, 'ovl, 'ed, T, C, Q> Explorer<'ctx, 'ovl, 'ed, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
{
    pub fn new(
        ctx: &'ctx ProposeCtx<'ctx, T, C, Q>,
        overlay: &'ovl BerthOccupancyOverlay<T>,
        edits: &'ed [AssignEdit<T>],
    ) -> Self {
        Self {
            ctx,
            overlay,
            edits,
        }
    }

    pub fn iter_tentatives(&self) -> impl Iterator<Item = Tentative<'ctx, T, C>> + '_ {
        let baseline = self
            .ctx
            .problem()
            .preassigned()
            .iter()
            .filter(move |(id, _)| {
                !self.edits.iter().any(|e| {
                    matches!(
                        *e,
                        AssignEdit::Clear(cid) if cid == **id
                    )
                })
            })
            .map(|(_, fx)| Tentative::new_branded(*fx.assignment()));

        let sets = self.edits.iter().filter_map(move |e| match *e {
            AssignEdit::Set(re) => {
                let req = *self.ctx.request(re.id()).ok()?;
                Some(Tentative::new_branded(Assignment::new(
                    req,
                    re.space().start(),
                    re.time().start(),
                )))
            }
            _ => None,
        });

        baseline.chain(sets)
    }

    pub fn iter_free_slots(
        &self,
        h: MovableHandle<'ctx>,
    ) -> Result<impl Iterator<Item = FreeSlot<T>> + 'ctx + 'ovl, PlanError> {
        let id = h.id();
        let req = *self.ctx.request(id)?;
        if self.ctx.is_locked(id)? {
            return Err(PlanError::Locked(id));
        }

        Ok(FreePlacementIter::new(
            self.ctx.berth,
            *self.ctx.job_time_window(id)?,
            req.processing_duration(),
            req.length(),
            *self.ctx.job_space_window(id)?,
            Some(self.overlay),
        )
        .map(|(t, run)| FreeSlot::new(t, run)))
    }

    #[inline]
    pub fn is_free(&self, time: TimeInterval<T>, space: SpaceInterval) -> bool {
        AvailabilityView::new(self.ctx.berth, time).is_free_under(space, Some(self.overlay))
    }
}

pub struct PlanBuilder<'brand, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
{
    ctx: &'brand ProposeCtx<'brand, T, C, Q>,
    overlay: BerthOccupancyOverlay<T>,
    ops: Vec<BerthOccupancyChangeOperation<T>>,
    edits: Vec<AssignEdit<T>>,
    staging: Staging<T>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RemoveResult<T: PrimInt + Signed> {
    Noop,
    Freed(FreeSlot<T>),
}

impl<T: PrimInt + Signed + Display> std::fmt::Display for RemoveResult<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RemoveResult::Noop => write!(f, "Noop"),
            RemoveResult::Freed(slot) => write!(f, "Freed({})", slot),
        }
    }
}

impl<'brand, T, C, Q> PlanBuilder<'brand, T, C, Q>
where
    T: PrimInt + Signed + Hash,
    C: PrimInt + Signed,
    Q: Quay,
{
    #[inline]
    pub fn new(ctx: &'brand ProposeCtx<'brand, T, C, Q>) -> Self {
        Self {
            ctx,
            overlay: BerthOccupancyOverlay::new(),
            ops: Vec::new(),
            edits: Vec::new(),
            staging: Staging::default(),
        }
    }

    #[inline]
    pub fn explorer(&self) -> Explorer<'brand, '_, '_, T, C, Q> {
        Explorer::new(self.ctx, &self.overlay, &self.edits)
    }

    #[inline]
    pub fn with_explorer<F, R>(&self, f: F) -> R
    where
        F: for<'ovl, 'ed> FnOnce(Explorer<'brand, 'ovl, 'ed, T, C, Q>) -> R,
    {
        f(self.explorer())
    }

    pub fn remove(
        &mut self,
        tentative: &Tentative<'brand, T, C>,
    ) -> Result<RemoveResult<T>, PlanError> {
        let id = tentative.assignment().request().id();

        if self.ctx.is_locked(id)? {
            return Err(PlanError::Locked(id));
        }

        match self.cancel_planned(id) {
            RemoveResult::Freed(slot) => return Ok(RemoveResult::Freed(slot)),
            RemoveResult::Noop => {}
        }

        if self
            .edits
            .iter()
            .any(|e| matches!(e, AssignEdit::Clear(cid) if *cid == id))
        {
            if let Some(baseline) = self.ctx.baseline_assignment(id)? {
                let rect = OccupancyRect::from(baseline);
                if AvailabilityView::new(self.ctx.berth, *rect.time())
                    .is_free_under(*rect.space(), Some(&self.overlay))
                {
                    return Ok(RemoveResult::Freed(FreeSlot::new(
                        rect.time().start(),
                        *rect.space(),
                    )));
                }
            }
            return Ok(RemoveResult::Noop);
        }

        if self.ctx.baseline_assignment(id)?.is_some() {
            return self.ensure_baseline_cleared_if_any(id);
        }

        Ok(RemoveResult::Noop)
    }

    pub fn place_into_free_slot(
        &mut self,
        movable_handle: MovableHandle<'brand>,
        free_slot: FreeSlot<T>,
        place_fn: impl Fn(SpaceInterval, SpaceLength) -> SpacePosition,
    ) -> Result<(), PlanError> {
        let request_id = movable_handle.id();
        let _ = self.cancel_planned(request_id);

        let request_ref = self.ctx.request(request_id)?;
        let request_length = request_ref.length();
        let processing_duration = request_ref.processing_duration();
        let free_run_interval: SpaceInterval = free_slot.free_run();
        let chosen_start_position: SpacePosition = place_fn(free_run_interval, request_length);
        let chosen_end_position =
            SpacePosition::new(chosen_start_position.value() + request_length.value());
        let target_space_interval = SpaceInterval::new(chosen_start_position, chosen_end_position);
        if target_space_interval.start() < free_run_interval.start()
            || target_space_interval.end() > free_run_interval.end()
        {
            return Err(PlanError::SlotStale(request_id));
        }

        let slot_start_time = free_slot.start_time();
        let slot_end_time = TimePoint::new(slot_start_time.value() + processing_duration.value());
        let target_time_interval = TimeInterval::new(slot_start_time, slot_end_time);

        let _ = self.ensure_baseline_cleared_if_any(request_id)?;

        let feasible_time_window = self.ctx.job_time_window(request_id)?;
        let feasible_space_window = self.ctx.job_space_window(request_id)?;
        if target_time_interval.start() < feasible_time_window.start()
            || target_time_interval.end() > feasible_time_window.end()
            || target_space_interval.start() < feasible_space_window.start()
            || target_space_interval.end() > feasible_space_window.end()
        {
            return Err(PlanError::SlotStale(request_id));
        }

        if !AvailabilityView::new(self.ctx.berth, target_time_interval)
            .is_free_under(target_space_interval, Some(&self.overlay))
        {
            return Err(PlanError::Overlap);
        }

        if let Some(prev) = self.staging.remove_set(request_id) {
            if let Some(i) = self
                .edits
                .iter()
                .position(|e| matches!(e, AssignEdit::Set(x) if x.id() == request_id))
            {
                self.edits.swap_remove(i);
            }
            if let Some(i) = self
                .ops
                .iter()
                .position(|op| matches!(op, BerthOccupancyChangeOperation::Occupy(r) if *r == prev))
            {
                self.ops.swap_remove(i);
            }
            self.undo_occupy(prev.time, prev.space);
        }

        let rect = OccupancyRect::from((target_time_interval, target_space_interval));
        self.staging.put_set(request_id, rect);
        self.apply_occupy(target_time_interval, target_space_interval);
        self.ops
            .push(BerthOccupancyChangeOperation::Occupy(OccupancyRect::new(
                target_time_interval,
                target_space_interval,
            )));
        self.edits.push(AssignEdit::Set(RequestEdit::new(
            request_id,
            target_time_interval,
            target_space_interval,
        )));

        Ok(())
    }

    pub fn finish(self) -> Result<Plan<T>, PlanError> {
        let mut tmp = BerthOccupancyOverlay::new();
        for op in &self.ops {
            let r = op.rect();
            match op {
                BerthOccupancyChangeOperation::Free(_) => {
                    tmp.free(self.ctx.berth, *r.time(), *r.space());
                }
                BerthOccupancyChangeOperation::Occupy(_) => {
                    if !AvailabilityView::new(self.ctx.berth, *r.time())
                        .is_free_under(*r.space(), Some(&tmp))
                    {
                        return Err(PlanError::Overlap);
                    }
                    tmp.occupy(self.ctx.berth, *r.time(), *r.space());
                }
            }
        }

        let mut occupy_rects = HashSet::new();
        let mut free_rects = HashSet::new();
        for op in &self.ops {
            match op {
                BerthOccupancyChangeOperation::Occupy(r) => {
                    occupy_rects.insert(*r);
                }
                BerthOccupancyChangeOperation::Free(r) => {
                    free_rects.insert(*r);
                }
            }
        }

        let mut set_rects: HashSet<OccupancyRect<T>> = HashSet::new();
        let mut clear_rects: HashSet<OccupancyRect<T>> = HashSet::new();

        for edit in &self.edits {
            match edit {
                AssignEdit::Set(re) => {
                    let time_window = self.ctx.job_time_window(re.id())?;
                    let sw = self.ctx.job_space_window(re.id())?;
                    if re.time().start() < time_window.start()
                        || re.time().end() > time_window.end()
                        || re.space().start() < sw.start()
                        || re.space().end() > sw.end()
                    {
                        return Err(PlanError::SlotStale(re.id()));
                    }
                    let k = OccupancyRect::from(re);
                    if !occupy_rects.contains(&k) {
                        return Err(PlanError::SlotStale(re.id()));
                    }
                    set_rects.insert(k);
                }
                AssignEdit::Clear(id) => {
                    let Some(asg) = self.ctx.baseline_assignment(*id)? else {
                        return Err(PlanError::NoBaselineAssignment(*id));
                    };

                    let k: OccupancyRect<T> = OccupancyRect::from(asg);
                    if !free_rects.contains(&k) {
                        return Err(PlanError::SlotStale(*id));
                    }
                    clear_rects.insert(k);
                }
            }
        }

        for k in &occupy_rects {
            if !set_rects.contains(k) {
                return Err(PlanError::SlotStale(RequestId::new(0)));
            }
        }
        for k in &free_rects {
            if !clear_rects.contains(k) {
                return Err(PlanError::SlotStale(RequestId::new(0)));
            }
        }

        Ok(Plan::new(self.ops, self.edits, self.ctx.stamp))
    }

    #[inline]
    fn apply_occupy(&mut self, time: TimeInterval<T>, space: SpaceInterval) {
        self.overlay.occupy(self.ctx.berth, time, space);
    }
    #[inline]
    fn undo_occupy(&mut self, time: TimeInterval<T>, space: SpaceInterval) {
        self.overlay.undo_occupy(self.ctx.berth, time, space);
    }
    #[inline]
    fn apply_free(&mut self, time: TimeInterval<T>, space: SpaceInterval) {
        self.overlay.free(self.ctx.berth, time, space);
    }
    #[inline]
    fn undo_free(&mut self, time: TimeInterval<T>, space: SpaceInterval) {
        self.overlay.undo_free(self.ctx.berth, time, space);
    }

    fn ensure_baseline_cleared_if_any(
        &mut self,
        request_id: RequestId,
    ) -> Result<RemoveResult<T>, PlanError> {
        if self
            .edits
            .iter()
            .any(|edit| matches!(edit, AssignEdit::Clear(id) if *id == request_id))
        {
            return Ok(RemoveResult::Noop);
        }
        let Some(baseline) = self.ctx.baseline_assignment(request_id)? else {
            return Ok(RemoveResult::Noop);
        };
        let rect: OccupancyRect<T> = OccupancyRect::from(baseline);
        self.ops.push(BerthOccupancyChangeOperation::Free(rect));
        self.edits.push(AssignEdit::Clear(request_id));
        if let Some(prev) = self.staging.remove_clear(request_id) {
            self.undo_free(prev.time, prev.space);
        }

        self.staging.put_clear(request_id, rect);
        self.apply_free(*rect.time(), *rect.space());

        Ok(RemoveResult::Freed(FreeSlot::new(
            rect.time().start(),
            *rect.space(),
        )))
    }

    fn cancel_planned(&mut self, id: RequestId) -> RemoveResult<T> {
        if let Some(rect) = self.staging.remove_set(id) {
            if let Some(i) = self
                .edits
                .iter()
                .position(|e| matches!(e, AssignEdit::Set(x) if x.id() == id))
            {
                self.edits.swap_remove(i);
            }
            if let Some(i) = self
                .ops
                .iter()
                .position(|op| matches!(op, BerthOccupancyChangeOperation::Occupy(r) if *r == rect))
            {
                self.ops.swap_remove(i);
            }
            self.undo_occupy(rect.time, rect.space);

            return RemoveResult::Freed(FreeSlot::new(rect.time.start(), rect.space));
        }

        RemoveResult::Noop
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quay::BTreeMapQuay;
    use dock_alloc_core::domain::{
        Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
    };
    use dock_alloc_model::{Assignment, Fixed, ProblemBuilder, Request, RequestId};

    fn mk_req(
        id: u64,
        len: usize,
        proc: i64,
        t0: i64,
        t1: i64,
        s0: usize,
        s1: usize,
    ) -> Request<i64, i64> {
        Request::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimeDelta::new(proc),
            SpacePosition::new(0),
            Cost::new(0),
            Cost::new(0),
            TimeInterval::new(TimePoint::new(t0), TimePoint::new(t1)),
            SpaceInterval::new(SpacePosition::new(s0), SpacePosition::new(s1)),
        )
        .unwrap()
    }

    fn unchecked_for_tests<'brand, T: PrimInt + Signed, C: PrimInt + Signed>(
        a: Assignment<T, C>,
    ) -> Tentative<'brand, T, C> {
        Tentative::new_branded(a)
    }

    fn mk_ctx<'a>(
        berth: &'a BerthOccupancy<i64, BTreeMapQuay>,
        problem: &'a dock_alloc_model::Problem<i64, i64>,
    ) -> ProposeCtx<'a, i64, i64, BTreeMapQuay> {
        ProposeCtx::new(berth, problem)
    }

    #[test]
    fn test_footprint_from_operations_hull() {
        let t_a = TimeInterval::new(TimePoint::new(0), TimePoint::new(5));
        let s_a = SpaceInterval::new(SpacePosition::new(1), SpacePosition::new(4));
        let t_b = TimeInterval::new(TimePoint::new(3), TimePoint::new(10));
        let s_b = SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(9));

        let ops = vec![
            BerthOccupancyChangeOperation::Free(OccupancyRect::new(t_a, s_a)),
            BerthOccupancyChangeOperation::Occupy(OccupancyRect::new(t_b, s_b)),
        ];
        let fp = Footprint::from(ops.as_slice());
        assert_eq!(fp.time().start().value(), 0);
        assert_eq!(fp.time().end().value(), 10);
        assert_eq!(fp.space().start().value(), 1);
        assert_eq!(fp.space().end().value(), 9);
    }

    #[test]
    fn test_explorer_free_slots_yield_valid_slots() {
        let quay_length = SpaceLength::new(20);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let req = mk_req(1, 4, 3, 0, 10, 0, 20);
        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(req).unwrap();
            pb.build()
        };

        let ctx = mk_ctx(&berth, &problem);
        let overlay = BerthOccupancyOverlay::new();
        let edits = Vec::new();

        let explorer = Explorer::new(&ctx, &overlay, &edits);
        let mh = ctx.movable_handle(RequestId::new(1)).unwrap();
        let slots: Vec<_> = explorer.iter_free_slots(mh).unwrap().take(3).collect();

        assert!(
            !slots.is_empty(),
            "expected at least one free slot on empty berth"
        );
        for s in &slots {
            // space feasibility: run must fit the request length and be within SW
            let sw = req.feasible_space_window();
            let run = s.free_run();
            let extent = run.end().value() - run.start().value();
            assert!(extent >= req.length().value(), "run too small for request");
            assert!(run.start() >= sw.start(), "run starts before SW.start");
            assert!(run.end() <= sw.end(), "run ends after SW.end");

            // time feasibility: slot window must allow full processing
            let tw = req.feasible_time_window();
            let end_time =
                TimePoint::new(s.start_time().value() + req.processing_duration().value());
            assert!(s.start_time() >= tw.start(), "slot starts before TW.start");
            assert!(end_time <= tw.end(), "slot would finish after TW.end");
        }
    }

    #[test]
    fn test_move_flow_from_unassigned_and_finish() {
        let quay_length = SpaceLength::new(20);
        let mut berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        // put a blocker to make it non-trivial
        berth.occupy(
            TimeInterval::new(TimePoint::new(10), TimePoint::new(15)),
            SpaceInterval::new(SpacePosition::new(15), SpacePosition::new(20)),
        );

        let req = mk_req(1, 4, 3, 0, 20, 0, 20);
        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(req).unwrap();
            pb.build()
        };

        let ctx = mk_ctx(&berth, &problem);
        let mut builder = PlanBuilder::new(&ctx);

        let id = RequestId::new(1);
        let req_copy = *ctx.request(id).expect("request exists");
        let dummy_tent = unchecked_for_tests(Assignment::new(
            req_copy,
            SpacePosition::new(0),
            TimePoint::new(0),
        ));
        assert!(matches!(
            builder.remove(&dummy_tent),
            Ok(super::RemoveResult::Noop)
        ));

        let mh = ctx.movable_handle(RequestId::new(1)).unwrap();
        let slot = builder.with_explorer(|explorer| {
            explorer
                .iter_free_slots(mh)
                .unwrap()
                .next()
                .expect("a free slot exists")
        });
        builder
            .place_into_free_slot(mh, slot, |run, _len| run.start())
            .unwrap();

        let plan = builder.finish().expect("finish must validate");
        assert!(!plan.is_empty());
        assert_eq!(plan.operations().len(), 1, "only Occupy expected");
        assert_eq!(plan.edits().len(), 1, "only Set expected");
    }

    #[test]
    fn test_remove_errors_on_locked_preassigned() {
        let quay_length = SpaceLength::new(10);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let req = mk_req(1, 2, 1, 0, 10, 0, 10);
        let asg = Assignment::new(req, SpacePosition::new(0), TimePoint::new(0));

        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_preassigned(Fixed::new(asg)).unwrap();
            pb.build()
        };

        let ctx = mk_ctx(&berth, &problem);
        let mut builder = PlanBuilder::new(&ctx);

        let tent = unchecked_for_tests(Assignment::new(
            req,
            SpacePosition::new(0),
            TimePoint::new(0),
        ));
        let outcome = builder.remove(&tent);
        assert!(matches!(outcome, Err(PlanError::Locked(id)) if id == RequestId::new(1)));
    }

    #[test]
    fn test_remove_noop_when_no_baseline() {
        let quay_length = SpaceLength::new(10);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let req = mk_req(1, 2, 1, 0, 10, 0, 10);
        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(req).unwrap();
            pb.build()
        };

        let ctx = mk_ctx(&berth, &problem);
        let mut builder = PlanBuilder::new(&ctx);

        let tent = unchecked_for_tests(Assignment::new(
            req,
            SpacePosition::new(0),
            TimePoint::new(0),
        ));
        let outcome = builder.remove(&tent);
        assert!(matches!(outcome, Ok(super::RemoveResult::Noop)));
    }

    #[test]
    fn test_place_into_free_slot_rejects_bad_policy_outside_run() {
        let quay_length = SpaceLength::new(12);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let req = mk_req(1, 4, 3, 0, 10, 0, 12);
        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(req).unwrap();
            pb.build()
        };

        let ctx = mk_ctx(&berth, &problem);
        let mut builder = PlanBuilder::new(&ctx);

        let mh = ctx.movable_handle(RequestId::new(1)).unwrap();
        let slot = {
            let explorer = builder.explorer(); // &self borrow starts
            explorer
                .iter_free_slots(mh)
                .unwrap()
                .next()
                .expect("a free slot exists") // FreeSlot is Copy → owned value
        };
        // Malicious placement: start outside the free run -> must be SlotStale
        let bad_policy =
            |run: SpaceInterval, _len: SpaceLength| SpacePosition::new(run.end().value() + 1);
        let res = builder.place_into_free_slot(mh, slot, bad_policy);
        assert!(matches!(res, Err(PlanError::SlotStale(id)) if id == RequestId::new(1)));
    }

    #[test]
    fn test_explorer_is_free_rect_respects_overlay() {
        let quay_length = SpaceLength::new(10);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let req = mk_req(1, 2, 2, 0, 10, 0, 10);
        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(req).unwrap();
            pb.build()
        };

        let ctx = mk_ctx(&berth, &problem);
        let edits = Vec::new();

        let mut overlay = BerthOccupancyOverlay::new();
        overlay.add_occupy(
            TimePoint::new(0),
            SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(5)),
        );

        let explorer = Explorer::new(&ctx, &overlay, &edits);
        let rect = SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(4));
        assert!(
            !explorer.is_free(
                TimeInterval::new(TimePoint::new(0), TimePoint::new(1)),
                rect
            ),
            "occupied region must not be free"
        );

        let rect2 = SpaceInterval::new(SpacePosition::new(5), SpacePosition::new(7));
        assert!(
            explorer.is_free(
                TimeInterval::new(TimePoint::new(0), TimePoint::new(1)),
                rect2
            ),
            "non-overlapping region should be free"
        );
    }

    #[test]
    fn test_finish_can_be_empty() {
        let quay_length = SpaceLength::new(10);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let req = mk_req(1, 2, 1, 0, 10, 0, 10);
        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(req).unwrap();
            pb.build()
        };

        let ctx = mk_ctx(&berth, &problem);
        let builder = PlanBuilder::new(&ctx);

        let plan = builder.finish().expect("empty plan should validate");
        assert!(plan.is_empty(), "finish() should allow empty plans");
        assert_eq!(plan.operations().len(), 0);
        assert_eq!(plan.edits().len(), 0);
    }

    #[test]
    fn test_finish_rejects_manual_inconsistency() {
        let quay_length = SpaceLength::new(20);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let req = mk_req(1, 4, 3, 0, 50, 0, 20);
        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(req).unwrap();
            pb.build()
        };

        let ctx = mk_ctx(&berth, &problem);
        let mut builder = PlanBuilder::new(&ctx);

        let space = SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(6));
        let time = TimeInterval::new(TimePoint::new(1), TimePoint::new(4));
        builder
            .ops
            .push(BerthOccupancyChangeOperation::Occupy(OccupancyRect::new(
                time, space,
            )));

        assert!(builder.finish().is_err());
    }

    #[test]
    fn test_remove_cancels_staged_set_and_yields_freed_then_explorer_recovers_slot() {
        use crate::quay::BTreeMapQuay;

        let quay_length = SpaceLength::new(30);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let req = mk_req(1, 5, 4, 0, 50, 0, 30);
        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(req).unwrap();
            pb.build()
        };
        let ctx = mk_ctx(&berth, &problem);

        let mut builder = PlanBuilder::new(&ctx);
        let mh = ctx.movable_handle(RequestId::new(1)).unwrap();

        // Place once (left-aligned)
        let slot = builder.with_explorer(|ex| ex.iter_free_slots(mh).unwrap().next().unwrap());
        let run = slot.free_run();
        let chosen_space = SpaceInterval::new(
            run.start(),
            SpacePosition::new(run.start().value() + req.length().value()),
        );
        builder
            .place_into_free_slot(mh, slot, |r, _| r.start())
            .expect("initial placement must succeed");

        // Remove the staged Set, get the freed slot back
        let dummy_tent = unchecked_for_tests(Assignment::new(
            *ctx.request(RequestId::new(1)).unwrap(),
            chosen_space.start(),
            slot.start_time(),
        ));
        let freed_slot = match builder.remove(&dummy_tent).expect("remove must succeed") {
            RemoveResult::Freed(s) => s,
            _ => panic!("expected Freed"),
        };

        // The explorer should enumerate some slot that can host the freed rectangle.
        // Don't require equal start_time; allow coalesced/canonical starts.
        let proc = req.processing_duration().value();
        let freed_ok_according_to_iterator = builder.with_explorer(|ex| {
            ex.iter_free_slots(mh).unwrap().take(256).any(|s| {
                // space containment
                s.free_run().start().value() <= freed_slot.free_run().start().value()
                        && s.free_run().end().value() >= freed_slot.free_run().end().value()
                        // time containment: the enumerated start can begin at or before freed start,
                        // but must allow finishing at freed_start + proc
                        && s.start_time().value() <= freed_slot.start_time().value()
                        && s.start_time().value() + proc >= freed_slot.start_time().value()
            })
        });
        assert!(
            freed_ok_according_to_iterator,
            "explorer should enumerate a slot that can host the freed rectangle (not necessarily same start_time)"
        );

        // Strong end-to-end witness: re-place exactly into the freed slot must succeed.
        builder
            .place_into_free_slot(mh, freed_slot, |run, _| run.start())
            .expect("re-placing into the freed slot should succeed");
    }

    #[test]
    fn test_iter_tentatives_includes_sets_and_excludes_cleared_preassigned() {
        use crate::quay::BTreeMapQuay;

        // Problem with one preassigned (locked) and one movable request.
        let quay_length = SpaceLength::new(25);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let movable = mk_req(10, 5, 3, 0, 40, 0, 25);
        let fixed_req = mk_req(20, 4, 2, 0, 40, 0, 25);
        let fixed_asg = Assignment::new(fixed_req, SpacePosition::new(6), TimePoint::new(5));

        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(movable).unwrap();
            pb.add_preassigned(Fixed::new(fixed_asg)).unwrap();
            pb.build()
        };

        let ctx = mk_ctx(&berth, &problem);
        let mut builder = PlanBuilder::new(&ctx);

        // Place the movable request somewhere.
        let mh = ctx.movable_handle(RequestId::new(10)).unwrap();
        let slot = builder.with_explorer(|ex| ex.iter_free_slots(mh).unwrap().next().unwrap());
        builder
            .place_into_free_slot(mh, slot, |run, _len| run.start())
            .unwrap();

        // Tentatives now include the Set + (by default) the preassigned baseline.
        // But we want to ensure that if the preassigned is *cleared* (via ensure_baseline_cleared_if_any),
        // it disappears from the iterator, leaving only the Set.
        let /* RemoveResult */ _ = builder
            .ensure_baseline_cleared_if_any(RequestId::new(20))
            .expect("clear baseline must succeed for the fixed id"); // returns Freed(..)

        let tents: Vec<_> = builder.with_explorer(|ex| ex.iter_tentatives().collect());
        assert_eq!(
            tents.len(),
            1,
            "only the staged Set should remain after clearing the baseline"
        );

        let a = tents[0].assignment();
        assert_eq!(a.request().id(), RequestId::new(10));
        // Plausibility: staged Set should match the slot's start time.
        assert_eq!(a.start_time().value(), slot.start_time().value());
    }

    #[test]
    fn test_remove_noop_preserves_freedom_and_explorer_slots() {
        use crate::quay::BTreeMapQuay;

        let quay_length = SpaceLength::new(18);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let req = mk_req(1, 3, 2, 0, 30, 0, 18);
        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(req).unwrap();
            pb.build()
        };
        let ctx = mk_ctx(&berth, &problem);
        let mut builder = PlanBuilder::new(&ctx);
        let mh = ctx.movable_handle(RequestId::new(1)).unwrap();

        // Count some slots before a no-op remove.
        let count_before =
            builder.with_explorer(|ex| ex.iter_free_slots(mh).unwrap().take(16).count());

        // Remove with nothing staged/baseline → Noop.
        let dummy = unchecked_for_tests(Assignment::new(
            *ctx.request(RequestId::new(1)).unwrap(),
            SpacePosition::new(0),
            TimePoint::new(0),
        ));
        let res = builder.remove(&dummy).expect("remove should not error");
        assert!(matches!(res, RemoveResult::Noop));

        // Slots should remain unchanged.
        let count_after =
            builder.with_explorer(|ex| ex.iter_free_slots(mh).unwrap().take(16).count());
        assert_eq!(
            count_before, count_after,
            "no-op remove should not change free slots"
        );
    }

    #[test]
    fn test_is_free_reflects_remove_freed_region() {
        use crate::quay::BTreeMapQuay;

        let quay_length = SpaceLength::new(22);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let req = mk_req(1, 6, 4, 0, 50, 0, 22);
        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(req).unwrap();
            pb.build()
        };
        let ctx = mk_ctx(&berth, &problem);

        let mut builder = PlanBuilder::new(&ctx);
        let mh = ctx.movable_handle(RequestId::new(1)).unwrap();

        let slot = builder.with_explorer(|ex| ex.iter_free_slots(mh).unwrap().next().unwrap());
        let run = slot.free_run();
        let chosen_space = SpaceInterval::new(
            run.start(),
            SpacePosition::new(run.start().value() + req.length().value()),
        );

        builder
            .place_into_free_slot(mh, slot, |r, _| r.start())
            .unwrap();

        // Now remove it and assert is_free on that exact time/space.
        let dummy = unchecked_for_tests(Assignment::new(
            *ctx.request(RequestId::new(1)).unwrap(),
            chosen_space.start(),
            slot.start_time(),
        ));
        let res = builder.remove(&dummy).unwrap();
        let freed = match res {
            RemoveResult::Freed(s) => s,
            _ => panic!("expected Freed"),
        };

        // Recreate the time interval to check `is_free`.
        let end_t = TimePoint::new(freed.start_time().value() + req.processing_duration().value());
        let time = TimeInterval::new(freed.start_time(), end_t);
        let rect = freed.free_run();

        let ok = builder.with_explorer(|ex| ex.is_free(time, rect));
        assert!(ok, "region reported by remove() must be free under overlay");
    }

    #[test]
    fn test_overlap_detected_when_trying_to_place_into_occupied_rect() {
        use crate::quay::BTreeMapQuay;

        let quay_length = SpaceLength::new(40);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        // Two movable requests with same windows/length so they conflict if placed identically.
        let r1 = mk_req(1, 7, 4, 0, 60, 0, 40);
        let r2 = mk_req(2, 7, 4, 0, 60, 0, 40);

        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_unassigned_request(r1).unwrap();
            pb.add_unassigned_request(r2).unwrap();
            pb.build()
        };
        let ctx = mk_ctx(&berth, &problem);

        let mut builder = PlanBuilder::new(&ctx);

        // Place request 1 at some slot (left-aligned).
        let mh1 = ctx.movable_handle(RequestId::new(1)).unwrap();
        let slot1 = builder.with_explorer(|ex| ex.iter_free_slots(mh1).unwrap().next().unwrap());
        let run1 = slot1.free_run();
        let chosen_space1 = SpaceInterval::new(
            run1.start(),
            SpacePosition::new(run1.start().value() + r1.length().value()),
        );
        builder
            .place_into_free_slot(mh1, slot1, |r, _| r.start())
            .unwrap();

        // Now attempt to place r2 into EXACTLY the same rect/time → must be Overlap.
        let mh2 = ctx.movable_handle(RequestId::new(2)).unwrap();
        let fake_slot_for_r2 = FreeSlot::new(slot1.start_time(), chosen_space1);
        let err = builder.place_into_free_slot(mh2, fake_slot_for_r2, |r, _| r.start());
        assert!(matches!(err, Err(PlanError::Overlap)));
    }

    #[test]
    fn test_finish_after_clear_baseline_only_is_valid() {
        use crate::quay::BTreeMapQuay;

        // A plan that only clears a preassigned baseline (free + clear) should validate.
        let quay_length = SpaceLength::new(20);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);

        let fixed_req = mk_req(100, 4, 2, 0, 50, 0, 20);
        let fixed_asg = Assignment::new(fixed_req, SpacePosition::new(3), TimePoint::new(7));

        let problem = {
            let mut pb = ProblemBuilder::new(quay_length);
            pb.add_preassigned(Fixed::new(fixed_asg)).unwrap();
            pb.build()
        };
        let ctx = mk_ctx(&berth, &problem);

        let mut builder = PlanBuilder::new(&ctx);
        // Use the internal helper to stage the free/clear pair.
        let out = builder
            .ensure_baseline_cleared_if_any(RequestId::new(100))
            .expect("must be able to clear baseline");
        assert!(matches!(out, RemoveResult::Freed(_)));

        // Now finish() should validate (ops: 1 Free, edits: 1 Clear).
        let plan = builder
            .finish()
            .expect("plan with only ‘clear baseline’ should be consistent");
        assert_eq!(plan.operations().len(), 1);
        assert_eq!(plan.edits().len(), 1);
    }
}
