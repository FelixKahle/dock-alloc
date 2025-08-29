// Copyright (c) 2025 Felix Kahle.
// MIT license header omitted for brevity (keep yours)

use crate::{
    constraints::ConstraintSystem,
    domain::Version,
    lens::{AvailabilityView, BerthOccupancyOverlay, FreePlacementIter},
    occ::BerthOccupancy,
    quay::Quay,
    scheduling_read::ModelAccess,
};
use dock_alloc_core::domain::SpacePosition;
use dock_alloc_core::domain::{SpaceInterval, TimeInterval, TimePoint};
use dock_alloc_model::RequestId;
use num_traits::{PrimInt, Signed};
use std::{collections::HashSet, fmt::Display, hash::Hash};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BerthOccupancyChangePayload<T: PrimInt + Signed> {
    time: TimeInterval<T>,
    space: SpaceInterval,
}

impl<T: PrimInt + Signed> BerthOccupancyChangePayload<T> {
    pub fn new(time: TimeInterval<T>, space: SpaceInterval) -> Self {
        Self { time, space }
    }
    pub fn time(&self) -> &TimeInterval<T> {
        &self.time
    }
    pub fn space(&self) -> &SpaceInterval {
        &self.space
    }
}

impl<T: PrimInt + Signed + Display> Display for BerthOccupancyChangePayload<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "BerthOccupancyChange(time: {}, space: {})",
            self.time, self.space
        )
    }
}

impl<T: PrimInt + Signed> From<(TimeInterval<T>, SpaceInterval)>
    for BerthOccupancyChangePayload<T>
{
    fn from(v: (TimeInterval<T>, SpaceInterval)) -> Self {
        Self::new(v.0, v.1)
    }
}
impl<T: PrimInt + Signed> From<(&TimeInterval<T>, &SpaceInterval)>
    for BerthOccupancyChangePayload<T>
{
    fn from(v: (&TimeInterval<T>, &SpaceInterval)) -> Self {
        Self::new(*v.0, *v.1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BerthOccupancyChangeOperation<T: PrimInt + Signed> {
    Free(BerthOccupancyChangePayload<T>),
    Occupy(BerthOccupancyChangePayload<T>),
}
impl<T: PrimInt + Signed> BerthOccupancyChangeOperation<T> {
    pub fn payload(&self) -> &BerthOccupancyChangePayload<T> {
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RequestEdit<T: PrimInt + Signed> {
    id: RequestId,
    time: TimeInterval<T>,
    space: SpaceInterval,
}
impl<T: PrimInt + Signed> RequestEdit<T> {
    pub fn new(id: RequestId, time: TimeInterval<T>, space: SpaceInterval) -> Self {
        Self { id, time, space }
    }
    pub fn id(&self) -> RequestId {
        self.id
    }
    pub fn time(&self) -> TimeInterval<T> {
        self.time
    }
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

#[derive(Clone, Debug, PartialEq, Eq)]
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
    let start = if a.start().value() <= b.start().value() {
        a.start()
    } else {
        b.start()
    };
    let end = if a.end().value() >= b.end().value() {
        a.end()
    } else {
        b.end()
    };
    TimeInterval::new(start, end)
}
#[inline]
fn space_hull(a: &SpaceInterval, b: &SpaceInterval) -> SpaceInterval {
    let start = if a.start().value() <= b.start().value() {
        a.start()
    } else {
        b.start()
    };
    let end = if a.end().value() >= b.end().value() {
        a.end()
    } else {
        b.end()
    };
    SpaceInterval::new(start, end)
}

impl<T: PrimInt + Signed> From<&[BerthOccupancyChangeOperation<T>]> for Footprint<T> {
    fn from(ops: &[BerthOccupancyChangeOperation<T>]) -> Self {
        ops.iter()
            .map(|op| op.payload())
            .map(|d| (*d.time(), *d.space()))
            .reduce(|(t1, s1), (t2, s2)| (time_hull(&t1, &t2), space_hull(&s1, &s2)))
            .map(|(time, space)| Footprint::new(time, space))
            .unwrap_or_default()
    }
}
impl<T: PrimInt + Signed> From<&BerthOccupancyChangePayload<T>> for Footprint<T> {
    fn from(op: &BerthOccupancyChangePayload<T>) -> Self {
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

#[derive(Clone, Debug)]
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
            "SlotToken(start_time: {}, space: {})",
            self.start_time, self.space
        )
    }
}

pub struct ProposeCtx<'a, T, C, Q, M, CS>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
    CS: ConstraintSystem<T, C, M>,
{
    pub(crate) berth: &'a BerthOccupancy<T, Q>,
    pub(crate) model: &'a M,
    pub(crate) cons: CS,
    stamp: Version,
    _phantom: core::marker::PhantomData<C>,
}

impl<'a, T, C, Q, M, CS> ProposeCtx<'a, T, C, Q, M, CS>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
    CS: ConstraintSystem<T, C, M>,
{
    pub fn new(berth: &'a BerthOccupancy<T, Q>, model: &'a M, cons: CS) -> Self {
        Self {
            berth,
            model,
            cons,
            stamp: Version::default(),
            _phantom: Default::default(),
        }
    }

    #[inline]
    pub fn job_time_window(&self, id: RequestId) -> TimeInterval<T> {
        self.cons.job_time_window(id)
    }
    #[inline]
    pub fn job_space_window(&self, id: RequestId) -> SpaceInterval {
        self.cons.job_space_window(id)
    }
}

pub struct Explorer<'a, T, C, Q, M, CS>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
    CS: ConstraintSystem<T, C, M>,
{
    ctx: &'a ProposeCtx<'a, T, C, Q, M, CS>,
    overlay: &'a BerthOccupancyOverlay<T>,
}

impl<'a, T, C, Q, M, CS> Explorer<'a, T, C, Q, M, CS>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
    CS: ConstraintSystem<T, C, M>,
    BerthOccupancy<T, Q>: crate::lens::TimelineSlices<T, Q>,
{
    #[inline]
    pub fn new(
        ctx: &'a ProposeCtx<'a, T, C, Q, M, CS>,
        overlay: &'a BerthOccupancyOverlay<T>,
    ) -> Self {
        Self { ctx, overlay }
    }

    pub fn iter_slots(
        &'a self,
        job: RequestId,
    ) -> impl Iterator<Item = BerthOccupancySlot<T>> + 'a {
        let req = self.ctx.model.request(job);
        let len = req.length();
        let proc = req.processing_duration();

        let tw = self.ctx.job_time_window(job);
        let sw = self.ctx.job_space_window(job);

        FreePlacementIter::new(self.ctx.berth, tw, proc, len, sw, Some(self.overlay)).map(
            move |(t0, space)| BerthOccupancySlot {
                start_time: t0,
                space,
            },
        )
    }

    #[inline]
    pub fn is_free(&self, time: TimeInterval<T>, space: SpaceInterval) -> bool {
        AvailabilityView::new(self.ctx.berth, time).is_free_under(space, Some(self.overlay))
    }
}

pub struct PlanBuilder<'a, T, C, Q, M, CS>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
    CS: ConstraintSystem<T, C, M>,
{
    ctx: &'a ProposeCtx<'a, T, C, Q, M, CS>,
    overlay: BerthOccupancyOverlay<T>,
    ops: Vec<BerthOccupancyChangeOperation<T>>,
    edits: Vec<AssignEdit<T>>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RemoveOutcome {
    Removed,
    Noop,
}

impl<'a, T, C, Q, M, CS> PlanBuilder<'a, T, C, Q, M, CS>
where
    T: PrimInt + Signed + Hash,
    C: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
    CS: ConstraintSystem<T, C, M>,
{
    pub fn new(ctx: &'a ProposeCtx<'a, T, C, Q, M, CS>) -> Self {
        Self {
            ctx,
            overlay: BerthOccupancyOverlay::new(),
            ops: Vec::new(),
            edits: Vec::new(),
        }
    }

    #[inline]
    pub fn explorer(&'a self) -> Explorer<'a, T, C, Q, M, CS> {
        Explorer::new(self.ctx, &self.overlay)
    }

    pub fn remove(&mut self, job: RequestId) -> Result<RemoveOutcome, CS::Violation> {
        self.ctx.cons.allowed_remove(job)?;

        if self
            .edits
            .iter()
            .any(|e| matches!(e, AssignEdit::Clear(id) if *id == job))
        {
            return Ok(RemoveOutcome::Noop);
        }

        let Some(asg) = self.ctx.model.assignment(job) else {
            return Ok(RemoveOutcome::Noop);
        };

        let req = self.ctx.model.request(job);
        let len = req.length();
        let proc = req.processing_duration();

        let s0 = asg.start_position();
        let s1 = SpacePosition::new(s0.value() + len.value());
        let space = SpaceInterval::new(s0, s1);

        let t0 = asg.start_time();
        let t1 = TimePoint::new(t0.value() + proc.value());
        let time = TimeInterval::new(t0, t1);

        self.ops.push(BerthOccupancyChangeOperation::Free(
            BerthOccupancyChangePayload::new(time, space),
        ));
        self.edits.push(AssignEdit::Clear(job));
        self.overlay.free(self.ctx.berth, time, space);

        Ok(RemoveOutcome::Removed)
    }

    pub fn move_into_slot(
        &mut self,
        job: RequestId,
        slot: BerthOccupancySlot<T>,
    ) -> Result<(), CS::Violation> {
        let req = self.ctx.model.request(job);
        let len = req.length();
        let proc = req.processing_duration();

        let s0 = slot.space.start();
        let s1 = SpacePosition::new(s0.value() + len.value());
        if s1 > slot.space.end() {
            return Err(self.ctx.cons.map_slot_stale());
        }
        let space = SpaceInterval::new(s0, s1);

        let t0 = slot.start_time;
        let t1 = TimePoint::new(t0.value() + proc.value());
        let time = TimeInterval::new(t0, t1);

        self.ctx.cons.allowed_job_edit(job, &time, &space)?;

        if !AvailabilityView::new(self.ctx.berth, time).is_free_under(space, Some(&self.overlay)) {
            return Err(self.ctx.cons.map_overlap());
        }

        if self.ctx.model.assignment(job).is_some()
            && !self
                .edits
                .iter()
                .any(|e| matches!(e, AssignEdit::Clear(id) if *id == job))
        {
            let _ = self.remove(job)?;
        }

        self.ops.push(BerthOccupancyChangeOperation::Occupy(
            BerthOccupancyChangePayload::new(time, space),
        ));
        self.edits
            .push(AssignEdit::Set(RequestEdit::new(job, time, space)));
        self.overlay.occupy(self.ctx.berth, time, space);
        Ok(())
    }

    #[inline]
    fn rect_key(t: &TimeInterval<T>, s: &SpaceInterval) -> (T, T, usize, usize) {
        (
            t.start().value(),
            t.end().value(),
            s.start().value(),
            s.end().value(),
        )
    }

    pub fn finish(self) -> Result<Plan<T>, CS::Violation> {
        let mut tmp = BerthOccupancyOverlay::new();
        for op in &self.ops {
            let p = op.payload();
            match op {
                BerthOccupancyChangeOperation::Free(_) => {
                    tmp.free(self.ctx.berth, *p.time(), *p.space());
                }
                BerthOccupancyChangeOperation::Occupy(_) => {
                    if !AvailabilityView::new(self.ctx.berth, *p.time())
                        .is_free_under(*p.space(), Some(&tmp))
                    {
                        return Err(self.ctx.cons.map_overlap());
                    }
                    tmp.occupy(self.ctx.berth, *p.time(), *p.space());
                }
            }
        }

        let mut occupy_rects = HashSet::new();
        let mut free_rects = HashSet::new();
        for op in &self.ops {
            let p = op.payload();
            let k = Self::rect_key(p.time(), p.space());
            match op {
                BerthOccupancyChangeOperation::Occupy(_) => {
                    occupy_rects.insert(k);
                }
                BerthOccupancyChangeOperation::Free(_) => {
                    free_rects.insert(k);
                }
            }
        }

        let mut set_rects = HashSet::new();
        let mut clear_rects = HashSet::new();

        for edit in &self.edits {
            match edit {
                AssignEdit::Set(re) => {
                    let tw = self.ctx.cons.job_time_window(re.id());
                    let sw = self.ctx.cons.job_space_window(re.id());
                    if re.time().start() < tw.start()
                        || re.time().end() > tw.end()
                        || re.space().start() < sw.start()
                        || re.space().end() > sw.end()
                    {
                        return Err(self.ctx.cons.map_slot_stale());
                    }
                    self.ctx
                        .cons
                        .allowed_job_edit(re.id(), &re.time(), &re.space())?;

                    let k = Self::rect_key(&re.time(), &re.space());
                    if !occupy_rects.contains(&k) {
                        return Err(self.ctx.cons.map_slot_stale());
                    }
                    set_rects.insert(k);
                }
                AssignEdit::Clear(id) => {
                    self.ctx.cons.allowed_remove(*id)?;

                    let Some(asg) = self.ctx.model.assignment(*id) else {
                        return Err(self.ctx.cons.map_slot_stale());
                    };
                    let req = self.ctx.model.request(*id);
                    let len = req.length();
                    let proc = req.processing_duration();

                    let s0 = asg.start_position();
                    let s1 = SpacePosition::new(s0.value() + len.value());
                    let space = SpaceInterval::new(s0, s1);

                    let t0 = asg.start_time();
                    let t1 = TimePoint::new(t0.value() + proc.value());
                    let time = TimeInterval::new(t0, t1);

                    let k = Self::rect_key(&time, &space);
                    if !free_rects.contains(&k) {
                        return Err(self.ctx.cons.map_slot_stale());
                    }
                    clear_rects.insert(k);
                }
            }
        }

        for k in &occupy_rects {
            if !set_rects.contains(k) {
                return Err(self.ctx.cons.map_slot_stale());
            }
        }
        for k in &free_rects {
            if !clear_rects.contains(k) {
                return Err(self.ctx.cons.map_slot_stale());
            }
        }

        Ok(Plan::new(self.ops, self.edits, self.ctx.stamp))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{constraints::ConstraintsView, quay::BTreeMapQuay};
    use dock_alloc_core::domain::{
        Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
    };
    use dock_alloc_model::{Assignment, Request, RequestId};
    use std::collections::{HashMap, HashSet};

    struct MockModel {
        requests: Vec<Request<i64, i64>>,
        idx: HashMap<RequestId, usize>,
        assigns: HashMap<RequestId, Assignment<i64, i64>>,
        locked: HashSet<RequestId>,
    }

    impl MockModel {
        fn new(requests: Vec<Request<i64, i64>>) -> Self {
            let idx = requests
                .iter()
                .enumerate()
                .map(|(i, r)| (r.id(), i))
                .collect();
            Self {
                requests,
                idx,
                assigns: HashMap::new(),
                locked: HashSet::new(),
            }
        }
        fn set_assignment(&mut self, a: Assignment<i64, i64>) {
            self.assigns.insert(a.request().id(), a);
        }
        fn set_locked(&mut self, id: RequestId, v: bool) {
            if v {
                self.locked.insert(id);
            } else {
                self.locked.remove(&id);
            }
        }
    }

    impl ModelAccess<i64, i64> for MockModel {
        fn request(&self, id: RequestId) -> &Request<i64, i64> {
            let i = *self.idx.get(&id).expect("unknown RequestId");
            &self.requests[i]
        }
        fn requests(&self) -> &[Request<i64, i64>] {
            &self.requests
        }
        fn assignment(&self, id: RequestId) -> Option<&Assignment<i64, i64>> {
            self.assigns.get(&id)
        }
        fn is_locked(&self, id: RequestId) -> bool {
            self.locked.contains(&id)
        }
    }

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
    }

    fn mk_ctx<'a>(
        berth: &'a BerthOccupancy<i64, BTreeMapQuay>,
        model: &'a MockModel,
    ) -> ProposeCtx<'a, i64, i64, BTreeMapQuay, MockModel, ConstraintsView<'a, i64, i64, MockModel>>
    {
        ProposeCtx::new(berth, model, ConstraintsView::new(model))
    }

    #[test]
    fn test_footprint_from_operations_hull() {
        let t_a = TimeInterval::new(TimePoint::new(0), TimePoint::new(5));
        let s_a = SpaceInterval::new(SpacePosition::new(1), SpacePosition::new(4));
        let t_b = TimeInterval::new(TimePoint::new(3), TimePoint::new(10));
        let s_b = SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(9));

        let ops = vec![
            BerthOccupancyChangeOperation::Free(BerthOccupancyChangePayload::new(t_a, s_a)),
            BerthOccupancyChangeOperation::Occupy(BerthOccupancyChangePayload::new(t_b, s_b)),
        ];
        let fp = Footprint::from(ops.as_slice());
        assert_eq!(fp.time().start().value(), 0);
        assert_eq!(fp.time().end().value(), 10);
        assert_eq!(fp.space().start().value(), 1);
        assert_eq!(fp.space().end().value(), 9);
    }

    #[test]
    fn test_explorer_slots_default_yields_slots() {
        let quay_length = SpaceLength::new(20);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        let req = mk_req(1, 4, 3, 0, 10, 0, 20);
        let model = MockModel::new(vec![req]);

        let ctx = mk_ctx(&berth, &model);
        let overlay = BerthOccupancyOverlay::new();
        let explorer = Explorer::new(&ctx, &overlay);

        let slots: Vec<_> = explorer.iter_slots(RequestId::new(1)).take(3).collect();
        assert!(
            !slots.is_empty(),
            "expected at least one slot on empty berth"
        );
        for slot in &slots {
            assert!(slot.space.start() >= req.feasible_space_window().start());
            assert!(slot.space.end() <= req.feasible_space_window().end());
        }
    }

    #[test]
    fn test_planbuilder_remove_and_move_flow() {
        let quay_length = SpaceLength::new(20);
        let mut berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        berth.occupy(
            TimeInterval::new(TimePoint::new(10), TimePoint::new(15)),
            SpaceInterval::new(SpacePosition::new(15), SpacePosition::new(20)),
        );

        let req = mk_req(1, 4, 3, 0, 20, 0, 20);
        let mut model = MockModel::new(vec![req]);

        let asg = Assignment::new(req, SpacePosition::new(2), TimePoint::new(1));
        model.set_assignment(asg);

        let ctx = mk_ctx(&berth, &model);
        let mut builder = PlanBuilder::new(&ctx);

        assert!(matches!(
            builder.remove(RequestId::new(1)),
            Ok(RemoveOutcome::Removed)
        ));
        assert_eq!(builder.ops.len(), 1);
        assert_eq!(builder.edits.len(), 1);

        let slot = builder
            .explorer()
            .iter_slots(RequestId::new(1))
            .next()
            .expect("slot");
        builder
            .move_into_slot(RequestId::new(1), slot)
            .expect("move_into_slot");
        assert_eq!(builder.ops.len(), 2);
        assert_eq!(builder.edits.len(), 2);

        let plan = builder.finish().expect("finish must validate");
        assert!(!plan.is_empty());
        assert_eq!(plan.operations().len(), 2);
        assert_eq!(plan.edits().len(), 2);
    }

    #[test]
    fn test_planbuilder_remove_errors_empty_and_locked_policy() {
        let quay_length = SpaceLength::new(10);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        let req = mk_req(1, 2, 1, 0, 10, 0, 10);
        let mut model = MockModel::new(vec![req]);
        let ctx = mk_ctx(&berth, &model);
        let mut builder = PlanBuilder::new(&ctx);
        let outcome = builder.remove(RequestId::new(1));
        assert!(matches!(outcome, Ok(RemoveOutcome::Noop)));
        let asg = Assignment::new(req, SpacePosition::new(0), TimePoint::new(0));
        model.set_assignment(asg);
        model.set_locked(RequestId::new(1), true);
        let ctx2 = mk_ctx(&berth, &model);
        let mut builder2 = PlanBuilder::new(&ctx2);
        assert!(builder2.remove(RequestId::new(1)).is_err());
    }

    #[test]
    fn test_move_into_slot_infeasible_space_and_time() {
        let quay_length = SpaceLength::new(12);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        let req = mk_req(1, 4, 3, 0, 10, 0, 12);
        let model = MockModel::new(vec![req]);
        let ctx = mk_ctx(&berth, &model);
        let mut builder = PlanBuilder::new(&ctx);
        let bad_space = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(3));
        let bad_slot = BerthOccupancySlot {
            start_time: TimePoint::new(0),
            space: bad_space,
        };
        assert!(builder.move_into_slot(RequestId::new(1), bad_slot).is_err());
        let wide_space = SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10));
        let bad_time_slot = BerthOccupancySlot {
            start_time: TimePoint::new(9),
            space: wide_space,
        };
        assert!(
            builder
                .move_into_slot(RequestId::new(1), bad_time_slot)
                .is_err()
        );
    }

    #[test]
    fn test_explorer_is_free_rect_respects_overlay() {
        let quay_length = SpaceLength::new(10);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        let req = mk_req(1, 2, 2, 0, 10, 0, 10);
        let model = MockModel::new(vec![req]);
        let ctx = mk_ctx(&berth, &model);

        let mut overlay = BerthOccupancyOverlay::new();
        overlay.add_occupy(
            TimePoint::new(0),
            SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(5)),
        );

        let explorer = Explorer::new(&ctx, &overlay);
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
    fn test_remove_idempotent_twice() {
        let quay_length = SpaceLength::new(10);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        let req = mk_req(1, 2, 1, 0, 10, 0, 10);
        let mut model = MockModel::new(vec![req]);

        let asg = Assignment::new(req, SpacePosition::new(3), TimePoint::new(2));
        model.set_assignment(asg);

        let ctx = mk_ctx(&berth, &model);
        let mut builder = PlanBuilder::new(&ctx);

        assert!(matches!(
            builder.remove(RequestId::new(1)),
            Ok(RemoveOutcome::Removed)
        ));
        assert!(matches!(
            builder.remove(RequestId::new(1)),
            Ok(RemoveOutcome::Noop)
        ));
    }

    #[test]
    fn test_finish_can_be_empty() {
        let quay_length = SpaceLength::new(10);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        let req = mk_req(1, 2, 1, 0, 10, 0, 10);
        let model = MockModel::new(vec![req]);

        let ctx = mk_ctx(&berth, &model);
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
        let model = MockModel::new(vec![req]);

        let ctx = mk_ctx(&berth, &model);
        let mut builder = PlanBuilder::new(&ctx);

        let space = SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(6));
        let time = TimeInterval::new(TimePoint::new(1), TimePoint::new(4));
        builder.ops.push(BerthOccupancyChangeOperation::Occupy(
            BerthOccupancyChangePayload::new(time, space),
        ));

        assert!(builder.finish().is_err());
    }
}
