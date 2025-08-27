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
    constraints::ConstraintsView,
    domain::Version,
    lens::{AvailabilityView, BerthOccupancyOverlay, FreePlacementIter},
    model_access::ModelAccess,
    occ::BerthOccupancy,
    quay::Quay,
};
use dock_alloc_core::domain::SpacePosition;
use dock_alloc_core::domain::{SpaceInterval, TimeInterval, TimePoint};
use dock_alloc_model::RequestId;
use num_traits::{PrimInt, Signed};
use std::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OperationData<T: PrimInt + Signed> {
    time: TimeInterval<T>,
    space: SpaceInterval,
}

impl<T: PrimInt + Signed> OperationData<T> {
    pub fn new(time: TimeInterval<T>, space: SpaceInterval) -> Self {
        Self { time, space }
    }

    pub fn time(&self) -> TimeInterval<T> {
        self.time
    }

    pub fn space(&self) -> SpaceInterval {
        self.space
    }
}

impl<T: PrimInt + Signed + Display> Display for OperationData<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "OperationData(time: {}, space: {})",
            self.time, self.space
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Operation<T: PrimInt + Signed> {
    Free(OperationData<T>),
    Occupy(OperationData<T>),
}

impl<T: PrimInt + Signed> Operation<T> {
    pub fn data(&self) -> &OperationData<T> {
        match self {
            Operation::Free(d) => d,
            Operation::Occupy(d) => d,
        }
    }
}

impl<T: PrimInt + Signed + Display> Display for Operation<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operation::Free(d) => write!(f, "Free({})", d),
            Operation::Occupy(d) => write!(f, "Occupy({})", d),
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
fn time_hull<T: PrimInt + Signed>(a: TimeInterval<T>, b: TimeInterval<T>) -> TimeInterval<T> {
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
fn space_hull(a: SpaceInterval, b: SpaceInterval) -> SpaceInterval {
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

impl<T: PrimInt + Signed> From<&[Operation<T>]> for Footprint<T> {
    fn from(ops: &[Operation<T>]) -> Self {
        ops.iter()
            .map(|op| op.data())
            .map(|d| (d.time(), d.space()))
            .reduce(|(t1, s1), (t2, s2)| (time_hull(t1, t2), space_hull(s1, s2)))
            .map(|(time, space)| Footprint::new(time, space))
            .unwrap_or_default()
    }
}

impl<T: PrimInt + Signed> From<&OperationData<T>> for Footprint<T> {
    #[inline]
    fn from(op: &OperationData<T>) -> Self {
        Footprint::new(op.time(), op.space())
    }
}

impl<T: PrimInt + Signed> From<&Operation<T>> for Footprint<T> {
    #[inline]
    fn from(op: &Operation<T>) -> Self {
        match op {
            Operation::Free(d) | Operation::Occupy(d) => Footprint::from(d),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Plan<T: PrimInt + Signed> {
    operations: Vec<Operation<T>>,
    edits: Vec<AssignEdit<T>>,
    version: Version,
    footprint: Footprint<T>,
}

impl<T: PrimInt + Signed> Plan<T> {
    pub fn new(operations: Vec<Operation<T>>, edits: Vec<AssignEdit<T>>, version: Version) -> Self {
        let footprint = Footprint::from(operations.as_slice());
        Self {
            operations,
            edits,
            version,
            footprint,
        }
    }

    #[inline]
    pub fn operations(&self) -> &[Operation<T>] {
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
pub struct SlotToken<T: PrimInt + Signed> {
    start_time: TimePoint<T>,
    space: SpaceInterval,
    epoch: u64,
}

impl<T: PrimInt + Signed> SlotToken<T> {
    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }

    #[inline]
    pub fn space(&self) -> SpaceInterval {
        self.space
    }

    #[inline]
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
}

impl<T: PrimInt + Signed + Display> Display for SlotToken<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SlotToken(start_time: {}, space: {}, epoch: {})",
            self.start_time, self.space, self.epoch
        )
    }
}

pub struct ProposeCtx<'a, T, C, Q, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
{
    berth: &'a BerthOccupancy<T, Q>,
    model: &'a M,
    cons: ConstraintsView<'a, T, C, M>,
    stamp: Version,
}

impl<'a, T, C, Q, M> ProposeCtx<'a, T, C, Q, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
{
    #[inline]
    pub fn job_time_window(&self, id: RequestId) -> TimeInterval<T> {
        self.cons.job_time_window(id)
    }

    #[inline]
    pub fn job_space_window(&self, id: RequestId) -> SpaceInterval {
        self.cons.job_space_window(id)
    }
}

pub struct Explorer<'a, T, C, Q, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
{
    ctx: &'a ProposeCtx<'a, T, C, Q, M>,
    overlay: &'a BerthOccupancyOverlay<T>,
    epoch: u64,
}

impl<'a, T, C, Q, M> Explorer<'a, T, C, Q, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    M: ModelAccess<T, C>,
    Q: Quay,
    BerthOccupancy<T, Q>: crate::lens::TimelineSlices<T, Q>,
{
    #[inline]
    pub fn new(
        ctx: &'a ProposeCtx<'a, T, C, Q, M>,
        overlay: &'a BerthOccupancyOverlay<T>,
        epoch: u64,
    ) -> Self {
        Self {
            ctx,
            overlay,
            epoch,
        }
    }

    pub fn iter_slots(&'a self, job: RequestId) -> impl Iterator<Item = SlotToken<T>> + 'a {
        let req = self.ctx.model.request(job);
        let len = req.length();
        let proc = req.processing_duration();
        let tw = req.feasible_time_window();
        let sw = req.feasible_space_window();

        FreePlacementIter::new(self.ctx.berth, tw, proc, len, sw, Some(self.overlay)).map(
            move |(t0, space)| SlotToken {
                start_time: t0,
                space,
                epoch: self.epoch,
            },
        )
    }

    #[inline]
    pub fn is_free(&self, time: TimeInterval<T>, space: SpaceInterval) -> bool {
        AvailabilityView::new(self.ctx.berth, time).is_free_under(space, Some(self.overlay))
    }
}

pub struct PlanBuilder<'a, T, C, Q, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
{
    ctx: &'a ProposeCtx<'a, T, C, Q, M>,
    overlay: BerthOccupancyOverlay<T>,
    epoch: u64,
    ops: Vec<Operation<T>>,
    edits: Vec<AssignEdit<T>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RemoveError {
    Locked,
}

impl Display for RemoveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RemoveError::Locked => write!(f, "RemoveError: Locked"),
        }
    }
}

impl std::error::Error for RemoveError {}

impl From<RemoveError> for TokenMoveError {
    fn from(e: RemoveError) -> Self {
        match e {
            RemoveError::Locked => TokenMoveError::Locked,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RemoveOutcome {
    Noop,
    Removed,
}

impl Display for RemoveOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RemoveOutcome::Noop => write!(f, "RemoveOutcome: Noop"),
            RemoveOutcome::Removed => write!(f, "RemoveOutcome: Removed"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenMoveError {
    StaleToken,
    Locked,
    Forbidden,
    InvalidToken,
}

impl Display for TokenMoveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StaleToken => write!(f, "slot token is stale"),
            Self::Locked => write!(f, "request is locked"),
            Self::Forbidden => write!(f, "edit forbidden by constraints"),
            Self::InvalidToken => write!(f, "invalid slot token"),
        }
    }
}

impl std::error::Error for TokenMoveError {}

impl<'a, T, C, Q, M> PlanBuilder<'a, T, C, Q, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
    BerthOccupancy<T, Q>: crate::lens::TimelineSlices<T, Q>,
{
    #[inline]
    pub fn new(ctx: &'a ProposeCtx<'a, T, C, Q, M>) -> Self {
        Self {
            ctx,
            overlay: BerthOccupancyOverlay::new(),
            epoch: 0,
            ops: Vec::new(),
            edits: Vec::new(),
        }
    }

    #[inline]
    pub fn explorer(&'a self) -> Explorer<'a, T, C, Q, M> {
        Explorer::new(self.ctx, &self.overlay, self.epoch)
    }

    pub fn remove(&mut self, job: RequestId) -> Result<RemoveOutcome, RemoveError> {
        if self.ctx.model.is_locked(job) {
            return Err(RemoveError::Locked);
        }

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

        self.ops
            .push(Operation::Free(OperationData::new(time, space)));
        self.edits.push(AssignEdit::Clear(job));
        self.overlay.free(self.ctx.berth, time, space);
        self.bump_epoch();
        Ok(RemoveOutcome::Removed)
    }

    pub fn move_into_token(
        &mut self,
        job: RequestId,
        token: SlotToken<T>,
    ) -> Result<(), TokenMoveError> {
        if token.epoch != self.epoch {
            return Err(TokenMoveError::StaleToken);
        }

        let req = self.ctx.model.request(job);
        let len = req.length();
        let proc = req.processing_duration();

        let s0 = token.space.start();
        let s1 = SpacePosition::new(s0.value() + len.value());
        if s1 > token.space.end() {
            return Err(TokenMoveError::InvalidToken);
        }
        let space = SpaceInterval::new(s0, s1);

        let t0 = token.start_time;
        let t1 = TimePoint::new(t0.value() + proc.value());
        let time = TimeInterval::new(t0, t1);

        let tw = self.ctx.job_time_window(job);
        let sw = self.ctx.job_space_window(job);

        if time.start() < tw.start()
            || time.end() > tw.end()
            || space.start() < sw.start()
            || space.end() > sw.end()
        {
            return Err(TokenMoveError::InvalidToken);
        }

        if !self.ctx.cons.allowed_job_edit(job, &time, &space) {
            return Err(if self.ctx.model.is_locked(job) {
                TokenMoveError::Locked
            } else {
                TokenMoveError::Forbidden
            });
        }

        if self.ctx.model.assignment(job).is_some()
            && !self
                .edits
                .iter()
                .any(|e| matches!(e, AssignEdit::Clear(id) if *id == job))
        {
            let _ = self.remove(job)?;
        }

        self.ops
            .push(Operation::Occupy(OperationData::new(time, space)));
        self.edits
            .push(AssignEdit::Set(RequestEdit::new(job, time, space)));

        self.overlay.occupy(self.ctx.berth, time, space);
        self.bump_epoch();
        Ok(())
    }

    #[inline]
    pub fn finish(self) -> Plan<T> {
        Plan::new(self.ops, self.edits, self.ctx.stamp)
    }

    #[inline]
    fn bump_epoch(&mut self) {
        self.epoch = self.epoch.wrapping_add(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraints::ConstraintsView;
    use crate::occ::BerthOccupancy;
    use crate::quay::BTreeMapQuay;
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
    ) -> ProposeCtx<'a, i64, i64, BTreeMapQuay, MockModel> {
        ProposeCtx {
            berth,
            model,
            cons: ConstraintsView::new(model),
            stamp: Version::default(),
        }
    }

    #[test]
    fn test_footprint_from_operations_hull() {
        let t_a = TimeInterval::new(TimePoint::new(0), TimePoint::new(5));
        let s_a = SpaceInterval::new(SpacePosition::new(1), SpacePosition::new(4));
        let t_b = TimeInterval::new(TimePoint::new(3), TimePoint::new(10));
        let s_b = SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(9));

        let ops = vec![
            Operation::Free(OperationData::new(t_a, s_a)),
            Operation::Occupy(OperationData::new(t_b, s_b)),
        ];
        let fp = Footprint::from(ops.as_slice());
        assert_eq!(fp.time().start().value(), 0);
        assert_eq!(fp.time().end().value(), 10);
        assert_eq!(fp.space().start().value(), 1);
        assert_eq!(fp.space().end().value(), 9);
    }

    #[test]
    fn test_explorer_slots_default_yields_tokens() {
        let quay_length = SpaceLength::new(20);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        let req = mk_req(1, 4, 3, 0, 10, 0, 20);
        let model = MockModel::new(vec![req]);

        let ctx = mk_ctx(&berth, &model);
        let overlay = BerthOccupancyOverlay::new();
        let explorer = Explorer::new(&ctx, &overlay, 0);

        let tokens: Vec<_> = explorer.iter_slots(RequestId::new(1)).take(3).collect();
        assert!(
            !tokens.is_empty(),
            "expected at least one token on empty berth"
        );
        for tok in &tokens {
            assert_eq!(tok.epoch, 0);
            // token space should be within feasible space window
            assert!(tok.space.start() >= req.feasible_space_window().start());
            assert!(tok.space.end() <= req.feasible_space_window().end());
        }
    }

    #[test]
    fn test_planbuilder_remove_and_move_flow_and_epoch_bump() {
        let quay_length = SpaceLength::new(20);
        let mut berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        // Occupy a slice boundary to ensure time slicing exists but keeps base free
        berth.occupy(
            TimeInterval::new(TimePoint::new(10), TimePoint::new(15)),
            SpaceInterval::new(SpacePosition::new(15), SpacePosition::new(20)),
        );

        let req = mk_req(1, 4, 3, 0, 20, 0, 20);
        let mut model = MockModel::new(vec![req]);

        // Preload an assignment so remove() has something to clear
        let asg = Assignment::new(req, SpacePosition::new(2), TimePoint::new(1));
        model.set_assignment(asg);

        let ctx = mk_ctx(&berth, &model);
        let mut builder = PlanBuilder::new(&ctx);

        // Remove should record ops and edits and bump epoch
        assert!(matches!(
            builder.remove(RequestId::new(1)),
            Ok(RemoveOutcome::Removed)
        ));
        assert_eq!(builder.ops.len(), 1);
        assert_eq!(builder.edits.len(), 1);

        // Now explore and place back into a token
        let tok = builder
            .explorer()
            .iter_slots(RequestId::new(1))
            .next()
            .expect("expected a token");
        let start_epoch = tok.epoch;
        assert_eq!(start_epoch, 1, "epoch should have bumped after remove");

        // Move into token should succeed and bump epoch again
        assert!(matches!(
            builder.move_into_token(RequestId::new(1), tok),
            Ok(())
        ));
        assert_eq!(builder.ops.len(), 2);
        assert_eq!(builder.edits.len(), 2);

        // New tokens should carry the bumped epoch
        let tok2 = builder
            .explorer()
            .iter_slots(RequestId::new(1))
            .next()
            .expect("expected a token");
        assert_eq!(tok2.epoch, start_epoch + 1);
    }

    #[test]
    fn test_planbuilder_remove_errors_empty_and_locked() {
        let quay_length = SpaceLength::new(10);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        let req = mk_req(1, 2, 1, 0, 10, 0, 10);
        let mut model = MockModel::new(vec![req]);

        // No assignment -> Empty
        let ctx = mk_ctx(&berth, &model);
        let mut builder = PlanBuilder::new(&ctx);
        let outcome = builder.remove(RequestId::new(1));
        assert!(matches!(outcome, Ok(RemoveOutcome::Noop)));

        // Set assignment and lock -> Locked
        let asg = Assignment::new(req, SpacePosition::new(0), TimePoint::new(0));
        model.set_assignment(asg);
        model.set_locked(RequestId::new(1), true);

        let ctx2 = mk_ctx(&berth, &model);
        let mut builder2 = PlanBuilder::new(&ctx2);
        let err2 = builder2.remove(RequestId::new(1)).unwrap_err();
        assert!(matches!(err2, RemoveError::Locked));
    }

    #[test]
    fn test_move_into_token_stale_and_infeasible() {
        let quay_length = SpaceLength::new(12);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        let req = mk_req(1, 4, 3, 0, 10, 0, 12);
        let model = MockModel::new(vec![req]);
        let ctx = mk_ctx(&berth, &model);
        let mut builder = PlanBuilder::new(&ctx);

        // Get a fresh token then artificially stale it by bumping epoch
        let tok = builder
            .explorer()
            .iter_slots(RequestId::new(1))
            .next()
            .expect("expected a token");
        builder.bump_epoch();
        let err = builder.move_into_token(RequestId::new(1), tok).unwrap_err();
        assert!(matches!(err, TokenMoveError::StaleToken));

        // Create an infeasible token (space too short for len=4)
        let bad_tok = SlotToken {
            start_time: TimePoint::new(0),
            space: SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(3)),
            epoch: builder.epoch,
        };
        let err2 = builder
            .move_into_token(RequestId::new(1), bad_tok)
            .unwrap_err();
        assert!(matches!(err2, TokenMoveError::InvalidToken));

        // Infeasible time window (outside req feasible window)
        let bad_tok_time = SlotToken {
            start_time: TimePoint::new(9), // t1 = 12 > tw.end(10)
            space: SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10)),
            epoch: builder.epoch,
        };
        let err3 = builder
            .move_into_token(RequestId::new(1), bad_tok_time)
            .unwrap_err();
        assert!(matches!(err3, TokenMoveError::InvalidToken));
    }

    #[test]
    fn test_explorer_is_free_rect_respects_overlay() {
        let quay_length = SpaceLength::new(10);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        let req = mk_req(1, 2, 2, 0, 10, 0, 10);
        let model = MockModel::new(vec![req]);
        let ctx = mk_ctx(&berth, &model);

        // Overlay occupies [2,5) at t=0
        let mut overlay = BerthOccupancyOverlay::new();
        overlay.add_occupy(
            TimePoint::new(0),
            SpaceInterval::new(SpacePosition::new(2), SpacePosition::new(5)),
        );

        let explorer = Explorer::new(&ctx, &overlay, 0);
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

        // Preload an assignment so the first remove() actually does work
        let asg = Assignment::new(req, SpacePosition::new(3), TimePoint::new(2));
        model.set_assignment(asg);

        let ctx = mk_ctx(&berth, &model);
        let mut builder = PlanBuilder::new(&ctx);

        let epoch0 = builder.epoch;
        assert!(matches!(
            builder.remove(RequestId::new(1)),
            Ok(RemoveOutcome::Removed)
        ));
        let epoch1 = builder.epoch;
        assert_eq!(epoch1, epoch0 + 1, "epoch should bump after a real removal");

        // Second remove() should be a no-op and must not change epoch
        assert!(matches!(
            builder.remove(RequestId::new(1)),
            Ok(RemoveOutcome::Noop)
        ));
        assert_eq!(builder.epoch, epoch1, "epoch must not change on Noop");
    }

    #[test]
    fn test_finish_can_be_empty() {
        let quay_length = SpaceLength::new(10);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        let req = mk_req(1, 2, 1, 0, 10, 0, 10);
        let model = MockModel::new(vec![req]);

        let ctx = mk_ctx(&berth, &model);
        let builder = PlanBuilder::new(&ctx);

        let plan = builder.finish();
        assert!(plan.is_empty(), "finish() should allow empty plans");
        assert_eq!(plan.operations().len(), 0);
        assert_eq!(plan.edits().len(), 0);
    }

    #[test]
    fn test_finish_nonempty_after_move_into_token() {
        let quay_length = SpaceLength::new(20);
        let berth = BerthOccupancy::<i64, BTreeMapQuay>::new(quay_length);
        // Length=4, proc=3, wide windows allow many tokens
        let req = mk_req(1, 4, 3, 0, 50, 0, 20);
        let model = MockModel::new(vec![req]);

        let ctx = mk_ctx(&berth, &model);
        let mut builder = PlanBuilder::new(&ctx);

        // Take a valid token and place the job
        let tok = builder
            .explorer()
            .iter_slots(RequestId::new(1))
            .next()
            .expect("expected at least one feasible token");
        builder
            .move_into_token(RequestId::new(1), tok)
            .expect("token move must succeed");

        // Finalize and verify the plan is non-empty with a single OCCUPY + SET edit
        let plan = builder.finish();
        assert!(
            !plan.is_empty(),
            "plan should not be empty after a token move"
        );
        assert_eq!(
            plan.operations().len(),
            1,
            "exactly one OCCUPY operation expected"
        );
        assert_eq!(plan.edits().len(), 1, "exactly one SET edit expected");
    }
}
