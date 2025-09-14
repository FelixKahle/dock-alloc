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
    dec::Assignment,
    err::{
        AssignmentBeforeArrivalTimeError, AssignmentExceedsQuayError,
        AssignmentOutsideSpaceWindowError, PreassignedOverlapError, ProblemBuildError,
    },
    id::{FixedRequestId, MovableRequestId},
    req::{AnyRequestRef, Fixed, Kind, Movable, Request},
};
use dock_alloc_core::{
    SolverVariable,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimeInterval, TimePoint},
};
use num_traits::{FromPrimitive, ToPrimitive};
use std::{collections::HashMap, fmt::Display};

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ProblemStats<T: SolverVariable> {
    /// Total quay length (space) as a typed length.
    quay_length: SpaceLength,
    /// Number of movable requests.
    movable_count: usize,
    /// 50th percentile of request lengths (typed).
    p50_request_length: SpaceLength,
    /// 90th percentile of request lengths (typed).
    p90_request_length: SpaceLength,
    /// 50th percentile of processing durations (typed).
    p50_processing_time: TimeDelta<T>,
    /// Proxy for instance horizon: latest known completion time among fixed and movable ETA+proc.
    latest_completion_time: TimePoint<T>,
    /// Crude congestion: total area demand / (quay_length * horizon),
    /// capped to [0, 2] for stability. Dimensionless.
    rho: f64,
}

impl<T: SolverVariable> ProblemStats<T> {
    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    #[inline]
    pub fn movable_count(&self) -> usize {
        self.movable_count
    }

    #[inline]
    pub fn p50_request_length(&self) -> SpaceLength {
        self.p50_request_length
    }

    #[inline]
    pub fn p90_request_length(&self) -> SpaceLength {
        self.p90_request_length
    }

    #[inline]
    pub fn p50_processing_time(&self) -> TimeDelta<T> {
        self.p50_processing_time
    }

    #[inline]
    pub fn latest_completion_time(&self) -> TimePoint<T> {
        self.latest_completion_time
    }

    #[inline]
    pub fn rho(&self) -> f64 {
        self.rho
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Problem<T = i64, C = i64>
where
    T: SolverVariable,
    C: SolverVariable,
{
    movables: Vec<Request<Movable, T, C>>,
    movable_index: HashMap<MovableRequestId, usize>,
    preassigned: Vec<Assignment<Fixed, T, C>>,
    preassigned_index: HashMap<FixedRequestId, usize>,
    quay_length: SpaceLength,
    stats: ProblemStats<T>,
}

impl<T: SolverVariable, C: SolverVariable> Problem<T, C> {
    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    #[inline]
    pub fn quay_interval(&self) -> SpaceInterval {
        SpaceInterval::new(
            SpacePosition::zero(),
            SpacePosition::zero() + self.quay_length,
        )
    }

    #[inline]
    pub fn total_requests(&self) -> usize {
        self.movables.len() + self.preassigned.len()
    }

    #[inline]
    pub fn movables(&self) -> &[Request<Movable, T, C>] {
        &self.movables
    }

    #[inline]
    pub fn preassigned(&self) -> &[Assignment<Fixed, T, C>] {
        &self.preassigned
    }

    #[inline]
    pub fn get_movable(&self, id: MovableRequestId) -> Option<&Request<Movable, T, C>> {
        let idx = self.movable_index.get(&id)?;
        self.movables.get(*idx)
    }

    #[inline]
    pub fn get_preassigned(&self, id: FixedRequestId) -> Option<&Assignment<Fixed, T, C>> {
        let idx = self.preassigned_index.get(&id)?;
        self.preassigned.get(*idx)
    }

    #[inline]
    pub fn iter_movable_requests(&self) -> impl Iterator<Item = &Request<Movable, T, C>> {
        self.movables.iter()
    }

    #[inline]
    pub fn iter_fixed_requests(&self) -> impl Iterator<Item = &Request<Fixed, T, C>> {
        self.preassigned.iter().map(|a| a.request())
    }

    #[inline]
    pub fn iter_any_requests(&self) -> impl Iterator<Item = AnyRequestRef<'_, T, C>> + '_ {
        self.iter_movable_requests()
            .map(AnyRequestRef::from)
            .chain(self.iter_fixed_requests().map(AnyRequestRef::from))
    }

    #[inline]
    pub fn iter_fixed_assignments(&self) -> impl Iterator<Item = &Assignment<Fixed, T, C>> {
        self.preassigned.iter()
    }

    #[inline]
    pub fn stats(&self) -> &ProblemStats<T> {
        &self.stats
    }

    #[inline]
    pub fn congestion_rho(&self) -> f64 {
        self.stats.rho()
    }

    #[inline]
    pub fn latest_completion_time(&self) -> TimePoint<T> {
        self.stats.latest_completion_time()
    }

    #[inline]
    pub fn p50_processing_time(&self) -> TimeDelta<T> {
        self.stats.p50_processing_time()
    }

    #[inline]
    pub fn p50_request_length(&self) -> SpaceLength {
        self.stats.p50_request_length()
    }

    #[inline]
    pub fn p90_request_length(&self) -> SpaceLength {
        self.stats.p90_request_length()
    }

    #[inline]
    pub fn movable_count(&self) -> usize {
        self.stats.movable_count()
    }
}

impl<T: SolverVariable, C: SolverVariable> Display for Problem<T, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Problem:")?;
        writeln!(f, "  Quay length: {}", self.quay_length)?;
        writeln!(f, "  Movable requests ({}):", self.movables.len())?;
        for r in &self.movables {
            writeln!(f, "    {}", r)?;
        }
        writeln!(f, "  Preassigned ({}):", self.preassigned.len())?;
        for a in &self.preassigned {
            writeln!(f, "    {}", a)?;
        }
        Ok(())
    }
}

pub struct ProblemBuilder<T = i64, C = i64>
where
    T: SolverVariable + ToPrimitive + FromPrimitive,
    C: SolverVariable,
{
    movables: HashMap<MovableRequestId, Request<Movable, T, C>>,
    preassigned: HashMap<FixedRequestId, Assignment<Fixed, T, C>>,
    quay_length: SpaceLength,
}

impl<T: SolverVariable + ToPrimitive + FromPrimitive, C: SolverVariable> ProblemBuilder<T, C> {
    #[inline]
    pub fn new(quay_length: SpaceLength) -> Self {
        Self {
            movables: HashMap::new(),
            preassigned: HashMap::new(),
            quay_length,
        }
    }

    #[inline]
    pub fn quay_length(&mut self, length: SpaceLength) -> &mut Self {
        self.quay_length = length;
        self
    }

    #[inline]
    pub fn add_movable_request(
        &mut self,
        request: Request<Movable, T, C>,
    ) -> Result<&mut Self, ProblemBuildError<T>> {
        let id = request.id();
        if self.movables.contains_key(&id.into()) || self.preassigned.contains_key(&id.into()) {
            return Err(ProblemBuildError::DuplicateRequestId(id));
        }
        self.movables.insert(id.into(), request);
        Ok(self)
    }

    #[inline]
    fn assignment_spans<K: Kind>(a: &Assignment<K, T, C>) -> (TimeInterval<T>, SpaceInterval) {
        let t0 = a.start_time();
        let t1 = t0 + a.request().processing_duration();
        let s0 = a.start_position();
        let s1 = SpacePosition::new(s0.value() + a.request().length().value());
        (TimeInterval::new(t0, t1), SpaceInterval::new(s0, s1))
    }

    pub fn add_preassigned(
        &mut self,
        fixed: Assignment<Fixed, T, C>,
    ) -> Result<&mut Self, ProblemBuildError<T>> {
        let a = &fixed;
        let r = a.request();
        let id = r.id();

        if self.movables.contains_key(&id.into()) || self.preassigned.contains_key(&id.into()) {
            return Err(ProblemBuildError::DuplicateRequestId(id));
        }

        if a.start_time() < r.arrival_time() {
            return Err(ProblemBuildError::AssignmentBeforeArrivalTime(
                AssignmentBeforeArrivalTimeError::new(id, r.arrival_time(), a.start_time()),
            ));
        }

        let (tspan, sspan) = Self::assignment_spans(a);

        let sw = r.feasible_space_window();
        if !sw.contains_interval(&sspan) {
            return Err(ProblemBuildError::AssignmentOutsideSpaceWindow(
                AssignmentOutsideSpaceWindowError::new(id, sw, sspan),
            ));
        }

        if sspan.end().value() > self.quay_length.value() {
            return Err(ProblemBuildError::AssignmentExceedsQuay(
                AssignmentExceedsQuayError::new(id, self.quay_length, sspan),
            ));
        }

        // Non-overlap among fixed assignments (space & time)
        for (&other_id, other_fixed) in &self.preassigned {
            let (ot, os) = Self::assignment_spans(other_fixed);
            if tspan.intersects(&ot) && sspan.intersects(&os) {
                return Err(ProblemBuildError::PreassignedOverlap(
                    PreassignedOverlapError::new(id.into(), other_id),
                ));
            }
        }

        self.preassigned.insert(id.into(), fixed);
        Ok(self)
    }

    #[inline]
    fn at_least_one_len(x: SpaceLength) -> SpaceLength {
        if x.value() == 0 {
            SpaceLength::new(1)
        } else {
            x
        }
    }

    #[must_use]
    #[inline]
    pub fn build(&self) -> Problem<T, C> {
        // Deterministic materialization from maps
        let (movables, movable_index) =
            materialize_sorted(&self.movables, |r: &Request<Movable, T, C>| r.id().into());
        let (preassigned, preassigned_index) =
            materialize_sorted(&self.preassigned, |a: &Assignment<Fixed, T, C>| {
                a.request().id().into()
            });

        // Percentiles (p50/p90 for lengths, p50 for proc times)
        let lengths: Vec<SpaceLength> = movables.iter().map(|r| r.length()).collect();
        let procs: Vec<TimeDelta<T>> = movables.iter().map(|r| r.processing_duration()).collect();

        let p50_len =
            Self::at_least_one_len(stats::percentile_space_length(lengths.as_slice(), 0.50));
        let p90_len =
            Self::at_least_one_len(stats::percentile_space_length(lengths.as_slice(), 0.90));
        let p50_proc = stats::percentile_time_delta::<T>(procs.as_slice(), 0.50);

        let mut latest_end = TimePoint::new(T::zero());
        for a in &preassigned {
            let end = a.start_time() + a.request().processing_duration();
            if end > latest_end {
                latest_end = end;
            }
        }
        for r in &movables {
            let end = r.arrival_time() + r.processing_duration();
            if end > latest_end {
                latest_end = end;
            }
        }

        let quay_len_f = self.quay_length.value() as f64;
        let horizon_f = latest_end.value().to_f64().unwrap_or(0.0).max(1.0);
        let denom = (quay_len_f * horizon_f).max(1.0);

        let mut total_area_f = 0.0;
        total_area_f += movables.iter().fold(0.0, |acc, r| {
            acc + (r.length().value() as f64)
                * (r.processing_duration().value().to_f64().unwrap_or(0.0))
        });
        total_area_f += preassigned.iter().fold(0.0, |acc, a| {
            acc + (a.request().length().value() as f64)
                * (a.request()
                    .processing_duration()
                    .value()
                    .to_f64()
                    .unwrap_or(0.0))
        });

        let rho = (total_area_f / denom).clamp(0.0, 2.0);

        let stats = ProblemStats {
            quay_length: self.quay_length,
            movable_count: movables.len(),
            p50_request_length: p50_len,
            p90_request_length: p90_len,
            p50_processing_time: p50_proc,
            latest_completion_time: latest_end,
            rho,
        };

        Problem {
            movables,
            movable_index,
            preassigned,
            preassigned_index,
            quay_length: self.quay_length,
            stats,
        }
    }
}

#[inline]
fn materialize_sorted<K, V, FId>(map: &HashMap<K, V>, id_of: FId) -> (Vec<V>, HashMap<K, usize>)
where
    K: Copy + Eq + std::hash::Hash + Ord,
    V: Clone,
    FId: Fn(&V) -> K,
{
    let mut items: Vec<V> = map.values().cloned().collect();
    items.sort_by_key(|v| id_of(v));
    let mut index = HashMap::with_capacity(items.len());
    for (i, v) in items.iter().enumerate() {
        index.insert(id_of(v), i);
    }
    (items, index)
}

mod stats {
    use super::*;
    use statrs::statistics::{Data, OrderStatistics};

    #[inline]
    pub fn percentile_map<T, FMap, FBack, R>(data: &[T], p: f64, to_f64: FMap, from_f64: FBack) -> R
    where
        FMap: Fn(&T) -> f64,
        FBack: Fn(f64) -> R,
    {
        let p = p.clamp(0.0, 1.0);
        // Filter non-finite to be defensive; early-exit if empty.
        let vals: Vec<f64> = data.iter().map(&to_f64).filter(|x| x.is_finite()).collect();
        if vals.is_empty() {
            return from_f64(0.0);
        }
        let mut d = Data::new(vals);
        let q = d.quantile(p);
        from_f64(q)
    }

    #[inline]
    pub fn percentile_space_length(v: &[SpaceLength], p: f64) -> SpaceLength {
        percentile_map(
            v,
            p,
            |x| x.value() as f64,
            |q| SpaceLength::new(q.round().max(0.0) as usize),
        )
    }

    #[inline]
    pub fn percentile_time_delta<Tm: SolverVariable + ToPrimitive + FromPrimitive>(
        v: &[TimeDelta<Tm>],
        p: f64,
    ) -> TimeDelta<Tm> {
        percentile_map(
            v,
            p,
            |x| x.value().to_f64().unwrap_or(0.0),
            |q| TimeDelta::new(Tm::from_f64(q.round()).unwrap_or_else(Tm::zero)),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::RequestId;
    use dock_alloc_core::cost::Cost;

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
            SpaceInterval::new(SpacePosition::new(s0), SpacePosition::new(s1)),
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
            SpaceInterval::new(SpacePosition::new(s0), SpacePosition::new(s1)),
        )
        .expect("valid fixed request")
    }

    #[test]
    fn builder_duplicate_ids_rejected() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(20));
        let r1 = req_movable_ok(1, 4, 0, 3, 0, 10);
        let r2 = req_movable_ok(1, 5, 0, 3, 0, 10); // same id
        b.add_movable_request(r1).unwrap();
        assert!(matches!(
            b.add_movable_request(r2),
            Err(ProblemBuildError::DuplicateRequestId(_))
        ));
    }

    #[test]
    fn builder_preassigned_window_violations_rejected() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(20));
        let rf2 = req_fixed_ok(2, 6, 0, 2, 0, 10); // arrival = 0 (so time is fine)
        let a2 = Assignment::new(rf2, SpacePosition::new(7), TimePoint::new(1)); // [7,13) leaks past 10
        assert!(matches!(
            b.add_preassigned(a2),
            Err(ProblemBuildError::AssignmentOutsideSpaceWindow(_))
        ));
    }

    #[test]
    fn builder_preassigned_exceeds_quay_rejected() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(10));
        let rf = req_fixed_ok(1, 6, 0, 2, 0, 20); // window wide enough to include [6,12)
        let a = Assignment::new(rf, SpacePosition::new(6), TimePoint::new(1)); // [6,12) > quay 10
        assert!(matches!(
            b.add_preassigned(a),
            Err(ProblemBuildError::AssignmentExceedsQuay(_))
        ));
    }

    #[test]
    fn builder_preassigned_overlap_rejected() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(20));
        let r1 = req_fixed_ok(1, 4, 0, 5, 0, 20);
        let r2 = req_fixed_ok(2, 4, 0, 5, 0, 20);

        b.add_preassigned(Assignment::new(
            r1,
            SpacePosition::new(5),
            TimePoint::new(2),
        ))
        .unwrap(); // t[2,7), s[5,9)
        let a2 = Assignment::new(r2, SpacePosition::new(7), TimePoint::new(4)); // t[4,9), s[7,11) -> overlaps
        assert!(matches!(
            b.add_preassigned(a2),
            Err(ProblemBuildError::PreassignedOverlap(_))
        ));
    }

    #[test]
    fn builder_build_ok_when_valid() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(20));
        let r_m = req_movable_ok(1, 4, 0, 3, 0, 10);
        let r_f = req_fixed_ok(2, 4, 10, 3, 0, 10); // arrival = 10
        b.add_movable_request(r_m).unwrap();
        b.add_preassigned(Assignment::new(
            r_f,
            SpacePosition::new(6),
            TimePoint::new(10), // start at/after arrival
        ))
        .unwrap();
        let p = b.build();
        assert_eq!(p.total_requests(), 2);
        assert_eq!(p.movables().len(), 1);
        assert_eq!(p.preassigned().len(), 1);
    }

    #[test]
    fn builder_preassigned_start_before_arrival_rejected() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
        let r = req_fixed_ok(42, 10, 50, 5, 0, 100); // arrival_time = 50
        let a = Assignment::new(r, SpacePosition::new(0), TimePoint::new(49)); // starts before arrival
        assert!(matches!(
            b.add_preassigned(a),
            Err(ProblemBuildError::AssignmentBeforeArrivalTime(_))
        ));
    }
}
