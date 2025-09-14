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
    dec::{AnyAssignment, AnyAssignmentRef},
    err::{AssignmentBeforeArrivalTimeError, AssignmentOverlapError, SolutionValidationError},
    id::RequestId,
};
use dock_alloc_core::{
    SolverVariable,
    cost::Cost,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimeInterval},
};
use std::{collections::HashMap, fmt::Display};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SolutionStats<T = i64, C = i64>
where
    T: SolverVariable,
    C: SolverVariable,
{
    total_cost: Cost<C>,
    total_waiting_time: TimeDelta<T>,
    total_target_position_deviation: SpaceLength,
}

impl<T, C> Display for SolutionStats<T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Solution statistics:")?;
        writeln!(f, "  Total cost: {}", self.total_cost)?;
        writeln!(f, "  Total waiting time: {}", self.total_waiting_time)?;
        writeln!(
            f,
            "  Total target position deviation: {}",
            self.total_target_position_deviation
        )?;
        Ok(())
    }
}

impl<T: SolverVariable, C: SolverVariable> SolutionStats<T, C> {
    #[inline]
    fn new(
        total_cost: Cost<C>,
        total_waiting_time: TimeDelta<T>,
        total_target_position_deviation: SpaceLength,
    ) -> Self {
        Self {
            total_cost,
            total_waiting_time,
            total_target_position_deviation,
        }
    }
    #[inline]
    pub fn total_cost(&self) -> Cost<C> {
        self.total_cost
    }

    #[inline]
    pub fn total_waiting_time(&self) -> TimeDelta<T> {
        self.total_waiting_time
    }

    #[inline]
    pub fn total_target_position_deviation(&self) -> SpaceLength {
        self.total_target_position_deviation
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedSolution<T = i64, C = i64>
where
    T: SolverVariable,
    C: SolverVariable,
{
    decisions: HashMap<RequestId, AnyAssignment<T, C>>,
    stats: SolutionStats<T, C>,
}

impl<T, C> Display for OwnedSolution<T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Solution:")?;
        for a in self.decisions.values() {
            writeln!(f, "{}", a)?;
        }
        writeln!(f)?;
        write!(f, "{}", self.stats)
    }
}

impl<T, C> OwnedSolution<T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    #[inline]
    fn new(decisions: HashMap<RequestId, AnyAssignment<T, C>>, stats: SolutionStats<T, C>) -> Self {
        Self { decisions, stats }
    }

    #[inline]
    pub fn stats(&self) -> &SolutionStats<T, C> {
        &self.stats
    }

    #[inline]
    pub fn decisions(&self) -> &HashMap<RequestId, AnyAssignment<T, C>> {
        &self.decisions
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolutionRef<'a, T = i64, C = i64>
where
    T: SolverVariable,
    C: SolverVariable,
{
    decisions: HashMap<RequestId, AnyAssignmentRef<'a, T, C>>,
    stats: SolutionStats<T, C>,
}

impl<T, C> Display for SolutionRef<'_, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Solution:")?;
        for a in self.decisions.values() {
            writeln!(f, "{}", a)?;
        }
        writeln!(f)?;
        write!(f, "{}", self.stats)
    }
}

impl<'a, T, C> SolutionRef<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
{
    #[inline]
    pub fn new(
        assignments: HashMap<RequestId, AnyAssignmentRef<'a, T, C>>,
        stats: SolutionStats<T, C>,
    ) -> Self {
        Self {
            decisions: assignments,
            stats,
        }
    }

    #[inline]
    pub fn from_assignments(assignments: HashMap<RequestId, AnyAssignmentRef<'a, T, C>>) -> Self {
        let mut total_wait = TimeDelta::<T>::new(T::zero());
        let mut total_dev = SpaceLength::new(0);
        let mut total_cost = Cost::<C>::new(C::zero());

        for a in assignments.values() {
            let r = a.request();

            let wait = (a.start_time() - r.arrival_time())
                .clamp(TimeDelta::zero(), TimeDelta::new(T::max_value()));
            total_wait += wait;

            let dev = a.start_position() - r.target_position();
            total_dev += dev;

            let wait_cost = {
                let scalar: C = C::try_from(wait.value())
                    .ok()
                    .expect("wait does not fit in C");
                r.cost_per_delay() * scalar
            };
            let dev_cost = {
                let scalar: C = C::try_from(dev.value())
                    .ok()
                    .expect("dev does not fit in C");
                r.cost_per_position_deviation() * scalar
            };

            total_cost = total_cost + wait_cost + dev_cost;
        }

        Self::new(
            assignments,
            SolutionStats::new(total_cost, total_wait, total_dev),
        )
    }

    #[inline]
    pub fn stats(&self) -> &SolutionStats<T, C> {
        &self.stats
    }

    #[inline]
    pub fn decisions(&self) -> &HashMap<RequestId, AnyAssignmentRef<'_, T, C>> {
        &self.decisions
    }
}

impl<'a, T, C> SolutionRef<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    #[inline]
    pub fn to_owned(&self) -> OwnedSolution<T, C> {
        let owned_decisions = self
            .decisions
            .iter()
            .map(|(&id, a)| (id, a.to_owned()))
            .collect();

        OwnedSolution::new(owned_decisions, self.stats)
    }

    #[inline]
    pub fn into_owned(self) -> OwnedSolution<T, C> {
        let owned_decisions = self
            .decisions
            .into_iter()
            .map(|(id, a)| (id, a.into_owned()))
            .collect();

        OwnedSolution::new(owned_decisions, self.stats)
    }
}

impl<'a, T, C> From<&SolutionRef<'a, T, C>> for OwnedSolution<T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    #[inline]
    fn from(s: &SolutionRef<'a, T, C>) -> Self {
        s.to_owned()
    }
}

impl<'a, T, C> SolutionRef<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    pub fn validate(&self) -> Result<(), SolutionValidationError<T>> {
        #[derive(Clone)]
        struct Rect<Tm: SolverVariable> {
            id: RequestId,
            t: TimeInterval<Tm>,
            s: SpaceInterval,
        }

        let mut rects = Vec::with_capacity(self.decisions.len());

        for (&id, a) in &self.decisions {
            let r = a.request();

            let start = a.start_time();
            let arrival = r.arrival_time();
            if start < arrival {
                return Err(SolutionValidationError::AssignmentBeforeArrivalTime(
                    AssignmentBeforeArrivalTimeError::new(id, arrival, start),
                ));
            }

            let t0 = start;
            let t1 = t0 + r.processing_duration();
            let s0 = a.start_position();
            let s1 = SpacePosition::new(s0.value() + r.length().value());

            rects.push(Rect {
                id,
                t: TimeInterval::new(t0, t1),
                s: SpaceInterval::new(s0, s1),
            });
        }

        rects.sort_by_key(|r| r.t.start().value());
        let mut active: Vec<Rect<T>> = Vec::new();

        for cur in rects {
            active.retain(|x| x.t.end() > cur.t.start());
            for other in &active {
                if other.t.intersects(&cur.t) && other.s.intersects(&cur.s) {
                    return Err(SolutionValidationError::Overlap(
                        AssignmentOverlapError::new(
                            other.id, cur.id, other.t, cur.t, other.s, cur.s,
                        ),
                    ));
                }
            }

            active.push(cur);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        dec::Assignment,
        req::{Movable, Request},
    };
    use dock_alloc_core::{
        space::{SpaceInterval, SpacePosition},
        time::TimePoint,
    };

    type Tm = i64;
    type Cm = i64;

    fn req_movable_ok(
        id: u64,
        len: usize,
        arrival: i64,
        proc_t: i64,
        s_lo: usize,
        s_hi: usize,
        target: usize,
    ) -> Request<Movable, Tm, Cm> {
        Request::<Movable, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimePoint::new(arrival),
            TimeDelta::new(proc_t),
            SpacePosition::new(target),
            Cost::new(1),
            Cost::new(1),
            SpaceInterval::new(SpacePosition::new(s_lo), SpacePosition::new(s_hi)),
        )
        .expect("valid req")
    }

    fn any_ref(a: &Assignment<Movable, Tm, Cm>) -> AnyAssignmentRef<'_, Tm, Cm> {
        AnyAssignmentRef::from(a)
    }

    #[test]
    fn cost_helpers_behave_like_solution_path() {
        // Set cost-per-delay=2, cost-per-dev=3 to see accumulation
        let r = Request::<Movable, Tm, Cm>::new(
            RequestId::new(7),
            SpaceLength::new(4),
            TimePoint::new(5),
            TimeDelta::new(3),
            SpacePosition::new(10),
            Cost::new(2), // per time unit
            Cost::new(3), // per space unit
            SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
        )
        .unwrap();

        // start at t=9 (wait=4), position=13 (dev=3)
        let a = Assignment::new(r, SpacePosition::new(13), TimePoint::new(9));
        let ae: AnyAssignmentRef<'_, Tm, Cm> = AnyAssignmentRef::from(&a);

        // replicate Solution math
        let wait = (ae.start_time() - ae.request().arrival_time())
            .clamp(TimeDelta::zero(), TimeDelta::new(Tm::max_value()));
        let dev = ae.start_position() - ae.request().target_position();

        assert_eq!(wait, TimeDelta::new(4));
        assert_eq!(dev, SpaceLength::new(3));

        let mut map = HashMap::new();
        map.insert(ae.id(), ae.clone());
        let sol = SolutionRef::from_assignments(map);

        // expected: cost = 2*4 + 3*3 = 8 + 9 = 17
        assert_eq!(sol.stats().total_cost(), Cost::new(17));
    }

    #[test]
    fn validate_ok_no_overlap_same_band_separated_in_time() {
        // Same space band, disjoint in time.
        let r1 = req_movable_ok(1, 4, 0, 5, 0, 100, 10);
        let r2 = req_movable_ok(2, 5, 0, 5, 0, 100, 30);

        let a1 = Assignment::new(r1, SpacePosition::new(10), TimePoint::new(0));
        // a1 time = [0,5)
        let a2 = Assignment::new(r2, SpacePosition::new(10), TimePoint::new(5));
        // a2 time = [5,10) — touches a1 at 5, half-open => OK

        let mut m = HashMap::new();
        m.insert(a1.id(), any_ref(&a1));
        m.insert(a2.id(), any_ref(&a2));

        let sol = SolutionRef::from_assignments(m);
        assert!(sol.validate().is_ok());
    }

    #[test]
    fn validate_ok_time_overlap_but_disjoint_space() {
        // Overlap in time windows but not in space => OK.
        let r1 = req_movable_ok(1, 4, 0, 5, 0, 100, 10);
        let r2 = req_movable_ok(2, 6, 0, 5, 0, 100, 40);

        let a1 = Assignment::new(r1, SpacePosition::new(10), TimePoint::new(2)); // [2,7), space [10,14)
        let a2 = Assignment::new(r2, SpacePosition::new(50), TimePoint::new(3)); // [3,8), space [50,56)

        let mut m = HashMap::new();
        m.insert(a1.id(), any_ref(&a1));
        m.insert(a2.id(), any_ref(&a2));

        let sol = SolutionRef::from_assignments(m);
        assert!(sol.validate().is_ok());
    }

    #[test]
    fn validate_ok_space_touching_edges_same_time() {
        // Same start time; space intervals touch at an edge => OK (half-open).
        let r1 = req_movable_ok(1, 4, 0, 3, 0, 100, 10);
        let r2 = req_movable_ok(2, 5, 0, 3, 0, 100, 14);

        let a1 = Assignment::new(r1, SpacePosition::new(10), TimePoint::new(5)); // space [10,14)
        let a2 = Assignment::new(r2, SpacePosition::new(14), TimePoint::new(5)); // space [14,19)

        let mut m = HashMap::new();
        m.insert(a1.id(), any_ref(&a1));
        m.insert(a2.id(), any_ref(&a2));

        let sol = SolutionRef::from_assignments(m);
        assert!(sol.validate().is_ok());
    }

    #[test]
    fn validate_err_start_before_arrival() {
        let r = req_movable_ok(7, 4, 10, 3, 0, 100, 10);
        // start at t=9 but arrival is 10 => should fail
        let a = Assignment::new(r, SpacePosition::new(10), TimePoint::new(9));

        let mut m = HashMap::new();
        m.insert(a.id(), any_ref(&a));
        let sol = SolutionRef::from_assignments(m);

        let err = sol.validate().unwrap_err();
        assert!(matches!(
            err,
            SolutionValidationError::AssignmentBeforeArrivalTime(_)
        ));
    }

    #[test]
    fn validate_err_true_spacetime_overlap() {
        // Overlap in time AND space => error.
        let r1 = req_movable_ok(1, 4, 0, 5, 0, 100, 10);
        let r2 = req_movable_ok(2, 5, 0, 5, 0, 100, 12);

        let a1 = Assignment::new(r1, SpacePosition::new(10), TimePoint::new(1)); // time [1,6), space [10,14)
        let a2 = Assignment::new(r2, SpacePosition::new(12), TimePoint::new(3)); // time [3,8), space [12,17) => overlaps both

        let mut m = HashMap::new();
        m.insert(a1.id(), any_ref(&a1));
        m.insert(a2.id(), any_ref(&a2));

        let sol = SolutionRef::from_assignments(m);

        let err = sol.validate().unwrap_err();
        assert!(matches!(err, SolutionValidationError::Overlap(_)));
    }

    #[test]
    fn validate_ok_time_touching_edges_same_space() {
        // Space overlaps, but time is just edge-touching => OK.
        let r1 = req_movable_ok(1, 4, 0, 5, 0, 100, 10);
        let r2 = req_movable_ok(2, 4, 0, 5, 0, 100, 10);

        let a1 = Assignment::new(r1, SpacePosition::new(20), TimePoint::new(0)); // [0,5)
        let a2 = Assignment::new(r2, SpacePosition::new(20), TimePoint::new(5)); // [5,10)

        let mut m = HashMap::new();
        m.insert(a1.id(), any_ref(&a1));
        m.insert(a2.id(), any_ref(&a2));

        let sol = SolutionRef::from_assignments(m);
        assert!(sol.validate().is_ok());
    }

    #[test]
    fn validate_ok_many_mixed_active_window() {
        // A small mixed instance to exercise the sweep-line active set.
        // a1 overlaps in time with a2, but in disjoint space; a3 starts later and is disjoint.
        let r1 = req_movable_ok(1, 3, 0, 4, 0, 100, 10);
        let r2 = req_movable_ok(2, 3, 0, 4, 0, 100, 50);
        let r3 = req_movable_ok(3, 6, 0, 3, 0, 100, 30);

        let a1 = Assignment::new(r1, SpacePosition::new(10), TimePoint::new(1)); // [1,5), space [10,13)
        let a2 = Assignment::new(r2, SpacePosition::new(60), TimePoint::new(2)); // [2,6), space [60,63)
        let a3 = Assignment::new(r3, SpacePosition::new(30), TimePoint::new(7)); // [7,10), disjoint in time

        let mut m = HashMap::new();
        m.insert(a1.id(), any_ref(&a1));
        m.insert(a2.id(), any_ref(&a2));
        m.insert(a3.id(), any_ref(&a3));

        let sol = SolutionRef::from_assignments(m);
        assert!(sol.validate().is_ok());
    }
}
