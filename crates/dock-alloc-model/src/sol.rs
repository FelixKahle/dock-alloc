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
    id::RequestId,
};
use dock_alloc_core::{SolverVariable, cost::Cost, space::SpaceLength, time::TimeDelta};
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
}
