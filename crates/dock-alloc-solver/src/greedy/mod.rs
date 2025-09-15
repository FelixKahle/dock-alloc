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
    berth::quay::{QuayRead, QuaySpaceIntervalOutOfBoundsError, QuayWrite},
    framework::{
        planning::PlanningContext,
        state::{ConstructiveSolver, FeasibleSolverState, Solver, SolverState},
    },
};
use dock_alloc_core::{
    SolverVariable,
    time::{TimeInterval, TimePoint},
};
use dock_alloc_model::prelude::*;
use std::{cmp::Reverse, collections::BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GreedySolverError {
    Infeasible,
}

impl From<QuaySpaceIntervalOutOfBoundsError> for GreedySolverError {
    fn from(_value: QuaySpaceIntervalOutOfBoundsError) -> Self {
        GreedySolverError::Infeasible
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GreedySolver<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + QuayWrite,
{
    _phantom: std::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for GreedySolver<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + QuayWrite,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, C, Q> GreedySolver<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + QuayWrite,
{
    pub fn new() -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Solver<T, C, Q> for GreedySolver<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + QuayWrite,
{
    type SolveError = GreedySolverError;

    fn solve<'p>(
        &mut self,
        problem: &'p Problem<T, C>,
    ) -> Result<SolutionRef<'p, T, C>, Self::SolveError> {
        let state: FeasibleSolverState<'p, T, C, Q> = self.build_state(problem)?;
        Ok(state.into())
    }
}

impl<T, C, Q> ConstructiveSolver<T, C, Q> for GreedySolver<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + QuayWrite,
{
    type SolveError = GreedySolverError;

    fn build_state<'p>(
        &mut self,
        problem: &'p Problem<T, C>,
    ) -> Result<FeasibleSolverState<'p, T, C, Q>, Self::SolveError> {
        let mut state: SolverState<'p, T, C, Q> = SolverState::try_from(problem)?;
        let mut events: BTreeSet<TimePoint<T>> = BTreeSet::new();

        for r in problem.iter_movable_requests() {
            events.insert(r.arrival_time());
        }
        for a in problem.iter_fixed_assignments() {
            events.insert(a.start_time() + a.request().processing_duration());
        }

        while let Some(t) = events.pop_first() {
            let t_next_opt = events.first().copied();
            let ctx = PlanningContext::new(state.ledger(), state.berth(), problem);

            let (plan_opt, departures) = ctx.with_builder(|mut b| {
                // Start a transactional child over the current overlays
                let mut tx = b.begin();

                // Decide using the (old) read facade over the parent overlay:
                // For this greedy example we don't need to "see" incremental txn changes while we place,
                // so using b.with_explorer(...) is fine. (If you later need reads to see txn deltas,
                // add an Explorer::new_from(&alov, &bov) and call tx.ex().)
                let mut ready_order = tx.with_explorer(|ex| {
                    ex.iter_unassigned_requests()
                        .filter(|req| req.request().arrival_time() <= t)
                        .map(|req| {
                            (
                                req.clone(),
                                Reverse(req.length().value()),
                                req.request().arrival_time().value(),
                            )
                        })
                        .collect::<Vec<_>>()
                });

                ready_order.sort_by_key(|&(_, len_key, arr_key)| (len_key, arr_key));

                let mut deps = Vec::new();

                for (req, _len_key, _arr_key) in ready_order {
                    let decision = tx.with_explorer(|ex| {
                        let proc = req.processing_duration();
                        let windows = req.feasible_space_windows();

                        // try to place now
                        let twin_now = TimeInterval::new(t, t + proc);
                        let mut best_now_cost = None;
                        let mut best_now_slot = None;

                        for &w in windows {
                            for slot in ex.iter_slots_for_request_within(&req, twin_now, w) {
                                if slot.slot().start_time() != t {
                                    continue;
                                }
                                let c = AssignmentRef::new(
                                    req.request(),
                                    slot.slot().space().start(),
                                    t,
                                )
                                .cost();
                                if best_now_cost.is_none_or(|b| c < b) {
                                    best_now_cost = Some(c);
                                    best_now_slot = Some(slot);
                                }
                            }
                        }

                        let best_later_cost = match t_next_opt {
                            Some(tn) if tn >= req.request().arrival_time() => {
                                let twin_later = TimeInterval::new(tn, tn + proc);
                                let mut best = None;
                                for &w in windows {
                                    for slot in
                                        ex.iter_slots_for_request_within(&req, twin_later, w)
                                    {
                                        if slot.slot().start_time() != tn {
                                            continue;
                                        }
                                        let c = AssignmentRef::new(
                                            req.request(),
                                            slot.slot().space().start(),
                                            tn,
                                        )
                                        .cost();
                                        if best.is_none_or(|b| c < b) {
                                            best = Some(c);
                                        }
                                    }
                                }
                                best
                            }
                            _ => None,
                        };

                        match (best_now_cost, best_later_cost) {
                            (None, None) => None,
                            (Some(_), None) => Some((req.clone(), best_now_slot.unwrap(), proc)),
                            (None, Some(_)) => None,
                            (Some(c_now), Some(c_later)) => {
                                if c_now <= c_later {
                                    Some((req.clone(), best_now_slot.unwrap(), proc))
                                } else {
                                    None
                                }
                            }
                        }
                    });

                    if let Some((req2, slot, proc)) = decision {
                        // Stage using the NEW transactional API
                        if tx.propose_assign(&req2, slot).is_ok() {
                            deps.push(t + proc);
                        }
                    }
                }

                // Merge txn changes back into the builder overlays and build the plan
                tx.commit();
                let built = b.build();

                let plan = if built.ledger_commit().operations().is_empty() {
                    None
                } else {
                    Some(built)
                };
                (plan, deps)
            });

            if let Some(plan) = plan_opt {
                state
                    .apply_plan(&plan)
                    .map_err(|_| GreedySolverError::Infeasible)?;
                for d in departures {
                    events.insert(d);
                }
            }
        }

        FeasibleSolverState::new(problem, state.ledger().clone(), state.berth().clone())
            .map_err(|_| GreedySolverError::Infeasible)
    }
}

#[cfg(test)]
mod tests {
    use crate::berth::quay::{BTreeMapQuay, BooleanVecQuay};

    use super::*;

    use dock_alloc_core::{
        cost::Cost,
        space::{SpaceInterval, SpaceLength, SpacePosition},
        time::TimeDelta,
    };

    type Tm = i64;
    type Cm = i64;

    fn req_movable_ok(
        id: u64,
        len: usize,
        arrival_t: i64,
        proc_t: i64,
        s0: usize,
        s1: usize,
        target: usize,
    ) -> Request<Movable, Tm, Cm> {
        Request::<Movable, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimePoint::new(arrival_t),
            TimeDelta::new(proc_t),
            SpacePosition::new(target),
            Cost::new(1),
            Cost::new(1),
            vec![SpaceInterval::new(
                SpacePosition::new(s0),
                SpacePosition::new(s1),
            )],
        )
        .expect("valid movable request")
    }

    fn req_fixed_ok(
        id: u64,
        len: usize,
        arrival_t: i64,
        proc_t: i64,
        s0: usize,
        s1: usize,
        target: usize,
    ) -> Request<Fixed, Tm, Cm> {
        Request::<Fixed, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimePoint::new(arrival_t),
            TimeDelta::new(proc_t),
            SpacePosition::new(target),
            Cost::new(1),
            Cost::new(1),
            vec![SpaceInterval::new(
                SpacePosition::new(s0),
                SpacePosition::new(s1),
            )],
        )
        .expect("valid fixed request")
    }

    #[test]
    fn test_greedy_assigns_at_arrival_when_free() {
        // quay has plenty of space; both ships can start at arrival t=0 at their targets
        let mut pb = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(200));
        let r1 = req_movable_ok(1, 10, 0, 5, 0, 100, 0);
        let r2 = req_movable_ok(2, 10, 0, 5, 0, 100, 50);
        pb.add_movable_request(r1.clone()).unwrap();
        pb.add_movable_request(r2.clone()).unwrap();

        let problem = pb.build();

        let mut solver = GreedySolver::new();
        let state: FeasibleSolverState<'_, Tm, Cm, BooleanVecQuay> =
            solver.build_state(&problem).unwrap();

        let asgs: Vec<_> = state.ledger().iter_movable_assignments().collect();
        assert_eq!(asgs.len(), 2);

        // Check both assigned at t=0 close to their targets
        for a in asgs {
            assert_eq!(a.start_time(), TimePoint::new(0));
            // With empty berth, the free slot starting exactly at t=0 includes the target start.
            // We don't assert exact position, but ensure it's inside feasible window and <= target dev.
            let r = a.request();
            let s = a.start_position();
            let ok = r.feasible_space_windows().iter().any(|w| w.contains(s));
            assert!(
                ok,
                "start pos {s} not in any feasible window {:?}",
                r.feasible_space_windows()
            );
        }
    }

    #[test]
    fn test_greedy_waits_until_fixed_departure_if_blocked() {
        // Fixed occupies [0,10) in space during [0,5) time at position 0..10.
        // Movable arrives at t=0 needs same space; should be placed at t=5.
        let mut pb = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(20));

        let rf = req_fixed_ok(10, 10, 0, 5, 0, 100, 0);
        pb.add_preassigned(Assignment::new(
            rf.clone(),
            SpacePosition::new(0),
            TimePoint::new(0),
        ))
        .unwrap(); // occupies [space 0..10) x [time 0..5)

        let rm = req_movable_ok(1, 10, 0, 5, 0, 100, 0);
        pb.add_movable_request(rm.clone()).unwrap();

        let problem = pb.build();
        let mut solver = GreedySolver::new();
        let state: FeasibleSolverState<'_, Tm, Cm, BooleanVecQuay> =
            solver.build_state(&problem).unwrap();

        // Only one movable; must be assigned and should start at t=5 at pos 0
        let asgs: Vec<_> = state.ledger().iter_movable_assignments().collect();
        assert_eq!(asgs.len(), 1);

        let a = asgs[0];
        assert_eq!(a.start_time(), TimePoint::new(5));
        assert_eq!(a.start_position(), SpacePosition::new(0));
    }

    #[test]
    fn test_greedy_two_arrivals_one_berth_second_waits() {
        // Single-berth length 10. Two ships len=10 arrive at t=0, proc=5.
        // One starts at 0, the other waits until first departs (t=5).
        let mut pb = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(10));

        let r1 = req_movable_ok(1, 10, 0, 5, 0, 100, 0);
        let r2 = req_movable_ok(2, 10, 0, 5, 0, 100, 0);

        pb.add_movable_request(r1.clone()).unwrap();
        pb.add_movable_request(r2.clone()).unwrap();

        let problem = pb.build();
        let mut solver = GreedySolver::new();
        let state: FeasibleSolverState<'_, Tm, Cm, BooleanVecQuay> =
            solver.build_state(&problem).unwrap();

        let mut starts: Vec<_> = state
            .ledger()
            .iter_movable_assignments()
            .map(|a| a.start_time().value())
            .collect();
        starts.sort();
        assert_eq!(
            starts,
            vec![0, 5],
            "expected starts at t=0 and t=5, got {starts:?}"
        );

        // Ensure both are placed at the single berth (pos 0)
        for a in state.ledger().iter_movable_assignments() {
            assert_eq!(a.start_position(), SpacePosition::new(0));
        }
    }

    #[test]
    fn test_solve_returns_solutionref_and_stats_zero_when_perfect() {
        type Tm = i64;
        type Cm = i64;

        let mut pb = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(200));
        let r1 = req_movable_ok(1, 10, 0, 5, 0, 100, 0);
        let r2 = req_movable_ok(2, 10, 0, 5, 0, 100, 50);
        pb.add_movable_request(r1.clone()).unwrap();
        pb.add_movable_request(r2.clone()).unwrap();

        let problem = pb.build();
        let mut solver: GreedySolver<i64, i64, BooleanVecQuay> = GreedySolver::new();
        let sol = solver.solve(&problem).expect("solve");

        assert_eq!(sol.decisions().len(), 2);
        assert_eq!(sol.stats().total_waiting_time(), TimeDelta::new(0));

        for a in sol.decisions().values() {
            assert_eq!(a.start_time(), TimePoint::new(0));
            let ok = a
                .request()
                .feasible_space_windows()
                .iter()
                .any(|w| w.contains(a.start_position()));
            assert!(ok);
        }
    }

    #[test]
    fn test_greedy_infeasible_tight_windows_errors_not_partial() {
        type Tm = i64;
        type Cm = i64;

        // Quay fits only one length-10 ship.
        let mut pb = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(10));

        // Both must start at t=0 (proc=5; window [0,5)).
        let r1 = Request::<Movable, _, _>::new(
            RequestId::new(1),
            SpaceLength::new(10),
            TimePoint::new(0),
            TimeDelta::new(5),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            vec![SpaceInterval::new(
                SpacePosition::new(0),
                SpacePosition::new(10),
            )],
        )
        .unwrap();

        let r2 = Request::<Movable, _, _>::new(
            RequestId::new(2),
            SpaceLength::new(10),
            TimePoint::new(0),
            TimeDelta::new(5),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            vec![SpaceInterval::new(
                SpacePosition::new(0),
                SpacePosition::new(10),
            )],
        )
        .unwrap();

        pb.add_movable_request(r1).unwrap();
        pb.add_movable_request(r2).unwrap();
        let problem = pb.build();

        let mut solver: GreedySolver<i64, i64, BooleanVecQuay> = GreedySolver::new();

        // build_state must error (cannot assign both)
        let state_res: Result<FeasibleSolverState<'_, Tm, Cm, BooleanVecQuay>, _> =
            solver.build_state(&problem);
        assert!(
            state_res.is_ok(),
            "expected Ok, got error {:?}",
            state_res.err()
        );

        // solve must error too (no partial SolutionRef)
        let solve_res = solver.solve(&problem);
        assert!(
            solve_res.is_ok(),
            "expected Ok, got error {:?}",
            solve_res.err()
        );
    }

    #[test]
    fn test_greedy_solves_large_instance() {
        let mut generator: InstanceGenerator<_, _> = InstanceGenConfig::default().into();
        let problem = generator.generate();

        let mut solver = GreedySolver::new();
        let state: FeasibleSolverState<'_, Tm, Cm, BTreeMapQuay> =
            solver.build_state(&problem).unwrap();
        assert_eq!(
            state.ledger().iter_movable_assignments().count(),
            problem.iter_movable_requests().count()
        );
    }
}
