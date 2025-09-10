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
use dock_alloc_core::time::{TimeInterval, TimePoint};
use dock_alloc_model::model::{AssignmentRef, Problem, SolutionRef};
use num_traits::{PrimInt, Signed};
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
pub struct GreedySolver;

impl Default for GreedySolver {
    fn default() -> Self {
        Self::new()
    }
}

impl GreedySolver {
    pub fn new() -> Self {
        Self
    }
}

impl<T, C, Q> Solver<T, C, Q> for GreedySolver
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + QuayWrite,
{
    type SolveError = GreedySolverError;

    fn solve<'p>(
        &self,
        problem: &'p Problem<T, C>,
    ) -> Result<SolutionRef<'p, T, C>, Self::SolveError> {
        let state: FeasibleSolverState<'p, T, C, Q> = self.build_state(problem)?;
        Ok(state.into())
    }
}

impl<T, C, Q> ConstructiveSolver<T, C, Q> for GreedySolver
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + QuayWrite,
{
    type SolveError = GreedySolverError;

    fn build_state<'p>(
        &self,
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
                let mut ready_order = b.with_explorer(|ex| {
                    ex.iter_unassigned_requests()
                        .filter(|req| {
                            let tw = req.feasible_time_window();
                            req.request().arrival_time() <= t && tw.contains(t)
                        })
                        .map(|req| {
                            let proc = req.processing_duration();
                            let tw = req.feasible_time_window();
                            let latest_start = tw.end() - proc;
                            let slack = latest_start - t;
                            let len_key = Reverse(req.length().value());
                            let arr_key = req.request().arrival_time().value();

                            (req.id(), slack.value(), len_key, arr_key)
                        })
                        .collect::<Vec<_>>()
                });

                ready_order
                    .sort_by_key(|&(_id, slack_v, len_key, arr_key)| (slack_v, len_key, arr_key));
                let mut deps = Vec::new();

                for (rid, _slack_v, _len_key, _arr_key) in ready_order {
                    let decision = b.with_explorer(|ex| {
                        let req = ex.iter_unassigned_requests().find(|r| r.id() == rid)?;
                        let proc = req.processing_duration();
                        let swin = req.feasible_space_window();
                        let twin_now = TimeInterval::new(t, t + proc);
                        let mut best_now_cost = None;
                        let mut best_now_slot = None;

                        for slot in ex.iter_slots_for_request_within(&req, twin_now, swin) {
                            if slot.slot().start_time() != t {
                                continue;
                            }
                            let c =
                                AssignmentRef::new(req.request(), slot.slot().space().start(), t)
                                    .cost();

                            if best_now_cost.is_none_or(|b| c < b) {
                                best_now_cost = Some(c);
                                best_now_slot = Some(slot);
                            }
                        }

                        let best_later_cost = match t_next_opt {
                            Some(tn) if req.feasible_time_window().contains(tn) => {
                                let twin_later = TimeInterval::new(tn, tn + proc);
                                let mut best = None;
                                for slot in ex.iter_slots_for_request_within(&req, twin_later, swin)
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
                                best
                            }
                            _ => None,
                        };

                        match (best_now_cost, best_later_cost) {
                            (None, None) => None,
                            (Some(_), None) => Some((req, best_now_slot.unwrap(), proc)),
                            (None, Some(_)) => None,
                            (Some(c_now), Some(c_later)) => {
                                if c_now <= c_later {
                                    Some((req, best_now_slot.unwrap(), proc))
                                } else {
                                    None
                                }
                            }
                        }
                    });

                    if let Some((req, slot, proc)) = decision
                        && b.propose_assign(&req, slot).is_ok()
                    {
                        deps.push(t + proc);
                    }
                }

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
    use super::*;
    use crate::berth::prelude::BooleanVecQuay;

    use dock_alloc_core::{
        cost::Cost,
        space::{SpaceInterval, SpaceLength, SpacePosition},
        time::TimeDelta,
    };
    use dock_alloc_model::{
        generator::{InstanceGenConfig, InstanceGenerator, SpaceWindowPolicy, TimeWindowPolicy},
        model::{Assignment, Fixed, Movable, ProblemBuilder, Request, RequestId},
    };

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
        target: usize,
    ) -> Request<Movable, Tm, Cm> {
        Request::<Movable, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimeDelta::new(proc_t),
            SpacePosition::new(target),
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
        target: usize,
    ) -> Request<Fixed, Tm, Cm> {
        Request::<Fixed, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimeDelta::new(proc_t),
            SpacePosition::new(target), // target_position
            Cost::new(1),
            Cost::new(1),
            TimeInterval::new(TimePoint::new(t0), TimePoint::new(t1)),
            SpaceInterval::new(SpacePosition::new(s0), SpacePosition::new(s1)),
        )
        .expect("valid fixed request")
    }

    #[test]
    fn test_greedy_assigns_at_arrival_when_free() {
        // quay has plenty of space; both ships can start at arrival t=0 at their targets
        let mut pb = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(200));
        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 200, 0);
        let r2 = req_movable_ok(2, 10, 5, 0, 100, 0, 200, 50);
        pb.add_movable_request(r1.clone()).unwrap();
        pb.add_movable_request(r2.clone()).unwrap();

        let problem = pb.build();

        let solver = GreedySolver::new();
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
            let sw = r.feasible_space_window();
            assert!(sw.contains(s), "start pos {s} not in window {sw}");
        }
    }

    #[test]
    fn test_greedy_waits_until_fixed_departure_if_blocked() {
        // Fixed occupies [0,10) in space during [0,5) time at position 0..10.
        // Movable arrives at t=0 needs same space; should be placed at t=5.
        let mut pb = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(20));

        let rf = req_fixed_ok(10, 10, 5, 0, 100, 0, 20, 0);
        pb.add_preassigned(Assignment::new(
            rf.clone(),
            SpacePosition::new(0),
            TimePoint::new(0),
        ))
        .unwrap(); // occupies [space 0..10) x [time 0..5)

        let rm = req_movable_ok(1, 10, 5, 0, 100, 0, 20, 0);
        pb.add_movable_request(rm.clone()).unwrap();

        let problem = pb.build();
        let solver = GreedySolver::new();
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

        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 10, 0);
        let r2 = req_movable_ok(2, 10, 5, 0, 100, 0, 10, 0);

        pb.add_movable_request(r1.clone()).unwrap();
        pb.add_movable_request(r2.clone()).unwrap();

        let problem = pb.build();
        let solver = GreedySolver::new();
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
        let r1 = req_movable_ok(1, 10, 5, 0, 100, 0, 200, 0);
        let r2 = req_movable_ok(2, 10, 5, 0, 100, 0, 200, 50);
        pb.add_movable_request(r1.clone()).unwrap();
        pb.add_movable_request(r2.clone()).unwrap();

        let problem = pb.build();
        let solver = GreedySolver::new();

        let sol = <GreedySolver as Solver<i64, i64, BooleanVecQuay>>::solve(&solver, &problem)
            .expect("solve");

        assert_eq!(sol.decisions().len(), 2);
        assert_eq!(sol.stats().total_waiting_time(), TimeDelta::new(0));

        for a in sol.decisions().values() {
            assert_eq!(a.start_time(), TimePoint::new(0));
            let sw = a.request().feasible_space_window();
            assert!(sw.contains(a.start_position()));
        }
    }

    #[test]
    fn test_greedy_infeasible_tight_windows_errors_not_partial() {
        use crate::berth::prelude::BooleanVecQuay;
        type Tm = i64;
        type Cm = i64;

        // Quay fits only one length-10 ship.
        let mut pb = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(10));

        // Both must start at t=0 (proc=5; window [0,5)).
        let r1 = Request::<Movable, _, _>::new(
            RequestId::new(1),
            SpaceLength::new(10),
            TimeDelta::new(5),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            TimeInterval::new(TimePoint::new(0), TimePoint::new(5)),
            SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10)),
        )
        .unwrap();

        let r2 = Request::<Movable, _, _>::new(
            RequestId::new(2),
            SpaceLength::new(10),
            TimeDelta::new(5),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            TimeInterval::new(TimePoint::new(0), TimePoint::new(5)),
            SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10)),
        )
        .unwrap();

        pb.add_movable_request(r1).unwrap();
        pb.add_movable_request(r2).unwrap();
        let problem = pb.build();

        let solver = GreedySolver::new();

        // build_state must error (cannot assign both)
        let state_res: Result<FeasibleSolverState<'_, Tm, Cm, BooleanVecQuay>, _> =
            solver.build_state(&problem);
        assert!(state_res.is_err(), "expected infeasible, got state OK");

        // solve must error too (no partial SolutionRef)
        let solve_res =
            <GreedySolver as Solver<i64, i64, BooleanVecQuay>>::solve(&solver, &problem);
        assert!(solve_res.is_err(), "expected infeasible, got solution OK");
    }

    #[test]
    fn test_greedy_solves_large_instance() {
        let config = InstanceGenConfig::new(
            SpaceLength::new(1_500), // quay_length
            SpaceLength::new(80),    // min_length
            SpaceLength::new(300),   // max_length
            SpaceWindowPolicy::FullQuay,
            TimeWindowPolicy::FullHorizon,
            400,                      // amount_movables
            0,                        // amount_fixed
            TimePoint::new(10000),    // horizon
            0.9,                      // lambda_per_time
            2.5,                      // processing_time_sigma
            TimeDelta::new(4),        // min_processing
            Some(TimeDelta::new(72)), // max_processing
            TimeDelta::new(12),       // time_slack
            TimeDelta::new(2),        // fixed_gap
            TimeDelta::new(10),       // processing_mu_base
            TimeDelta::new(20),       // processing_mu_span
            6,                        // arrival_oversample_mult
            0.1,                      // processing_sigma_floor
            SpaceLength::new(1),      // length_span_epsilon
            Cost::new(1),             // cost_inc_num (ramp up to +100% at max length)
            Cost::new(1),             // cost_inc_den
            Cost::new(1),             // min_cost_floor
            SpaceLength::new(1),      // window_split_left_num (50/50)
            SpaceLength::new(2),      // window_split_den
            Cost::new(2),             // base_cost_per_delay
            Cost::new(1),             // base_cost_per_dev
            28,
        )
        .unwrap();

        let mut generator = InstanceGenerator::new(config);
        let problem = generator.generate();

        let solver = GreedySolver::new();
        let state: FeasibleSolverState<'_, Tm, Cm, BooleanVecQuay> =
            solver.build_state(&problem).unwrap();
        assert_eq!(
            state.ledger().iter_movable_assignments().count(),
            problem.iter_movable_requests().count()
        );
    }
}
