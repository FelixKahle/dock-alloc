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

use dock_alloc_core::{SolverVariable, cost::Cost};
use num_traits::Zero;
use rand::{Rng, SeedableRng, rngs::StdRng};
use rayon::prelude::*;
use std::{
    fmt::{Debug, Display},
    time::{Duration, Instant},
};

use crate::{
    berth::quay::{QuayRead, QuayWrite},
    framework::{
        planning::{Plan, PlanningContext},
        state::{ConstructiveSolver, FeasibleSolverState, FeasibleSolverStateApplyError, Solver},
    },
    meta::{
        config::{AllocationConfig, MetaConfig, ShardConfig, StatsConfig},
        operator::Operator,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub struct OperatorStats<C: SolverVariable> {
    attempts: u64,
    accepted: u64,
    ewma_reward: f64,
    total_improvement: Cost<C>,
    emwa_gen_ns_per_proposal: f64,
    emwa_eval_ns_per_proposal: f64,
}

impl<C: SolverVariable + Zero> Default for OperatorStats<C> {
    fn default() -> Self {
        Self {
            attempts: 0,
            accepted: 0,
            ewma_reward: 0.0,
            total_improvement: Cost::zero(),
            emwa_gen_ns_per_proposal: 0.0,
            emwa_eval_ns_per_proposal: 0.0,
        }
    }
}

impl<C: SolverVariable + Zero> OperatorStats<C> {
    pub fn on_attempt(&mut self) {
        self.attempts += 1;
    }

    pub fn on_accept(&mut self, improvement: Cost<C>, reward_alpha: f64) {
        self.accepted += 1;
        self.total_improvement += improvement;
        let r = improvement.value().to_f64().unwrap_or(0.0);
        self.ewma_reward = ewma(self.ewma_reward, r, reward_alpha);
    }

    pub fn on_timing(&mut self, gen_ns: f64, eval_ns: f64, gen_alpha: f64, eval_alpha: f64) {
        self.emwa_gen_ns_per_proposal = ewma(self.emwa_gen_ns_per_proposal, gen_ns, gen_alpha);
        self.emwa_eval_ns_per_proposal = ewma(self.emwa_eval_ns_per_proposal, eval_ns, eval_alpha);
    }
}

pub struct OperatorRecord<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    operator: Box<dyn Operator<Time = T, Cost = C, Quay = Q>>,
    stats: OperatorStats<C>,
}

impl<T, C, Q> OperatorRecord<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub fn new(operator: Box<dyn Operator<Time = T, Cost = C, Quay = Q>>) -> Self {
        Self {
            operator,
            stats: OperatorStats::default(),
        }
    }

    pub fn operator(&self) -> &dyn Operator<Time = T, Cost = C, Quay = Q> {
        self.operator.as_ref()
    }

    pub fn stats(&self) -> &OperatorStats<C> {
        &self.stats
    }

    pub fn stats_mut(&mut self) -> &mut OperatorStats<C> {
        &mut self.stats
    }
}

struct Candidate<'p, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    op_idx: usize,
    plan: Plan<'p, T, C>,
    gen_ns: f64,
    eval_ns: f64,
}

pub struct MetaEngine<T, C, Q, S>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead + QuayWrite,
    S: ConstructiveSolver<T, C, Q>,
{
    config: MetaConfig,
    operator_records: Vec<OperatorRecord<T, C, Q>>,
    construction_solver: S,
    proposals_made: u64,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MetaEngineError<T, C, Q, S>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead + QuayWrite,
    S: ConstructiveSolver<T, C, Q>,
{
    ConstructionError(S::SolveError),
    StepError(FeasibleSolverStateApplyError<T>),
}

impl<T, C, Q, S> From<FeasibleSolverStateApplyError<T>> for MetaEngineError<T, C, Q, S>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead + QuayWrite,
    S: ConstructiveSolver<T, C, Q>,
{
    fn from(e: FeasibleSolverStateApplyError<T>) -> Self {
        MetaEngineError::StepError(e)
    }
}

impl<T, C, Q, S> MetaEngine<T, C, Q, S>
where
    T: SolverVariable + Send + Sync + Debug,
    C: SolverVariable + Send + Sync + Display,
    Q: QuayRead + QuayWrite + Send + Sync,
    S: ConstructiveSolver<T, C, Q> + Sync,
{
    pub fn new(
        config: MetaConfig,
        ops: impl IntoIterator<Item = Box<dyn Operator<Time = T, Cost = C, Quay = Q> + Send + Sync>>,
        construction_solver: S,
    ) -> Self {
        let operator_records = ops
            .into_iter()
            .map(|op| OperatorRecord::new(op)) // <-- closure enables coercion
            .collect();

        Self {
            config,
            operator_records,
            construction_solver,
            proposals_made: 0,
        }
    }

    pub fn construction_solver(&self) -> &S {
        &self.construction_solver
    }

    pub fn operator_records(&self) -> &[OperatorRecord<T, C, Q>] {
        &self.operator_records
    }

    pub fn construct_initial_state<'p>(
        &mut self,
        problem: &'p dock_alloc_model::model::Problem<T, C>,
    ) -> Result<FeasibleSolverState<'p, T, C, Q>, S::SolveError> {
        self.construction_solver.build_state(problem)
    }

    pub fn step(
        &mut self,
        state: &mut FeasibleSolverState<'_, T, C, Q>,
        iteration: usize,
    ) -> Result<Option<Cost<C>>, FeasibleSolverStateApplyError<T>> {
        let problem = state.problem();
        let ledger = state.ledger();
        let berth = state.berth();

        let anneal = &self.config.anneal;
        let stats_cfg = &self.config.stats;
        let alloc_cfg = &self.config.alloc;
        let shard_cfg = &self.config.shard;
        let rng_cfg = &self.config.random;

        // ——— temperature & tau ———
        let temp = (anneal.initial_temperature * anneal.cooling_rate.powi(iteration as i32))
            .max(anneal.min_temperature);
        let norm = (temp / anneal.initial_temperature).clamp(0.0, 1.0);
        let tau = alloc_cfg.softmax_tau_min
            + (alloc_cfg.softmax_tau_max - alloc_cfg.softmax_tau_min) * norm;

        // ——— allocate proposal budget per operator ———
        let alloc: Vec<usize> = softmax_alloc(
            &self
                .operator_records
                .iter()
                .map(|r| r.stats.clone())
                .collect::<Vec<_>>(),
            alloc_cfg,
            stats_cfg,
            tau,
        );

        // ——— build tasks (chunking) ———
        #[derive(Clone, Copy)]
        struct Task {
            op_idx: usize,
            proposals: usize,
        }
        let mut tasks = Vec::with_capacity(alloc.iter().sum());
        for (op_idx, (rec, &quota)) in self.operator_records.iter().zip(&alloc).enumerate() {
            if quota == 0 {
                continue;
            }
            let preferred = proposals_per_task(&rec.stats, shard_cfg, stats_cfg) as usize;
            let chunk = preferred
                .max(shard_cfg.min_proposals_per_task as usize)
                .min(shard_cfg.max_proposals_per_task as usize)
                .max(1);
            let mut remaining = quota;
            while remaining > 0 {
                let take = remaining.min(chunk);
                tasks.push(Task {
                    op_idx,
                    proposals: take,
                });
                remaining -= take;
            }
        }

        if tasks.is_empty() {
            return Ok(None);
        }

        // ——— parallel candidate generation ———
        let candidates: Vec<Candidate<'_, T, C>> = tasks
            .into_par_iter()
            .filter_map(|task| {
                let rec = &self.operator_records[task.op_idx];

                // stable-ish per-task RNG
                let mut rng = StdRng::seed_from_u64(
                    rng_cfg.seed_base_task
                        ^ (task.op_idx as u64)
                        ^ (task.proposals as u64)
                        ^ (iteration as u64),
                );

                let mut best: Option<Candidate<'_, T, C>> = None;

                for _ in 0..task.proposals {
                    // fresh planning context each attempt (lightweight overlays inside)
                    let ctx = PlanningContext::new(ledger, berth, problem);

                    let t0 = Instant::now();
                    let plan = rec.operator.propose(iteration, &mut rng, ctx);
                    let gen_ns = t0.elapsed().as_nanos() as f64;

                    // discard true no-ops quickly
                    if plan.ledger_commit().operations().is_empty() {
                        continue;
                    }

                    // touch eval so we can time + compare (delta already computed in PlanBuilder::build)
                    let t1 = Instant::now();
                    let _delta = plan.eval().delta_cost();
                    let eval_ns = t1.elapsed().as_nanos() as f64;

                    let cand = Candidate {
                        op_idx: task.op_idx,
                        plan,
                        gen_ns,
                        eval_ns,
                    };

                    // keep the best (lowest) delta within this task
                    let better = match &best {
                        None => true,
                        Some(b) => cand.plan.eval().delta_cost() < b.plan.eval().delta_cost(),
                    };
                    if better {
                        best = Some(cand);
                    }
                }

                best
            })
            .collect();

        if candidates.is_empty() {
            return Ok(None);
        }

        self.proposals_made += candidates.len() as u64;

        // ——— SA selection (accept worse with prob exp(-Δ/T)) ———
        // Start from the first candidate, then do pairwise Metropolis tournament.
        let mut rng = StdRng::seed_from_u64(rng_cfg.seed_base_select ^ iteration as u64);
        let mut winner_idx = 0usize;

        for (i, cand) in candidates.iter().enumerate().skip(1) {
            // Compare candidate i against current winner
            let w = &candidates[winner_idx];
            let d = cand.plan.eval().delta_cost() - w.plan.eval().delta_cost();

            let accept = if d.value() < C::zero() {
                true // strictly better → accept
            } else if d.value() > C::zero() {
                // worse → accept with probability exp(-d/T)
                let dv = d.value().to_f64().unwrap_or(0.0);
                let p = (-dv / temp).exp();
                rng.random::<f64>() < p
            } else {
                // equal delta: reject to reduce churn
                false
            };

            if accept {
                winner_idx = i;
            }
        }

        let winner = candidates.into_iter().nth(winner_idx).unwrap();
        let delta = winner.plan.eval().delta_cost();

        // minimal stats/timing update on the chosen op
        let rec = &mut self.operator_records[winner.op_idx];
        rec.stats_mut().on_attempt();
        rec.stats_mut().on_timing(
            winner.gen_ns,
            winner.eval_ns,
            stats_cfg.gen_time_alpha,
            stats_cfg.eval_time_alpha,
        );

        // ——— apply only if valid on the real state ———
        if state.apply_plan_validated(&winner.plan).is_ok() {
            // improvement tracked as positive → pass -delta
            rec.stats_mut().on_accept(-delta, stats_cfg.reward_alpha);
            return Ok(Some(delta));
        }
        Ok(None)
    }
}

impl<T, C, Q, S> Solver<T, C, Q> for MetaEngine<T, C, Q, S>
where
    T: SolverVariable + Send + Sync + Debug,
    C: SolverVariable + TryFrom<T> + TryFrom<usize> + Send + Sync + Display,
    Q: QuayRead + QuayWrite + Send + Sync,
    S: ConstructiveSolver<T, C, Q> + Sync,
{
    type SolveError = MetaEngineError<T, C, Q, S>;

    fn solve<'p>(
        &mut self,
        problem: &'p dock_alloc_model::model::Problem<T, C>,
    ) -> Result<dock_alloc_model::model::SolutionRef<'p, T, C>, Self::SolveError> {
        // 1) build initial feasible state
        let mut state = self
            .construction_solver
            .build_state(problem)
            .map_err(MetaEngineError::ConstructionError)?;

        // 2) time budget
        let budget = Duration::from_millis(self.config.max_solver_time_ms);
        let t0 = Instant::now();

        // 3) best-so-far tracking
        let mut cum_delta = Cost::<C>::zero();
        let mut best_cum = cum_delta;
        let mut best_state: Option<_> = Some(state.clone());

        let mut iter: usize = 0;
        while t0.elapsed() < budget {
            if let Some(delta) = self.step(&mut state, iter)? {
                cum_delta += delta;
                if cum_delta < best_cum {
                    best_cum = cum_delta;
                    best_state = Some(state.clone());
                }
            }
            iter += 1;
            if (iter & 0xF) == 0 && t0.elapsed() >= budget {
                break;
            }
        }
        let final_state = best_state.unwrap_or(state);
        println!("Iterations: {}", iter);
        println!("Proposals made: {}", self.proposals_made);
        Ok(final_state.into())
    }
}

#[inline]
fn ewma(prev: f64, x: f64, alpha: f64) -> f64 {
    if prev == 0.0 {
        x
    } else {
        alpha * x + (1.0 - alpha) * prev
    }
}

fn proposals_per_task<C: SolverVariable>(
    stats: &OperatorStats<C>,
    shard: &ShardConfig,
    stats_cfg: &StatsConfig,
) -> u64 {
    let ns_per = (stats.emwa_gen_ns_per_proposal + stats.emwa_eval_ns_per_proposal)
        .max(stats_cfg.min_ns_per_proposal);
    let target = (shard.target_task_ns as f64 / ns_per).floor() as u64;
    target.clamp(shard.min_proposals_per_task, shard.max_proposals_per_task)
}

fn softmax_alloc<C: SolverVariable>(
    stats: &[OperatorStats<C>],
    alloc: &AllocationConfig,
    stats_cfg: &StatsConfig,
    tau: f64,
) -> Vec<usize> {
    let n = stats.len();
    if n == 0 {
        return vec![];
    }

    let raw: Vec<f64> = stats
        .iter()
        .map(|s| {
            let ns_per = (s.emwa_gen_ns_per_proposal + s.emwa_eval_ns_per_proposal)
                .max(stats_cfg.min_ns_per_proposal);
            let speed = 1.0 / ns_per;
            let succ = if s.attempts > 0 {
                s.accepted as f64 / s.attempts as f64
            } else {
                stats_cfg.bootstrap_success_rate
            };
            alloc.speed_weight * speed + alloc.success_weight * succ
        })
        .collect();

    let maxv = raw.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
    let t = tau.max(1e-6); // numerical guard, could also be another knob
    let exps: Vec<f64> = raw.iter().map(|&v| ((v - maxv) / t).exp()).collect();
    let sum: f64 = exps.iter().sum::<f64>().max(alloc.softmax_eps);

    exps.into_iter()
        .map(|w| (w / sum) * alloc.target_total_proposals_per_round as f64)
        .map(|x| x.round() as usize)
        .map(|a| a.clamp(alloc.min_per_op, alloc.max_per_op))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{berth::quay::BTreeMapQuay, framework::planning::PlanEval, greedy::GreedySolver};
    use static_assertions::{assert_impl_all, assert_type_eq_all};

    type T = i64;
    type C = i64;
    type Q = BTreeMapQuay;
    type S = GreedySolver<T, C, Q>;

    assert_type_eq_all!(T, i64);
    assert_type_eq_all!(C, i64);

    #[allow(dead_code)]
    type DynOp = dyn Operator<Time = T, Cost = C, Quay = Q>;
    type DynOpBox = Box<dyn Operator<Time = T, Cost = C, Quay = Q> + Send + Sync>;
    assert_impl_all!(DynOpBox: Send, Sync);

    assert_impl_all!(Q: Send, Sync);
    assert_impl_all!(OperatorRecord<T, C, Q>: Send, Sync);
    assert_impl_all!(MetaEngine<T, C, Q, S>: Send, Sync);
    assert_impl_all!(Plan<'static, T, C>: Send);
    assert_impl_all!(PlanEval<T, C>: Send);
    assert_impl_all!(OperatorStats<C>: Send, Sync);

    #[allow(dead_code)]
    type MetaSolverType = MetaEngine<T, C, Q, S>;
}
