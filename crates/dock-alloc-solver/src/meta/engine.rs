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
    berth::quay::{QuayRead, QuayWrite},
    framework::{
        planning::{Plan, PlanningContext},
        state::{ConstructiveSolver, FeasibleSolverState, FeasibleSolverStateApplyError, Solver},
    },
    meta::{
        config::{AllocationConfig, MetaConfig, StatsConfig},
        operator::Operator,
    },
};
use dock_alloc_core::{SolverVariable, cost::Cost};
use dock_alloc_model::prelude::*;
use num_traits::Zero;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use rayon::prelude::*;
use std::{
    fmt::{Debug, Display},
    time::{Duration, Instant},
};
use tracing::{debug, info, instrument, trace, warn};

#[inline]
fn acceptance_prob<C: SolverVariable>(delta: Cost<C>, temp: f64) -> f64 {
    let dv = delta.value();
    if dv < C::zero() {
        1.0
    } else if dv > C::zero() {
        let f = dv.to_f64().unwrap_or(f64::INFINITY);
        (-f / temp.max(1e-12)).exp()
    } else {
        0.0
    }
}

#[derive(Debug)]
struct Candidate<'p, T: SolverVariable, C: SolverVariable> {
    op_idx: usize,
    plan: Plan<'p, T, C>,
    gen_ns: f64,
    eval_ns: f64,
    delta: Cost<C>,
}

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
    #[inline]
    pub fn on_attempt(&mut self) {
        self.attempts += 1;
    }

    #[inline]
    pub fn on_accept(&mut self, improvement: Cost<C>, reward_alpha: f64) {
        self.accepted += 1;
        self.total_improvement += improvement;
        let r = improvement.value().to_f64().unwrap_or(0.0);
        self.ewma_reward = ewma(self.ewma_reward, r, reward_alpha);
    }

    #[inline]
    pub fn on_timing(&mut self, gen_ns: f64, eval_ns: f64, gen_alpha: f64, eval_alpha: f64) {
        if gen_ns > 0.0 {
            self.emwa_gen_ns_per_proposal = ewma(self.emwa_gen_ns_per_proposal, gen_ns, gen_alpha);
        }
        if eval_ns > 0.0 {
            self.emwa_eval_ns_per_proposal =
                ewma(self.emwa_eval_ns_per_proposal, eval_ns, eval_alpha);
        }
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

    #[inline]
    pub fn operator(&self) -> &dyn Operator<Time = T, Cost = C, Quay = Q> {
        self.operator.as_ref()
    }

    #[inline]
    pub fn stats(&self) -> &OperatorStats<C> {
        &self.stats
    }

    #[inline]
    pub fn stats_mut(&mut self) -> &mut OperatorStats<C> {
        &mut self.stats
    }
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

impl<T, C, Q, S> Display for MetaEngineError<T, C, Q, S>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead + QuayWrite,
    S: ConstructiveSolver<T, C, Q>,
    S::SolveError: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MetaEngineError::ConstructionError(e) => write!(f, "Construction error: {e:?}"),
            MetaEngineError::StepError(e) => write!(f, "Step error: {e}"),
        }
    }
}

#[inline]
fn make_job_rng(base_seed: u64, op_idx: usize, k: usize, iter: usize) -> ChaCha8Rng {
    let s = base_seed
        ^ ((op_idx as u64).wrapping_mul(0x9E37_79B1_85EB_CA87))
        ^ ((k as u64).rotate_left(17))
        ^ ((iter as u64).wrapping_mul(0xD134_2543_DE82_E285));
    ChaCha8Rng::seed_from_u64(s)
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
        let operator_records = ops.into_iter().map(|op| OperatorRecord::new(op)).collect();
        Self {
            config,
            operator_records,
            construction_solver,
            proposals_made: 0,
        }
    }

    #[inline]
    pub fn construction_solver(&self) -> &S {
        &self.construction_solver
    }

    #[inline]
    pub fn operator_records(&self) -> &[OperatorRecord<T, C, Q>] {
        &self.operator_records
    }

    pub fn construct_initial_state<'p>(
        &mut self,
        problem: &'p Problem<T, C>,
    ) -> Result<FeasibleSolverState<'p, T, C, Q>, S::SolveError> {
        self.construction_solver.build_state(problem)
    }

    #[instrument(skip_all, fields(iteration, temp, tau), err(Display))]
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
        let rng_cfg = &self.config.random;

        let temp = (anneal.initial_temperature * anneal.cooling_rate.powi(iteration as i32))
            .max(anneal.min_temperature);
        let norm = (temp / anneal.initial_temperature).clamp(0.0, 1.0);
        let tau = alloc_cfg.softmax_tau_min
            + (alloc_cfg.softmax_tau_max - alloc_cfg.softmax_tau_min) * norm;

        tracing::Span::current().record("iteration", iteration);
        tracing::Span::current().record("temp", temp);
        tracing::Span::current().record("tau", tau);

        // Softmax allocation across operators
        let alloc = softmax_alloc(
            &self
                .operator_records
                .iter()
                .map(|r| r.stats.clone())
                .collect::<Vec<_>>(),
            alloc_cfg,
            stats_cfg,
            tau,
        );

        let total_jobs: usize = alloc.iter().sum();
        if total_jobs == 0 {
            trace!("No operators selected for this round (allocation sum = 0)");
            return Ok(None);
        }

        // Build job list (op index, per-op counter)
        let jobs: Vec<(usize, usize)> = alloc
            .iter()
            .enumerate()
            .flat_map(|(op_idx, &n)| (0..n).map(move |k| (op_idx, k)))
            .collect();

        let base_seed = rng_cfg.seed_base_task ^ (iteration as u64);

        // Generate candidates in parallel
        let candidates: Vec<Candidate<'_, T, C>> = jobs
            .par_iter()
            .filter_map(|&(op_idx, k)| {
                // Every job gets its own RNG
                let mut rng = make_job_rng(base_seed, op_idx, k, iteration);
                let rec = &self.operator_records[op_idx];

                // Context is cheap to build and read-only
                let ctx = PlanningContext::new(ledger, berth, problem);

                // Stochastic timing sampling to reduce overhead
                let sample_timing = (((base_seed as usize) ^ op_idx ^ k) & 0x7) == 0;

                let (plan, gen_ns) = if sample_timing {
                    let t0 = Instant::now();
                    let p = rec.operator.propose(iteration, &mut rng, ctx);
                    (p, t0.elapsed().as_nanos() as f64)
                } else {
                    (rec.operator.propose(iteration, &mut rng, ctx), 0.0)
                };

                // Skip no-ops
                if plan.ledger_commit().operations().is_empty() {
                    return None;
                }

                // Evaluate delta; optionally sample eval timing too
                let (delta, eval_ns) = if sample_timing {
                    let t1 = Instant::now();
                    let d = plan.eval().delta_cost();
                    (d, t1.elapsed().as_nanos() as f64)
                } else {
                    (plan.eval().delta_cost(), 0.0)
                };

                Some(Candidate {
                    op_idx,
                    plan,
                    gen_ns,
                    eval_ns,
                    delta,
                })
            })
            .collect();

        if candidates.is_empty() {
            trace!("All generated plans were no-ops; nothing to apply.");
            return Ok(None);
        }

        // Stats: mark an attempt for every *produced* candidate and feed timing into EWMA
        for c in &candidates {
            let rec = &mut self.operator_records[c.op_idx];
            rec.stats_mut().on_attempt();
            if c.gen_ns > 0.0 || c.eval_ns > 0.0 {
                rec.stats_mut().on_timing(
                    c.gen_ns,
                    c.eval_ns,
                    stats_cfg.gen_time_alpha,
                    stats_cfg.eval_time_alpha,
                );
            }
        }

        self.proposals_made += candidates.len() as u64;

        // Simulated annealing selection: walk once and decide acceptance against current winner
        let mut winner_idx = 0usize;
        for i in 1..candidates.len() {
            let cur = &candidates[i];
            let win = &candidates[winner_idx];
            // Prefer moves with higher acceptance probability vs. current winner
            let d = cur.delta - win.delta;
            let p = acceptance_prob(d, temp);
            if p > 0.0 {
                // Flip once
                if rand::random::<f64>() < p {
                    winner_idx = i;
                }
            }
        }

        let winner = candidates
            .into_iter()
            .nth(winner_idx)
            .expect("winner must exist");
        let winner_op = self.operator_records[winner.op_idx].operator.name();

        info!(op_index = winner.op_idx, op = winner_op, %temp, %tau, delta = %winner.delta, "Selected winner");

        // Try to apply
        match state.apply_plan_validated(&winner.plan) {
            Ok(()) => {
                // Reward the winning operator
                let rec = &mut self.operator_records[winner.op_idx];
                rec.stats_mut()
                    .on_accept(winner.delta, stats_cfg.reward_alpha);

                trace!("Applied plan successfully.");
                Ok(Some(winner.delta))
            }
            Err(e) => {
                // This shouldn’t happen often because we pre-validated ledger ops,
                // but if it does, we just report and skip the delta.
                warn!(error = %e, op = winner_op, "Plan application failed; skipping.");
                Err(e)
            }
        }
    }
}

impl<T, C, Q, S> Solver<T, C, Q> for MetaEngine<T, C, Q, S>
where
    T: SolverVariable + Send + Sync + Debug,
    C: SolverVariable + TryFrom<T> + TryFrom<usize> + Send + Sync + Display,
    Q: QuayRead + QuayWrite + Send + Sync,
    S: ConstructiveSolver<T, C, Q> + Sync,
    S::SolveError: std::fmt::Debug,
{
    type SolveError = MetaEngineError<T, C, Q, S>;

    #[instrument(skip_all, fields(max_ms = self.config.max_solver_time_ms), err(Display))]
    fn solve<'p>(
        &mut self,
        problem: &'p Problem<T, C>,
    ) -> Result<SolutionRef<'p, T, C>, Self::SolveError> {
        // 1) Build initial feasible state
        let mut state = self
            .construction_solver
            .build_state(problem)
            .map_err(MetaEngineError::ConstructionError)?;

        // 2) Budget
        let budget = Duration::from_millis(self.config.max_solver_time_ms);
        let t0 = Instant::now();

        // 3) Best-so-far tracking
        let mut cum_delta = Cost::<C>::zero();
        let mut best_cum = cum_delta;
        let mut best_state: Option<_> = Some(state.clone());

        let mut iter: usize = 0;
        while t0.elapsed() < budget {
            match self.step(&mut state, iter) {
                Ok(Some(delta)) => {
                    cum_delta += delta;
                    if cum_delta < best_cum {
                        best_cum = cum_delta;
                        best_state = Some(state.clone());
                        debug!(%best_cum, "New best cumulative delta");
                    }
                }
                Ok(None) => {
                    // No accepted move; just continue
                }
                Err(e) => {
                    // Application failed; continue search (state is still valid)
                    warn!(error = %e, "Step failed; continuing.");
                }
            }

            iter += 1;

            // Cheap stop check every 16 iterations to avoid tight-loop overhead
            if (iter & 0xF) == 0 && t0.elapsed() >= budget {
                break;
            }
        }

        let final_state = best_state.unwrap_or(state);
        let final_temp = {
            let a = &self.config.anneal;
            (a.initial_temperature * a.cooling_rate.powi(iter as i32)).max(a.min_temperature)
        };

        info!(
            iterations = iter,
            proposals = self.proposals_made,
            temperature = final_temp,
            "Meta solve finished",
        );

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

    // base scores from speed and success
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
    let t = tau.max(1e-6); // guard
    let exps: Vec<f64> = raw.iter().map(|&v| ((v - maxv) / t).exp()).collect();
    let sum: f64 = exps.iter().sum::<f64>().max(alloc.softmax_eps);

    let mut out: Vec<usize> = exps
        .into_iter()
        .map(|w| (w / sum) * alloc.target_total_proposals_per_round as f64)
        .map(|x| x.round() as usize)
        .map(|a| a.clamp(alloc.min_per_op, alloc.max_per_op))
        .collect();

    // optional: exploration mass (uniform) — simple mix
    if alloc.explore_frac > 0.0 {
        let total: usize = out.iter().sum();
        if total > 0 {
            let explore = ((alloc.explore_frac * alloc.target_total_proposals_per_round as f64)
                .round() as usize)
                .max(n); // at least 1 each
            let base = explore / n;
            for v in &mut out {
                *v = (*v + base).clamp(alloc.min_per_op, alloc.max_per_op);
            }
        }
    }

    out
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

    assert_impl_all!(Q: Send, Sync);
    assert_impl_all!(OperatorRecord<T, C, Q>: Send, Sync);
    assert_impl_all!(MetaEngine<T, C, Q, S>: Send, Sync);
    assert_impl_all!(Plan<'static, T, C>: Send);
    assert_impl_all!(PlanEval<T, C>: Send);
    assert_impl_all!(OperatorStats<C>: Send, Sync);
}
