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
    meta::{config::MetaConfig, operator::Operator},
};
use dock_alloc_core::{SolverVariable, cost::Cost};
use dock_alloc_model::prelude::*;
use num_traits::Zero;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use rand_distr::{Distribution, weighted::WeightedIndex};
use rayon::prelude::*;
use std::{
    fmt::{Debug, Display},
    sync::Arc,
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

/// Small wrapper to encapsulate operator records & stats plumbing.
pub struct OperatorPool<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    records: Vec<OperatorRecord<T, C, Q>>,
}

impl<T, C, Q> OperatorPool<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn new(records: Vec<OperatorRecord<T, C, Q>>) -> Self {
        Self { records }
    }

    #[inline]
    fn len(&self) -> usize {
        self.records.len()
    }

    #[inline]
    fn get(&self, i: usize) -> &OperatorRecord<T, C, Q> {
        &self.records[i]
    }

    #[inline]
    fn get_mut(&mut self, i: usize) -> &mut OperatorRecord<T, C, Q> {
        &mut self.records[i]
    }

    #[inline]
    pub fn records(&self) -> &[OperatorRecord<T, C, Q>] {
        &self.records
    }

    /// Compute raw (speed, success) score for index `i` (no temperature/exploration yet).
    #[inline]
    fn raw_score_at(
        &self,
        i: usize,
        alloc: &crate::meta::config::AllocationConfig,
        stats: &crate::meta::config::StatsConfig,
    ) -> f64 {
        let s = &self.records[i].stats;
        let ns_per = (s.emwa_gen_ns_per_proposal + s.emwa_eval_ns_per_proposal)
            .max(stats.min_ns_per_proposal);
        let speed = 1.0 / ns_per;
        let succ = if s.attempts > 0 {
            s.accepted as f64 / s.attempts as f64
        } else {
            stats.bootstrap_success_rate
        };
        alloc.speed_weight * speed + alloc.success_weight * succ
    }

    fn apply_aggregates(&mut self, aggs: &[OpAgg], stats_cfg: &crate::meta::config::StatsConfig) {
        for (i, a) in aggs.iter().enumerate() {
            if a.attempts == 0 {
                continue;
            }
            let st = &mut self.records[i].stats;
            st.attempts += a.attempts;
            if a.gen_ns_count > 0 || a.eval_ns_count > 0 {
                let gene = if a.gen_ns_count > 0 {
                    a.gen_ns_sum / a.gen_ns_count as f64
                } else {
                    0.0
                };
                let eval = if a.eval_ns_count > 0 {
                    a.eval_ns_sum / a.eval_ns_count as f64
                } else {
                    0.0
                };
                st.on_timing(
                    gene,
                    eval,
                    stats_cfg.gen_time_alpha,
                    stats_cfg.eval_time_alpha,
                );
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
struct OpAgg {
    attempts: u64,
    gen_ns_sum: f64,
    eval_ns_sum: f64,
    gen_ns_count: u64,
    eval_ns_count: u64,
}

impl OpAgg {
    #[inline]
    fn add_attempt(&mut self) {
        self.attempts += 1;
    }
    #[inline]
    fn add_timing(&mut self, gen_ns: f64, eval_ns: f64) {
        if gen_ns > 0.0 {
            self.gen_ns_sum += gen_ns;
            self.gen_ns_count += 1;
        }
        if eval_ns > 0.0 {
            self.eval_ns_sum += eval_ns;
            self.eval_ns_count += 1;
        }
    }
}

struct ThreadAccum<'p, T: SolverVariable, C: SolverVariable> {
    candidate: Option<Candidate<'p, T, C>>,
    per_op: Vec<OpAgg>,
}

impl<'p, T: SolverVariable, C: SolverVariable> ThreadAccum<'p, T, C> {
    #[inline]
    fn empty(n_ops: usize) -> Self {
        Self {
            candidate: None,
            per_op: vec![OpAgg::default(); n_ops],
        }
    }

    #[inline]
    fn merge(mut self, mut other: Self, temp: f64) -> Self {
        for (i, o) in other.per_op.iter_mut().enumerate() {
            let s = &mut self.per_op[i];
            s.attempts += o.attempts;
            s.gen_ns_sum += o.gen_ns_sum;
            s.eval_ns_sum += o.eval_ns_sum;
            s.gen_ns_count += o.gen_ns_count;
            s.eval_ns_count += o.eval_ns_count;
        }
        self.candidate = choose_sa(self.candidate, other.candidate, temp);
        self
    }
}

#[inline]
fn choose_sa<'p, T: SolverVariable, C: SolverVariable>(
    a: Option<Candidate<'p, T, C>>,
    b: Option<Candidate<'p, T, C>>,
    temp: f64,
) -> Option<Candidate<'p, T, C>> {
    match (a, b) {
        (None, None) => None,
        (Some(x), None) | (None, Some(x)) => Some(x),
        (Some(x), Some(y)) => {
            let d = y.delta - x.delta;
            let p = acceptance_prob(d, temp);
            if p > 0.0 && rand::random::<f64>() < p {
                Some(y)
            } else {
                Some(x)
            }
        }
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
    operator_pool: OperatorPool<T, C, Q>,
    construction_solver: S,
    proposals_made: u64,
    weights_buf: Vec<f64>,
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
fn make_job_rng(base_seed: u64, j: usize) -> ChaCha8Rng {
    let s = base_seed ^ ((j as u64).rotate_left(17)) ^ 0x9E37_79B1_85EB_CA87u64;
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
        let records = ops.into_iter().map(|op| OperatorRecord::new(op)).collect();
        Self {
            config,
            operator_pool: OperatorPool::new(records),
            construction_solver,
            proposals_made: 0,
            weights_buf: Vec::new(),
        }
    }

    #[inline]
    pub fn construction_solver(&self) -> &S {
        &self.construction_solver
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

        let n_ops = self.operator_pool.len();
        if n_ops == 0 {
            trace!("No operators available.");
            return Ok(None);
        }

        if self.weights_buf.len() != n_ops {
            self.weights_buf.resize(n_ops, 0.0);
        }

        let mut maxv = f64::NEG_INFINITY;
        for i in 0..n_ops {
            let s = self.operator_pool.raw_score_at(i, alloc_cfg, stats_cfg);
            if s > maxv {
                maxv = s;
            }
            self.weights_buf[i] = s;
        }

        let t = tau.max(1e-6);
        for w in &mut self.weights_buf {
            *w = ((*w - maxv) / t).exp();
        }

        if alloc_cfg.explore_frac > 0.0 {
            // average of current (softmaxed) weights
            let mut sum = 0.0;
            for &w in &self.weights_buf {
                sum += w;
            }
            // guard against pathological zero sum
            let avg = if sum > 0.0 {
                sum / n_ops as f64
            } else {
                1.0 / n_ops as f64
            };
            let e = alloc_cfg.explore_frac;
            for w in &mut self.weights_buf {
                *w = (1.0 - e) * *w + e * avg;
            }
        }

        let dist = Arc::new(
            WeightedIndex::new(self.weights_buf.iter().cloned())
                .expect("weights must be non-negative and finite"),
        );

        let total_draws = usize::max(
            n_ops,
            self.config.alloc.target_total_proposals_per_round,
        );

        let base_seed = rng_cfg.seed_base_task ^ (iteration as u64);

        let reduced = (0..total_draws)
            .into_par_iter()
            .fold(
                || ThreadAccum::empty(n_ops), // one per worker
                |mut acc, j| {
                    let mut rng = make_job_rng(base_seed, j);
                    let op_idx = dist.sample(&mut rng);

                    let ctx = PlanningContext::new(ledger, berth, problem);
                    let t0 = Instant::now();
                    let plan = self
                        .operator_pool
                        .get(op_idx)
                        .operator()
                        .propose(iteration, &mut rng, ctx);
                    let gen_ns = t0.elapsed().as_nanos() as f64;

                    // Count attempt *always*, even if no-op
                    acc.per_op[op_idx].add_attempt();

                    if plan.ledger_commit().operations().is_empty() {
                        return acc; // nothing else to do
                    }

                    let t1 = Instant::now();
                    let delta = plan.eval().delta_cost();
                    let eval_ns = t1.elapsed().as_nanos() as f64;

                    // Fold timing into aggregates
                    acc.per_op[op_idx].add_timing(gen_ns, eval_ns);

                    // Maintain a per-worker candidate using SA reduction semantics
                    let cand = Candidate {
                        op_idx,
                        plan,
                        delta,
                    };
                    acc.candidate = choose_sa(acc.candidate, Some(cand), temp);
                    acc
                },
            )
            .reduce(|| ThreadAccum::empty(n_ops), |a, b| a.merge(b, temp));

        // If nothing useful was produced
        if reduced.per_op.iter().all(|agg| agg.attempts == 0) {
            trace!("All generated plans were no-ops; nothing to apply.");
            return Ok(None);
        }

        // Update per-operator attempts & timings (EWMA) once
        self.operator_pool
            .apply_aggregates(&reduced.per_op, stats_cfg);

        // Track proposals count accurately
        let mut attempts_sum: u64 = 0;
        for a in &reduced.per_op {
            attempts_sum += a.attempts;
        }
        self.proposals_made = self.proposals_made.saturating_add(attempts_sum);

        // Apply winner if present
        let Some(winner) = reduced.candidate else {
            trace!("No candidate survived the reduction.");
            return Ok(None);
        };

        let winner_op_name = self.operator_pool.get(winner.op_idx).operator().name();

        info!(
            op_index = winner.op_idx,
            op = winner_op_name,
            %temp,
            %tau,
            delta = %winner.delta,
            "Selected winner"
        );

        match state.apply_plan_validated(&winner.plan) {
            Ok(()) => {
                // Reward the winning operator
                let rec = self.operator_pool.get_mut(winner.op_idx);
                rec.stats_mut()
                    .on_accept(winner.delta, stats_cfg.reward_alpha);
                trace!("Applied plan successfully.");
                Ok(Some(winner.delta))
            }
            Err(e) => {
                warn!(error = %e, op = winner_op_name, "Plan application failed; skipping.");
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
                Ok(None) => {}
                Err(e) => {
                    warn!(error = %e, "Step failed; continuing.");
                }
            }

            iter += 1;

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
