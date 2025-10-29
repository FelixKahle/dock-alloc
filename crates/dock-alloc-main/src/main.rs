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

use dock_alloc_core::space::SpaceLength;
use dock_alloc_model::prelude::*;
use dock_alloc_solver::meta::oplib::{self};
use dock_alloc_solver::{
    berth::quay::BTreeMapQuay,
    framework::state::Solver,
    greedy::GreedySolver,
    meta::{config::MetaConfig, engine::MetaEngine},
};
use serde::Serialize;
use std::{fs::File, io::BufWriter, time::Instant};
use tracing_subscriber::{EnvFilter, fmt::format::FmtSpan};

#[allow(dead_code)]
fn enable_tracing() {
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info")),
        )
        .with_span_events(FmtSpan::ENTER | FmtSpan::EXIT | FmtSpan::CLOSE)
        .init();
}

#[derive(Debug, Clone, Serialize)]
struct InstanceInfo {
    idx: usize,
    seed: u64,
    quay_length: usize,
    movable_count: usize,
    fixed_count: usize,
    horizon: i64,
    space_window_policy: String,
    // Problem stats snapshot
    stats_quay_length: usize,
    stats_movable_count: usize,
    stats_p50_request_length: usize,
    stats_p90_request_length: usize,
    stats_p50_processing_time: i64,
    stats_latest_completion_time: i64,
    stats_rho: f64,
}

#[derive(Debug, Clone, Serialize)]
struct RunResult {
    instance: InstanceInfo,
    greedy_initial_cost: i64,
    greedy_elapsed_ms: u128,
    meta_final_cost: i64,
    meta_elapsed_ms: u128,
}

#[derive(Debug, Clone, Serialize)]
struct BenchmarkReport {
    description: String,
    instances: Vec<RunResult>,
}

fn interpolate_u(val0: usize, val1: usize, step: usize, steps: usize) -> usize {
    if steps <= 1 {
        return val1;
    }
    let num = (val1 as isize - val0 as isize) * step as isize;
    (val0 as isize + num / (steps as isize - 1)).max(0) as usize
}

fn main() {
    enable_tracing();

    // Baseline (for defaults we don't vary)
    type Tm = i64;
    type Cm = i64;

    let default_cfg: InstanceGenConfig<Tm, Cm> = InstanceGenConfig::default();

    // Define a ramp from small -> big across 10 instances
    let n_instances = 10usize;

    // You can tune these ranges if desired
    let min_quay_len = 500usize;
    let max_quay_len = 2000usize;

    let min_movables = 20usize;
    let max_movables = 200usize;

    let min_fixed = 10usize;
    let max_fixed = 120usize;

    // Keep default horizon; still record it
    let horizon_default = default_cfg.horizon().value();

    // Mirror the default space window policy in the builder
    let swp_default = default_cfg.space_window_policy().clone();
    let min_len = default_cfg.min_length();
    let max_len = default_cfg.max_length();

    // Prepare results
    let mut results: Vec<RunResult> = Vec::with_capacity(n_instances);

    for i in 0..n_instances {
        // Scale instance size
        let quay_length = interpolate_u(min_quay_len, max_quay_len, i, n_instances);
        let amt_mov = interpolate_u(min_movables, max_movables, i, n_instances);
        let amt_fix = interpolate_u(min_fixed, max_fixed, i, n_instances);

        // Deterministic seed per instance
        let seed: u64 = 42 + (i as u64);

        // Configure builder
        let mut builder = InstanceGenConfigBuilder::<Tm, Cm>::new()
            .quay_length(SpaceLength::new(quay_length))
            .min_length(min_len)
            .max_length(max_len)
            .horizon(dock_alloc_core::time::TimePoint::new(horizon_default))
            .amount_movables(amt_mov)
            .amount_fixed(amt_fix)
            .seed(seed);

        // Reapply the default space window policy using the builder
        builder = match swp_default.clone() {
            SpaceWindowPolicy::FullQuay => builder.space_policy_full_quay(),
            SpaceWindowPolicy::Halfwidth(HalfwidthPolicy::Fixed(hw)) => {
                builder.space_policy_fixed(hw)
            }
            SpaceWindowPolicy::Halfwidth(HalfwidthPolicy::Relative(rp)) => {
                builder.space_policy_relative(rp.frac_of_length, rp.min, rp.max)
            }
        };

        let cfg = builder.build().expect("valid instance config");
        let mut generator: InstanceGenerator<Tm, Cm> = cfg.into();
        let problem: Problem<Tm, Cm> = generator.generate();

        // Greedy initial solution
        let mut greedy: GreedySolver<Tm, Cm, BTreeMapQuay> = GreedySolver::new();
        let t0 = Instant::now();
        let greedy_solution = greedy.solve(&problem).expect("greedy solution");
        let greedy_elapsed = t0.elapsed();
        greedy_solution.validate().expect("valid greedy solution");

        // Operators and Meta solver (60s budget)
        let operators = oplib::prelude::op_list::<Tm, Cm, BTreeMapQuay>(&problem);
        let greedy_ctor: GreedySolver<Tm, Cm, BTreeMapQuay> = GreedySolver::new();
        let mut meta: MetaEngine<Tm, Cm, BTreeMapQuay, GreedySolver<Tm, Cm, BTreeMapQuay>> =
            MetaEngine::new(
                MetaConfig {
                    max_solver_time_ms: 60_000, // 60 seconds
                    ..MetaConfig::default()
                },
                operators,
                greedy_ctor,
            );

        let t1 = Instant::now();
        let meta_solution = meta.solve(&problem).expect("meta solution");
        let meta_elapsed = t1.elapsed();
        meta_solution.validate().expect("valid meta solution");

        // Collect stats
        let pstats = problem.stats();
        let inst_info = InstanceInfo {
            idx: i,
            seed,
            quay_length,
            movable_count: amt_mov,
            fixed_count: amt_fix,
            horizon: horizon_default,
            space_window_policy: format!("{}", swp_default),
            stats_quay_length: pstats.quay_length().value(),
            stats_movable_count: pstats.movable_count(),
            stats_p50_request_length: pstats.p50_request_length().value(),
            stats_p90_request_length: pstats.p90_request_length().value(),
            stats_p50_processing_time: pstats.p50_processing_time().value(),
            stats_latest_completion_time: pstats.latest_completion_time().value(),
            stats_rho: pstats.rho(),
        };

        let greedy_initial_cost = greedy_solution.stats().total_cost().value();
        let meta_final_cost = meta_solution.stats().total_cost().value();

        results.push(RunResult {
            instance: inst_info,
            greedy_initial_cost,
            greedy_elapsed_ms: greedy_elapsed.as_millis(),
            meta_final_cost,
            meta_elapsed_ms: meta_elapsed.as_millis(),
        });
    }

    // Serialize to JSON
    let report = BenchmarkReport {
        description: "Dock allocation benchmark: 10 instances from small to big; greedy initial cost vs meta (60s) final cost.".into(),
        instances: results,
    };

    let file = File::create("bench_results.json").expect("create bench_results.json");
    let mut writer = BufWriter::new(file);
    serde_json::to_writer_pretty(&mut writer, &report).expect("write json report");

    // Also print a short summary to stdout
    println!();
    println!("=================================================================");
    println!("======================== Benchmark Done =========================");
    println!("=================================================================");
    println!();
    println!("Wrote: bench_results.json");
}
