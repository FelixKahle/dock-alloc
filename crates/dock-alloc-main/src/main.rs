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
// THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

use dock_alloc_model::prelude::*;
use dock_alloc_solver::meta::oplib::{self};
use dock_alloc_solver::{
    berth::quay::BTreeMapQuay,
    framework::state::Solver,
    greedy::GreedySolver,
    meta::{config::MetaConfig, engine::MetaEngine},
};
use tracing_subscriber::{EnvFilter, fmt::format::FmtSpan};

#[allow(dead_code)]
fn enable_tracing() {
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("debug")),
        )
        .with_span_events(FmtSpan::ENTER | FmtSpan::EXIT | FmtSpan::CLOSE)
        .init();
}

fn main() {
    enable_tracing();

    // Generate the Problem
    let mut generator: InstanceGenerator<i64, i64> = InstanceGenConfig::default().into();
    let problem: Problem<i64, i64> = generator.generate();

    // Solve the Problem (greedy)
    let mut greedy: GreedySolver<i64, i64, BTreeMapQuay> = GreedySolver::new();
    let greedy_solution = greedy.solve(&problem).unwrap();

    let greedy: GreedySolver<i64, i64, BTreeMapQuay> = GreedySolver::new();
    let operators = oplib::prelude::op_list::<i64, i64, BTreeMapQuay>(&problem);
    let mut meta: MetaEngine<i64, i64, BTreeMapQuay, GreedySolver<i64, i64, BTreeMapQuay>> =
        MetaEngine::new(MetaConfig::default(), operators, greedy);
    let meta_solution = meta.solve(&problem).unwrap();

    // Make sure the solutions are valid
    greedy_solution.validate().unwrap();
    meta_solution.validate().unwrap();

    println!();
    println!("=================================================================");
    println!("==================== Solution Comparison ========================");
    println!("=================================================================");
    println!();

    println!("Greedy Solution: {}", greedy_solution.stats());
    println!("Meta Solution: {}", meta_solution.stats());
}
