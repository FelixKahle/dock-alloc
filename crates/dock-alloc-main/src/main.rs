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

use dock_alloc_model::{
    generator::{InstanceGenConfig, InstanceGenerator},
    model::Problem,
};
use dock_alloc_solver::{
    berth::quay::BTreeMapQuay, framework::state::Solver, greedy::GreedySolver,
};

fn main() {
    // Generate the Problem
    let mut generator: InstanceGenerator<i64, i64> = InstanceGenConfig::default().into();
    let problem: Problem<i64, i64> = generator.generate();
    println!("{}", problem);

    // Solve the Problem
    let mut greedy: GreedySolver<i64, i64, BTreeMapQuay> = GreedySolver::new();
    let solution = greedy.solve(&problem).unwrap();
    println!("Solution: {}", solution);
}
