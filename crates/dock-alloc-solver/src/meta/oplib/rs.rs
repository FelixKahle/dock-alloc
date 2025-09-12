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
    berth::quay::QuayRead,
    framework::planning::{Plan, PlanningContext},
    meta::{operator::Operator, oplib::util::pick_two_random_asgs},
};
use dock_alloc_core::{SolverVariable, time::TimeDelta};
use dock_alloc_model::model::Problem;
use num_traits::FromPrimitive;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

pub struct RandomSwapOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    /// How many random pairs to try before giving up.
    pub attempts: usize,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for RandomSwapOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            attempts: 8,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> From<&Problem<T, C>> for RandomSwapOperator<T, C, Q>
where
    T: dock_alloc_core::SolverVariable + FromPrimitive,
    C: dock_alloc_core::SolverVariable,
    Q: crate::berth::quay::QuayRead,
{
    fn from(problem: &Problem<T, C>) -> Self {
        let s = problem.stats();
        let mov = s.movable_count().max(1);
        let rho = s.rho();

        let p50_len = s.p50_request_length();
        let p90_len = s.p90_request_length();
        let p50_proc = s.p50_processing_time();
        let p90_proc =
            { TimeDelta::new(p50_proc.value() * T::from_usize(2).unwrap_or_else(T::one)) };

        // --- Base: O(log n) with a small size-aware bump
        let base = (mov.ilog2() as usize) + 4;
        let size_bump = (mov / 64).min(8); // grows slowly with instance size
        let mut attempts = base + size_bump;

        // --- Congestion scaling (ρ ∈ [0, 2] in your stats)
        // multiplier in ~[1.0, 2.0]
        let cong_mult = 1.0 + 0.50 * rho;
        attempts = ((attempts as f64) * cong_mult).round() as usize;

        // --- Heterogeneity bumps (typed comparisons; no scalar extraction)
        // Length diversity
        if p90_len >= p50_len * 2 {
            attempts += 2;
        }
        if p90_len >= p50_len * 3 {
            attempts += 2;
        } // strongly diverse lengths

        // Processing-time diversity
        if p90_proc >= p50_proc * T::from_usize(2).unwrap_or_else(T::one) {
            attempts += 2;
        }
        if p90_proc >= p50_proc * T::from_usize(3).unwrap_or_else(T::one) {
            attempts += 2;
        }

        // --- Final clamp with a size-aware ceiling
        let ceiling = (8 + (mov.ilog2() as usize) * 8).clamp(24, 96);
        let floor = 6;
        attempts = attempts.clamp(floor, ceiling);

        Self {
            attempts,
            ..Self::default()
        }
    }
}

impl<T, C, Q> Operator for RandomSwapOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "RandomSwap"
    }

    #[instrument(level = "info", skip_all, name = "RandomSwap")]
    fn propose<'p, 'al, 'bo>(
        &self,
        _iteration: usize,
        rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            // quick check without a txn (read-only, no borrow hazard)
            let n = b.with_explorer(|ex| ex.iter_movable_assignments().count());
            if n < 2 {
                return b.build();
            }

            for _ in 0..self.attempts {
                // fresh txn per attempt; if we don't call commit(), changes are discarded
                let mut tx = b.begin();

                // pick a pair from the child overlay view
                let pair = tx.with_explorer(|ex| pick_two_random_asgs(ex, rng));
                let Some((a, bmv)) = pair else {
                    continue; // nothing to try in this attempt
                };

                let req_a = a.branded_request();
                let req_b = bmv.branded_request();

                // identical footprint
                if req_a.length() != req_b.length()
                    || req_a.processing_duration() != req_b.processing_duration()
                {
                    continue;
                }

                let a_t = a.start_time();
                let a_s = a.start_position();
                let b_t = bmv.start_time();
                let b_s = bmv.start_position();

                // arrivals & windows
                if b_t < req_a.arrival_time() || a_t < req_b.arrival_time() {
                    continue;
                }
                let len = req_a.length();
                let a_win = req_a.feasible_space_window();
                let b_win = req_b.feasible_space_window();
                let a_ok = a_win.contains(b_s) && a_win.end() >= b_s + len;
                let b_ok = b_win.contains(a_s) && b_win.end() >= a_s + len;
                if !(a_ok && b_ok) {
                    continue;
                }

                // quick improvement gate
                let old_cost = a.assignment().cost() + bmv.assignment().cost();
                let a_if_at_b =
                    dock_alloc_model::model::AssignmentRef::new(req_a.request(), b_s, b_t);
                let b_if_at_a =
                    dock_alloc_model::model::AssignmentRef::new(req_b.request(), a_s, a_t);
                if a_if_at_b.cost() + b_if_at_a.cost() >= old_cost {
                    continue;
                }

                // do the swap inside the txn; failures just cause this attempt to be discarded
                let reg_a = match tx.propose_unassign(&a) {
                    Ok(r) => r,
                    Err(_) => continue,
                };
                let reg_b = match tx.propose_unassign(&bmv) {
                    Ok(r) => r,
                    Err(_) => continue,
                };

                if tx.propose_assign_at(&req_a, &reg_b, b_t, b_s).is_err() {
                    continue;
                }
                if tx.propose_assign_at(&req_b, &reg_a, a_t, a_s).is_err() {
                    continue;
                }

                // full-assignment check
                let fully_assigned =
                    tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none());
                if !fully_assigned {
                    continue;
                }

                // success → merge into parent overlays
                tx.commit();
                return b.build();
            }

            // no improving swap found
            b.build()
        })
    }
}
