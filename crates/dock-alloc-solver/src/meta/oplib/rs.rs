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
    meta::operator::Operator,
};
use dock_alloc_core::SolverVariable;
use dock_alloc_model::model::Problem;
use rand::Rng;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

pub struct RandomSwapOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    /// How many pair attempts per propose().
    pub attempts: usize,
    /// Tournament size for picking A (higher biases toward costly assignments).
    pub tournament_a: usize,
    /// Number of B candidates to evaluate for each A.
    pub candidates_b: usize,
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
            tournament_a: 6,
            candidates_b: 10,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> From<&Problem<T, C>> for RandomSwapOperator<T, C, Q>
where
    T: dock_alloc_core::SolverVariable,
    C: dock_alloc_core::SolverVariable,
    Q: crate::berth::quay::QuayRead,
{
    fn from(problem: &Problem<T, C>) -> Self {
        let s = problem.stats();
        let mov = s.movable_count().max(1);
        let rho = s.rho();

        // attempts ~ O(log n) * f(ρ)
        let mut attempts = (mov.ilog2() as usize + 4) as f64;
        attempts *= 1.0 + 0.50 * rho; // ρ∈[0,2] ⇒ ×[1.0 .. 2.0]
        // size-aware ceiling
        let ceil = (8 + (mov.ilog2() as usize) * 8).clamp(24, 128);
        let attempts = {
            let raw = attempts.round() as usize;
            core::cmp::min(ceil, core::cmp::max(6, raw))
        };

        // tournament for A: small but grows a bit with ρ and size
        let mut tour_a = 4.0 + (mov.ilog2() as f64) * 0.5;
        tour_a *= 1.0 + 0.25 * rho;
        let tournament_a = {
            let raw = tour_a.round() as usize;
            raw.clamp(3, 16)
        };

        // candidates for B: a handful, slightly more when congested
        let mut cand_b = 6.0 + (mov.ilog2() as f64) * 0.8;
        cand_b *= 1.0 + 0.35 * rho;
        let candidates_b = {
            let raw = cand_b.round() as usize;
            raw.clamp(6, 24)
        };

        Self {
            attempts,
            tournament_a,
            candidates_b,
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
            // quick check
            let n = b.with_explorer(|ex| ex.iter_movable_assignments().count());
            if n < 2 {
                return b.build();
            }

            for _ in 0..self.attempts {
                let mut tx = b.begin();

                // --- pick A via tournament selection over costs
                let n_a = tx.with_explorer(|ex| ex.iter_movable_assignments().count());
                if n_a < 2 {
                    continue;
                }

                let k = core::cmp::min(self.tournament_a, n_a);
                let mut best_a = None;
                tx.with_explorer(|ex| {
                    // sample k indices
                    for _ in 0..k {
                        let idx = rng.random_range(0..n_a);
                        if let Some(m) = ex.iter_movable_assignments().nth(idx) {
                            let cost = m.assignment().cost();
                            if best_a.as_ref().is_none_or(|(c, _)| cost > *c) {
                                best_a = Some((cost, m));
                            }
                        }
                    }
                });
                let Some((_a_cost, a)) = best_a else {
                    continue;
                };
                let req_a = a.branded_request();
                let a_t = a.start_time();
                let a_s = a.start_position();

                // --- pick the best B among a small random set, by direct delta
                let n_b = tx.with_explorer(|ex| ex.iter_movable_assignments().count());
                if n_b < 2 {
                    continue;
                }

                let mut best_pair = None; // (delta, b_mv)
                tx.with_explorer(|ex| {
                    let mut tried = 0usize;
                    while tried < self.candidates_b {
                        let idx = rng.random_range(0..n_b);
                        if let Some(bm) = ex.iter_movable_assignments().nth(idx) {
                            if bm.branded_request().id() == req_a.id() {
                                continue;
                            }
                            tried += 1;

                            // quick arrival/window guards for A→(b_s,b_t) and B→(a_s,a_t)
                            let req_b = bm.branded_request();
                            let b_t = bm.start_time();
                            let b_s = bm.start_position();

                            // arrival
                            if b_t < req_a.arrival_time() || a_t < req_b.arrival_time() {
                                continue;
                            }
                            // space window (start + length inside window)
                            let len_a = req_a.length();
                            let len_b = req_b.length();
                            let a_ok = {
                                let w = req_a.feasible_space_window();
                                w.contains(b_s) && w.end() >= b_s + len_a
                            };
                            let b_ok = {
                                let w = req_b.feasible_space_window();
                                w.contains(a_s) && w.end() >= a_s + len_b
                            };
                            if !(a_ok && b_ok) {
                                continue;
                            }

                            // evaluate cost delta
                            let old = a.assignment().cost() + bm.assignment().cost();
                            let a_if_at_b = dock_alloc_model::model::AssignmentRef::new(
                                req_a.request(),
                                b_s,
                                b_t,
                            );
                            let b_if_at_a = dock_alloc_model::model::AssignmentRef::new(
                                req_b.request(),
                                a_s,
                                a_t,
                            );
                            let new = a_if_at_b.cost() + b_if_at_a.cost();
                            let delta = new - old;
                            if delta.value() < C::zero()
                                && best_pair.as_ref().is_none_or(|(d, _)| delta < *d)
                            {
                                best_pair = Some((delta, bm));
                            }
                        }
                    }
                });

                let Some((_delta, bmv)) = best_pair else {
                    continue;
                };

                // --- perform the swap
                let a_t = a.start_time();
                let a_s = a.start_position();
                let b_t = bmv.start_time();
                let b_s = bmv.start_position();
                let req_a = a.branded_request();
                let req_b = bmv.branded_request();

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
                let full = tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none());
                if !full {
                    continue;
                }

                tx.commit();
                return b.build();
            }

            b.build()
        })
    }
}
