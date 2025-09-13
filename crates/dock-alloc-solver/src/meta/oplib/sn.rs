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
    berth::{overlay::BrandedFreeSlot, quay::QuayRead},
    framework::planning::{Plan, PlanningContext},
    meta::{operator::Operator, oplib::util::req_windows},
};
use dock_alloc_core::{
    SolverVariable,
    cost::Cost,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::TimeInterval,
};
use dock_alloc_model::model::Problem;
use rand_chacha::ChaCha8Rng;
use std::cmp;
use tracing::instrument;

/// Nudge an assignment left in space within a bounded span, keeping time within an adaptive window.
pub struct SpaceNudgeLeftOperator<T, C, Q> {
    pub max_span: SpaceLength,
    pub scan: usize,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for SpaceNudgeLeftOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            max_span: SpaceLength::new(256),
            scan: 64,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> From<&Problem<T, C>> for SpaceNudgeLeftOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(p: &Problem<T, C>) -> Self {
        let s = p.stats();
        let quay_len: SpaceLength = s.quay_length();
        let p50: SpaceLength = s.p50_request_length();
        let p90: SpaceLength = s.p90_request_length();
        let rho: f64 = s.rho();
        let mov: usize = s.movable_count();

        let span_mult = if rho < 0.9 {
            2
        } else if rho < 1.2 {
            3
        } else {
            4
        };
        let base_span = p90 * span_mult;
        let max_span = base_span.clamp(p50, quay_len);

        let rho_scan: usize = if rho < 0.6 {
            24
        } else if rho < 0.9 {
            48
        } else if rho < 1.2 {
            64
        } else {
            96
        };
        let size_scan = 16 + mov / 4;
        let scan = cmp::min(rho_scan, size_scan).clamp(16, 256);

        Self {
            max_span,
            scan,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for SpaceNudgeLeftOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "SpaceNudgeLeft"
    }

    #[instrument(level = "info", skip_all)]
    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        _: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let quay_len: SpaceLength = b.problem().quay_length();
            let quay_span =
                SpaceInterval::new(SpacePosition::zero(), SpacePosition::zero() + quay_len);

            let mut tx = b.begin();

            // pick the right-most movable to nudge left
            let Some(cur) = tx.with_explorer(|ex| {
                ex.iter_movable_assignments()
                    .max_by_key(|m| m.start_position().value())
            }) else {
                return b.build();
            };

            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();
            let old_s = cur.start_position();
            let old_t = cur.start_time();

            // spatial band strictly to the left: [old_s - max_span, old_s)
            let s_min = old_s.saturating_sub(self.max_span);
            let band = SpaceInterval::new(s_min, old_s);
            let s_band = band.intersection(&quay_span).unwrap_or(band);

            // adaptive time band around old_t: ± (p50_proc * f(ρ))
            let stats = tx.problem().stats();
            let mut rad = stats.p50_processing_time(); // TimeDelta<T>
            let mul = if stats.rho() < 0.9 {
                2
            } else if stats.rho() < 1.2 {
                3
            } else {
                4
            };
            for _ in 1..mul {
                rad += stats.p50_processing_time();
            } // cheap multiply
            let arr = req.arrival_time();
            let t_lo = core::cmp::max(arr, old_t - rad);
            let t_hi = old_t + rad;
            if t_lo >= t_hi {
                return b.build();
            }
            let gw = TimeInterval::new(t_lo, t_hi);

            let (t_w, s_w) = req_windows(&req, gw, s_band);

            // greedy best improvement, tie-break by larger left shift
            let mut best: Option<(Cost<C>, usize, BrandedFreeSlot<'_, T>)> = None;
            tx.with_explorer(|ex| {
                for s in ex
                    .iter_slots_for_request_within(&req, t_w, s_w)
                    .take(self.scan)
                {
                    let sp = s.slot().space().start();
                    if sp == old_s {
                        continue;
                    } // must actually move
                    if sp > old_s {
                        continue;
                    } // enforce left nudge

                    let t = s.slot().start_time();
                    let hyp = dock_alloc_model::model::AssignmentRef::new(req.request(), sp, t);
                    let d = hyp.cost() - old_cost;
                    if d.value() < C::zero() {
                        let dist = old_s.value().saturating_sub(sp.value()); // larger is better for left
                        if best
                            .as_ref()
                            .is_none_or(|(bd, bdist, _)| d < *bd || (d == *bd && dist > *bdist))
                        {
                            best = Some((d, dist, s));
                        }
                    }
                }
            });

            let Some((_d, _dist, slot)) = best else {
                return b.build();
            };

            if tx.propose_unassign(&cur).is_err() {
                return b.build();
            }
            if tx.propose_assign(&req, slot).is_err() {
                return b.build();
            }
            if tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}

/// Nudge an assignment right in space within a bounded span, keeping time within an adaptive window.
pub struct SpaceNudgeRightOperator<T, C, Q> {
    pub max_span: SpaceLength,
    pub scan: usize,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for SpaceNudgeRightOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            max_span: SpaceLength::new(256),
            scan: 64,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> From<&Problem<T, C>> for SpaceNudgeRightOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn from(p: &Problem<T, C>) -> Self {
        let s = p.stats();
        let quay_len: SpaceLength = s.quay_length();
        let p50: SpaceLength = s.p50_request_length();
        let p90: SpaceLength = s.p90_request_length();
        let rho: f64 = s.rho();
        let mov: usize = s.movable_count();

        let span_mult = if rho < 0.9 {
            2
        } else if rho < 1.2 {
            3
        } else {
            4
        };
        let base_span = p90 * span_mult;
        let max_span = base_span.clamp(p50, quay_len);

        let rho_scan: usize = if rho < 0.6 {
            24
        } else if rho < 0.9 {
            48
        } else if rho < 1.2 {
            64
        } else {
            96
        };
        let size_scan = 16 + mov / 4;
        let scan = cmp::min(rho_scan, size_scan).clamp(16, 256);

        Self {
            max_span,
            scan,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for SpaceNudgeRightOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "SpaceNudgeRight"
    }

    #[instrument(level = "info", skip_all)]
    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        _: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let quay_len: SpaceLength = b.problem().quay_length();
            let quay_span =
                SpaceInterval::new(SpacePosition::zero(), SpacePosition::zero() + quay_len);

            let mut tx = b.begin();

            // pick the left-most movable to nudge right
            let Some(cur) = tx.with_explorer(|ex| {
                ex.iter_movable_assignments()
                    .min_by_key(|m| m.start_position().value())
            }) else {
                return b.build();
            };

            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();
            let old_s = cur.start_position();
            let old_t = cur.start_time();

            // spatial band strictly to the right: (old_s, old_s + max_span]
            let s_max = old_s + self.max_span;
            let band = SpaceInterval::new(old_s, s_max);
            let s_band = band.intersection(&quay_span).unwrap_or(band);

            // adaptive time band around old_t: ± (p50_proc * f(ρ))
            let stats = tx.problem().stats();
            let mut rad = stats.p50_processing_time();
            let mul = if stats.rho() < 0.9 {
                2
            } else if stats.rho() < 1.2 {
                3
            } else {
                4
            };
            for _ in 1..mul {
                rad += stats.p50_processing_time();
            }
            let arr = req.arrival_time();
            let t_lo = core::cmp::max(arr, old_t - rad);
            let t_hi = old_t + rad;
            if t_lo >= t_hi {
                return b.build();
            }
            let gw = TimeInterval::new(t_lo, t_hi);

            let (t_w, s_w) = req_windows(&req, gw, s_band);

            // greedy best improvement, tie-break by larger right shift
            let mut best: Option<(Cost<C>, usize, BrandedFreeSlot<'_, T>)> = None;
            tx.with_explorer(|ex| {
                for s in ex
                    .iter_slots_for_request_within(&req, t_w, s_w)
                    .take(self.scan)
                {
                    let sp = s.slot().space().start();
                    if sp == old_s {
                        continue;
                    }
                    if sp < old_s {
                        continue;
                    } // enforce right nudge

                    let t = s.slot().start_time();
                    let hyp = dock_alloc_model::model::AssignmentRef::new(req.request(), sp, t);
                    let d = hyp.cost() - old_cost;
                    if d.value() < C::zero() {
                        let dist = sp.value().saturating_sub(old_s.value()); // larger is better for right
                        if best
                            .as_ref()
                            .is_none_or(|(bd, bdist, _)| d < *bd || (d == *bd && dist > *bdist))
                        {
                            best = Some((d, dist, s));
                        }
                    }
                }
            });

            let Some((_d, _dist, slot)) = best else {
                return b.build();
            };

            if tx.propose_unassign(&cur).is_err() {
                return b.build();
            }
            if tx.propose_assign(&req, slot).is_err() {
                return b.build();
            }
            if tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}
