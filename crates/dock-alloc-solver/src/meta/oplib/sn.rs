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

use std::cmp;

use crate::{
    berth::{overlay::BrandedFreeSlot, quay::QuayRead},
    framework::planning::{Plan, PlanningContext},
    meta::{operator::Operator, oplib::util::req_windows},
};
use dock_alloc_core::{
    SolverVariable,
    cost::Cost,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimeInterval, TimePoint},
};
use dock_alloc_model::model::Problem;
use rand_chacha::ChaCha8Rng;
use tracing::instrument;

/// Nudge an assignment left in space within a bounded span, keeping time within a tight window.
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
        let mov: usize = p.movable_count();

        // Base span: start from ~2×p90; increase when congested, but never exceed quay length.
        let span_mult = if rho < 0.9 {
            2
        } else if rho < 1.2 {
            3
        } else {
            4
        };
        let base_span = p90 * span_mult;
        let max_span = base_span.clamp(p50, quay_len);

        // Scan budget: modest when light, deeper when medium/heavy; lightly scale with instance size.
        let rho_scan: usize = if rho < 0.6 {
            24
        } else if rho < 0.9 {
            48
        } else if rho < 1.2 {
            64
        } else {
            96
        };
        // Add a small size-aware component; clamp to a sane range.
        let size_scan = 16 + mov / 4; // grows slowly with instance size
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
            let quay_span: SpaceInterval =
                SpaceInterval::new(SpacePosition::zero(), SpacePosition::zero() + quay_len);

            let mut tx = b.begin();
            let Some(cur) = tx.with_explorer(|ex| ex.iter_movable_assignments().next()) else {
                return b.build();
            };

            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();
            let old_s: SpacePosition = cur.start_position();

            // left band [old_s - max_span, old_s]
            let s_min = old_s.saturating_sub(self.max_span);
            let band = SpaceInterval::new(s_min, old_s);

            // tight time band [arrival, arrival + 24h)
            let arr: TimePoint<T> = req.arrival_time();
            let day = TimeDelta::new(T::from(24 * 3600).unwrap_or_else(T::zero));
            let gw = TimeInterval::new(arr, arr + day);

            // clamp spatial band to quay span
            let s_band = band.intersection(&quay_span).unwrap_or(band);

            let (t_w, s_w) = req_windows(&req, gw, s_band);

            // greedy best improvement within windows
            let mut best: Option<(Cost<C>, BrandedFreeSlot<'_, T>)> = None;
            tx.with_explorer(|ex| {
                for s in ex
                    .iter_slots_for_request_within(&req, t_w, s_w)
                    .take(self.scan)
                {
                    let t = s.slot().start_time();
                    let sp = s.slot().space().start();
                    let hyp = dock_alloc_model::model::AssignmentRef::new(req.request(), sp, t);
                    let d = hyp.cost() - old_cost;
                    if d.value() < C::zero() && best.as_ref().is_none_or(|(bd, _)| d < *bd) {
                        best = Some((d, s));
                    }
                }
            });

            let Some((_d, slot)) = best else {
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

/// Nudge an assignment right in space within a bounded span, keeping time within a tight window.
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
        // Mirror the Left heuristic; keep symmetry unless you intentionally want asymmetry.
        let s = p.stats();
        let quay_len: SpaceLength = s.quay_length();
        let p50: SpaceLength = s.p50_request_length();
        let p90: SpaceLength = s.p90_request_length();
        let rho: f64 = s.rho();
        let mov: usize = p.movable_count();

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
            let quay_span: SpaceInterval =
                SpaceInterval::new(SpacePosition::zero(), SpacePosition::zero() + quay_len);

            let mut tx = b.begin();
            let Some(cur) = tx.with_explorer(|ex| ex.iter_movable_assignments().next()) else {
                return b.build();
            };

            let req = cur.branded_request();
            let old_cost = cur.assignment().cost();
            let old_s: SpacePosition = cur.start_position();

            // right band [old_s, old_s + max_span]
            let s_max = old_s + self.max_span;
            let band = SpaceInterval::new(old_s, s_max);

            // tight time band [arrival, arrival + 24h)
            let arr: TimePoint<T> = req.arrival_time();
            let day = TimeDelta::new(T::from(24 * 3600).unwrap_or_else(T::zero));
            let gw = TimeInterval::new(arr, arr + day);

            // clamp spatial band to quay span
            let s_band = band.intersection(&quay_span).unwrap_or(band);

            let (t_w, s_w) = req_windows(&req, gw, s_band);

            // greedy best improvement within windows
            let mut best: Option<(Cost<C>, BrandedFreeSlot<'_, T>)> = None;
            tx.with_explorer(|ex| {
                for s in ex
                    .iter_slots_for_request_within(&req, t_w, s_w)
                    .take(self.scan)
                {
                    let t = s.slot().start_time();
                    let sp = s.slot().space().start();
                    let hyp = dock_alloc_model::model::AssignmentRef::new(req.request(), sp, t);
                    let d = hyp.cost() - old_cost;
                    if d.value() < C::zero() && best.as_ref().is_none_or(|(bd, _)| d < *bd) {
                        best = Some((d, s));
                    }
                }
            });

            let Some((_d, slot)) = best else {
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
