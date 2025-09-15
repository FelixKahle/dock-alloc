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

mod config;
mod err;
mod policies;

pub use config::{InstanceGenConfig, InstanceGenConfigBuilder};
pub use err::{InstanceGenConfigBuildError, QuayTooShortError};
pub use policies::{HalfwidthPolicy, RelativeSpaceWindowPolicy, SpaceWindowPolicy};

use crate::{
    dec::Assignment,
    id::RequestId,
    problem::{Problem, ProblemBuilder},
    req::{Fixed, Movable, Request},
};
use dock_alloc_core::{
    SolverVariable,
    cost::Cost,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimePoint},
};
use num_traits::{FromPrimitive, NumCast, SaturatingAdd, SaturatingMul, ToPrimitive};
use rand::{Rng, SeedableRng, rngs::SmallRng};
use rand_distr::{Distribution, Exp, Normal, Uniform, uniform::SampleUniform};
use std::fmt::Debug;

pub struct InstanceGenerator<TimePrimitive, CostPrimitive>
where
    TimePrimitive: SolverVariable + NumCast + ToPrimitive + SampleUniform,
    CostPrimitive: SolverVariable + NumCast + Copy,
{
    config: InstanceGenConfig<TimePrimitive, CostPrimitive>,
    rng: SmallRng,
    length_distribution: Uniform<usize>,
    next_id: u64,
}

impl<TimePrimitive, CostPrimitive> From<InstanceGenConfig<TimePrimitive, CostPrimitive>>
    for InstanceGenerator<TimePrimitive, CostPrimitive>
where
    TimePrimitive: SolverVariable + NumCast + ToPrimitive + Debug + SampleUniform + FromPrimitive,
    CostPrimitive: SolverVariable + NumCast + Copy + SaturatingAdd + SaturatingMul,
{
    fn from(config: InstanceGenConfig<TimePrimitive, CostPrimitive>) -> Self {
        Self::new(config)
    }
}

impl<TimePrimitive, CostPrimitive> InstanceGenerator<TimePrimitive, CostPrimitive>
where
    TimePrimitive: SolverVariable + NumCast + ToPrimitive + Debug + SampleUniform + FromPrimitive,
    CostPrimitive: SolverVariable + NumCast + Copy + SaturatingAdd + SaturatingMul,
{
    pub fn new(config: InstanceGenConfig<TimePrimitive, CostPrimitive>) -> Self {
        let seed = config.seed();
        Self {
            length_distribution: Uniform::new_inclusive(
                config.min_ship_length.value(),
                config.max_ship_length.value(),
            )
            .expect("valid [min_length, max_length]"),
            rng: SmallRng::seed_from_u64(seed),
            config,
            next_id: 0,
        }
    }

    #[inline]
    fn fresh_id(&mut self) -> RequestId {
        let id = self.next_id;
        self.next_id += 1;
        RequestId::new(id)
    }

    #[inline]
    fn sample_num_windows(&mut self) -> usize {
        let min = self.config.movable_windows_min;
        let max = self.config.movable_windows_max.max(min);
        if min == max {
            min
        } else {
            self.rng.random_range(min..=max)
        }
    }

    fn normalise_windows(
        &self,
        mut windows: Vec<SpaceInterval>,
        length: SpaceLength,
    ) -> Vec<SpaceInterval> {
        // Ensure every window can fit the ship
        for w in windows.iter_mut() {
            if w.measure() < length {
                let need = length - w.measure();
                let left = self.split_left(need);
                let right = need - left;
                let mut s = w.start().saturating_sub(left);
                let mut e = (w.end() + right).min(self.quay_end());
                if (e - s) < length {
                    s = s.min(self.max_start_pos(length));
                    e = s + length;
                }
                *w = SpaceInterval::new(s, e);
            }
        }

        if self.config.windows_must_be_disjoint {
            windows.sort_by_key(|w| w.start().value());
            let mut disjoint: Vec<SpaceInterval> = Vec::with_capacity(windows.len());
            for w in windows {
                if let Some(last) = disjoint.last() {
                    if w.start() < last.end() {
                        // try to shift right to avoid overlap
                        let len = w.measure();
                        let new_start = last.end();
                        let new_end = (new_start + len).min(self.quay_end());
                        let start = new_end.saturating_sub(len);
                        let fixed = SpaceInterval::new(start, new_end);
                        if fixed.start() < last.end() {
                            // cannot make it disjoint → skip it
                            continue;
                        }
                        disjoint.push(fixed);
                    } else {
                        disjoint.push(w);
                    }
                } else {
                    disjoint.push(w);
                }
            }
            if disjoint.is_empty() {
                // fallback: one minimal window at 0 of exact ship length (always fits after clamp)
                let end = (SpacePosition::zero() + length).min(self.quay_end());
                return vec![SpaceInterval::new(end.saturating_sub(length), end)];
            }
            disjoint
        } else {
            windows.sort_by_key(|w| (w.start().value(), w.end().value()));
            windows.dedup();
            windows
        }
    }

    fn windows_for_movable(
        &mut self,
        target: SpacePosition,
        length: SpaceLength,
    ) -> Vec<SpaceInterval> {
        let n = self.sample_num_windows();
        if n == 0 {
            return Vec::new();
        }

        match &self.config.space_window_policy {
            SpaceWindowPolicy::FullQuay => {
                let mut out = Vec::with_capacity(n);
                let max_extra = (self.config.quay_length.value() / 2).max(length.value());
                for _ in 0..n {
                    let extra = self.rng.random_range(0..=max_extra);
                    let width_val = length
                        .value()
                        .saturating_add(extra)
                        .min(self.config.quay_length.value());
                    let width = SpaceLength::new(width_val);
                    let start_max = self.config.quay_length.saturating_sub(width).value();
                    let start = if start_max == 0 {
                        SpacePosition::zero()
                    } else {
                        SpacePosition::new(self.rng.random_range(0..=start_max))
                    };
                    let end = (start + width).min(self.quay_end());
                    let iv = SpaceInterval::new(end.saturating_sub(width), end);
                    out.push(iv);
                }
                self.normalise_windows(out, length)
            }
            SpaceWindowPolicy::Halfwidth(_) => {
                let halfwidth = self.halfwidth_for(length).expect("halfwidth required");
                let mut out = Vec::with_capacity(n);
                let jitter_max = halfwidth.value().saturating_div(2);
                for _ in 0..n {
                    let offs = if jitter_max == 0 {
                        0
                    } else {
                        let j = self.rng.random_range(0..=jitter_max);
                        if self.rng.random() {
                            j as isize
                        } else {
                            -(j as isize)
                        }
                    };
                    let tgt_val = target.value() as isize + offs;
                    let tgt = if tgt_val <= 0 {
                        SpacePosition::zero()
                    } else {
                        SpacePosition::new(
                            (tgt_val as usize).min(self.max_start_pos(length).value()),
                        )
                    };
                    let iv = self.fixed_halfwidth_window(tgt, length, halfwidth);
                    out.push(iv);
                }
                self.normalise_windows(out, length)
            }
        }
    }

    #[inline]
    pub fn quay_end(&self) -> SpacePosition {
        SpacePosition::new(self.config.quay_length.value())
    }
    #[inline]
    pub fn max_start_pos(&self, length: SpaceLength) -> SpacePosition {
        self.quay_end() - length
    }

    #[inline]
    fn halfwidth_for(&self, length: SpaceLength) -> Option<SpaceLength> {
        match &self.config.space_window_policy {
            SpaceWindowPolicy::FullQuay => None,
            SpaceWindowPolicy::Halfwidth(halfwidth_policy) => match halfwidth_policy {
                HalfwidthPolicy::Fixed(hw) => Some(*hw),
                HalfwidthPolicy::Relative(RelativeSpaceWindowPolicy {
                    frac_of_length,
                    min,
                    max,
                }) => {
                    let length_f: f64 = NumCast::from(length.value()).unwrap();
                    let hw_f = (*frac_of_length * length_f).round();
                    let hw_usize: usize = NumCast::from(hw_f).unwrap();
                    Some(SpaceLength::new(hw_usize.clamp(min.value(), max.value())))
                }
            },
        }
    }

    pub fn generate(&mut self) -> Problem<TimePrimitive, CostPrimitive> {
        let total = self.config.amount_fixed + self.config.amount_movables;
        let arrivals = self.sample_arrivals(total);

        let mut builder =
            ProblemBuilder::<TimePrimitive, CostPrimitive>::new(self.config.quay_length);

        let mut fixed_indices: Vec<usize> = (0..self.config.amount_fixed).collect();
        fixed_indices.sort_by(|&a, &b| arrivals[a].cmp(&arrivals[b]));

        let fixed_assignments = self.plan_fixed(&fixed_indices, &arrivals);
        for a in fixed_assignments {
            builder
                .add_preassigned(a)
                .expect("preassigned must succeed");
        }

        for t in arrivals
            .iter()
            .take(total)
            .skip(self.config.amount_fixed)
            .copied()
        {
            let req = self.sample_movable(t);
            builder
                .add_movable_request(req)
                .expect("movable must succeed");
        }

        builder.build()
    }

    fn sample_arrivals(&mut self, count: usize) -> Vec<TimePoint<TimePrimitive>> {
        let mut arrivals = Vec::with_capacity(count);
        let mut current_time_f = 0.0f64;

        if self.config.lambda_per_time > 0.0 {
            let exp = Exp::new(self.config.lambda_per_time).unwrap();
            for _ in 0..(count * self.config.arrival_oversample_mult) {
                current_time_f += exp.sample(&mut self.rng);
                let rounded = current_time_f.round() as i64;
                let tval: TimePrimitive = NumCast::from(rounded.max(0)).unwrap();
                let tp = TimePoint::new(tval);
                if tp < self.config.horizon {
                    arrivals.push(tp);
                    if arrivals.len() >= count {
                        break;
                    }
                } else {
                    break;
                }
            }
        }

        while arrivals.len() < count {
            let v: TimePrimitive = self
                .rng
                .random_range(TimePrimitive::zero()..self.config.horizon.value());
            arrivals.push(TimePoint::new(v));
        }

        arrivals.sort();
        arrivals.truncate(count);
        arrivals
    }

    #[inline]
    fn sample_length(&mut self) -> SpaceLength {
        SpaceLength::new(self.length_distribution.sample(&mut self.rng))
    }

    #[inline]
    fn sample_target_position_for_length(&mut self, length: SpaceLength) -> SpacePosition {
        let max_start = self.config.quay_length.saturating_sub(length).value();
        let start_value = if max_start == 0 {
            0
        } else {
            self.rng.random_range(0..=max_start)
        };
        SpacePosition::new(start_value)
    }

    #[inline]
    fn length_span(&self) -> SpaceLength {
        let raw = self
            .config
            .max_ship_length
            .saturating_sub(self.config.min_ship_length);
        SpaceLength::new(
            raw.value()
                .max(self.config.length_span_epsilon.value().max(1)),
        )
    }

    fn processing_mean_from_length(&self, length: SpaceLength) -> f64 {
        let base_mu = self.config.processing_mu_base;
        let span_mu = self.config.processing_mu_span;
        let length_delta = length.saturating_sub(self.config.min_ship_length);
        let dx: f64 = NumCast::from(length_delta.value()).unwrap();
        let span: f64 = NumCast::from(self.length_span().value()).unwrap();
        let base: f64 = NumCast::from(base_mu.value()).unwrap();
        let span_add: f64 = NumCast::from(span_mu.value()).unwrap();
        base + (span_add * dx) / span
    }

    fn sample_processing(&mut self, length: SpaceLength) -> TimeDelta<TimePrimitive> {
        let mean = self.processing_mean_from_length(length);
        let sigma = self
            .config
            .processing_time_sigma
            .max(self.config.processing_sigma_floor);
        let normal = Normal::new(mean, sigma).unwrap();
        let draw_f64 = normal.sample(&mut self.rng).round();
        let draw_i64: i64 = NumCast::from(draw_f64).unwrap();

        let mut v: TimePrimitive = NumCast::from(draw_i64).unwrap();
        if v < self.config.min_processing.value() {
            v = self.config.min_processing.value();
        }
        if let Some(maxp) = self.config.max_processing
            && v > maxp.value() {
                v = maxp.value();
            }
        TimeDelta::new(v)
    }

    fn length_scaled_costs(
        &self,
        length: SpaceLength,
    ) -> (Cost<CostPrimitive>, Cost<CostPrimitive>) {
        let length_delta = length.saturating_sub(self.config.min_ship_length);
        let span = self.length_span();
        let span_scalar: CostPrimitive = NumCast::from(span.value()).unwrap();
        let delta_scalar: CostPrimitive = NumCast::from(length_delta.value()).unwrap();
        let increment_cost = self.config.cost_inc_num * delta_scalar;
        let base_cost = self.config.cost_inc_den * span_scalar;

        let scaling: CostPrimitive = increment_cost
            .ratio(base_cost)
            .unwrap_or(CostPrimitive::zero());

        let scale = |base: Cost<CostPrimitive>| {
            let scaled = base.saturating_add(base.saturating_mul(scaling));
            scaled.max(self.config.min_cost_floor)
        };
        (
            scale(self.config.base_cost_per_delay),
            scale(self.config.base_cost_per_dev),
        )
    }

    #[inline]
    fn split_left(&self, needed: SpaceLength) -> SpaceLength {
        if self.config.window_split_den.is_zero() {
            return SpaceLength::zero();
        }
        let left_val = (needed.value() * self.config.window_split_left_num.value())
            / self.config.window_split_den.value();
        SpaceLength::new(left_val)
    }

    fn space_window_for_fixed_assignment(
        &self,
        start_pos: SpacePosition,
        length: SpaceLength,
    ) -> SpaceInterval {
        match &self.config.space_window_policy {
            SpaceWindowPolicy::FullQuay => {
                SpaceInterval::new(SpacePosition::zero(), self.quay_end())
            }
            SpaceWindowPolicy::Halfwidth(_) => {
                let hw = self.halfwidth_for(length).expect("halfwidth required");
                self.fixed_halfwidth_window_containing_run(start_pos, length, hw)
            }
        }
    }

    fn fixed_halfwidth_window(
        &self,
        target: SpacePosition,
        length: SpaceLength,
        halfwidth: SpaceLength,
    ) -> SpaceInterval {
        let quay_end = self.quay_end();
        let mut s = target.saturating_sub(halfwidth);
        let mut e = (target + halfwidth).min(quay_end);

        if (e - s) < length {
            let need = length - (e - s);
            let l = self.split_left(need);
            let r = need - l;

            s = s.saturating_sub(l);
            e = (e + r).min(quay_end);

            if (e - s) < length {
                s = SpacePosition::zero();
                e = (s + length).min(quay_end);
            }
        }
        SpaceInterval::new(s, e)
    }

    fn fixed_halfwidth_window_containing_run(
        &self,
        start_pos: SpacePosition,
        length: SpaceLength,
        halfwidth: SpaceLength,
    ) -> SpaceInterval {
        let quay_end = self.quay_end();
        let mut s = start_pos.saturating_sub(halfwidth);
        let mut e = (start_pos + length + halfwidth).min(quay_end);

        if (e - s) < length {
            e = (s + length).min(quay_end);
            s = e.saturating_sub(length);
        }
        SpaceInterval::new(s, e)
    }

    fn sample_movable(
        &mut self,
        arrival: TimePoint<TimePrimitive>,
    ) -> Request<Movable, TimePrimitive, CostPrimitive> {
        let length = self.sample_length();
        let processing = self.sample_processing(length);
        let target = self.sample_target_position_for_length(length);
        let (c_delay, c_dev) = self.length_scaled_costs(length);
        let windows = self.windows_for_movable(target, length);

        Request::<Movable, TimePrimitive, CostPrimitive>::new(
            self.fresh_id(),
            length,
            arrival,
            processing,
            target,
            c_delay,
            c_dev,
            windows,
        )
        .expect("movable: constructed request must be feasible")
    }

    fn plan_fixed(
        &mut self,
        fixed_sorted: &[usize],
        arrivals: &[TimePoint<TimePrimitive>],
    ) -> Vec<Assignment<Fixed, TimePrimitive, CostPrimitive>> {
        let mut out = Vec::with_capacity(fixed_sorted.len());
        let mut current_time = TimePoint::new(TimePrimitive::zero());

        for &idx in fixed_sorted {
            let length = self.sample_length();
            let processing = self.sample_processing(length);
            let target = self.sample_target_position_for_length(length);
            let (c_delay, c_dev) = self.length_scaled_costs(length);

            let arrival = arrivals[idx];
            let start = if arrival > current_time {
                arrival
            } else {
                current_time
            };
            let start_pos = if target > self.max_start_pos(length) {
                self.max_start_pos(length)
            } else {
                target
            };
            let space_window = self.space_window_for_fixed_assignment(start_pos, length);

            let req = Request::<Fixed, TimePrimitive, CostPrimitive>::new(
                self.fresh_id(),
                length,
                arrival,
                processing,
                target,
                c_delay,
                c_dev,
                vec![space_window],
            )
            .expect("fixed: constructed request must be feasible");

            out.push(Assignment::new(req, start_pos, start));
            current_time = start + processing + self.config.fixed_gap;
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type Tm = i64;
    type Cm = i64;

    fn cfg_relative(seed: u64) -> InstanceGenConfig<Tm, Cm> {
        InstanceGenConfig::new(
            SpaceLength::new(1_500),
            SpaceLength::new(80),
            SpaceLength::new(300),
            SpaceWindowPolicy::Halfwidth(HalfwidthPolicy::Relative(
                RelativeSpaceWindowPolicy::new(0.75, SpaceLength::new(60), SpaceLength::new(260)),
            )),
            1,
            5,
            true,
            25,
            5,
            TimePoint::new(96),
            0.9,
            2.5,
            TimeDelta::new(4),
            Some(TimeDelta::new(72)),
            TimeDelta::new(2),
            TimeDelta::new(10),
            TimeDelta::new(20),
            6,
            0.1,
            SpaceLength::new(1),
            Cost::new(1),
            Cost::new(1),
            Cost::new(1),
            SpaceLength::new(1),
            SpaceLength::new(2),
            Cost::new(2),
            Cost::new(1),
            seed,
        )
        .unwrap()
    }

    #[test]
    fn generate_shapes_and_counts() {
        let config = cfg_relative(42);
        let mut generator = InstanceGenerator::<Tm, Cm>::new(config.clone());
        let problem: Problem<Tm, Cm> = generator.generate();

        assert_eq!(problem.movables().len(), config.amount_movables());
        assert_eq!(problem.preassigned().len(), config.amount_fixed());
        assert_eq!(
            problem.total_requests(),
            config.amount_movables() + config.amount_fixed()
        );
        assert!(config.quay_length() >= config.max_length());
    }

    #[test]
    fn movable_requests_feasible() {
        let config = cfg_relative(123);
        let mut generator = InstanceGenerator::<Tm, Cm>::new(config.clone());
        let problem = generator.generate();

        for r in problem.iter_movable_requests() {
            assert!(r.length() >= config.min_length());
            assert!(r.length() <= config.max_length());
            assert!(
                r.feasible_space_windows()
                    .iter()
                    .all(|w| w.measure() >= r.length())
            );
            let max_start_pos = SpacePosition::new(config.quay_length().value()) - r.length();
            assert!(r.target_position() <= max_start_pos);

            // check disjointness if requested
            if config.windows_must_be_disjoint() {
                let mut ws = r.feasible_space_windows().to_vec();
                ws.sort_by_key(|w| (w.start().value(), w.end().value()));
                for pair in ws.windows(2) {
                    assert!(pair[0].end() <= pair[1].start());
                }
            }
        }
    }

    #[test]
    fn fixed_assignments_non_overlapping_in_time_and_within_quay() {
        let config = cfg_relative(777);
        let mut generator = InstanceGenerator::<Tm, Cm>::new(config.clone());
        let problem = generator.generate();

        let mut spans: Vec<_> = problem
            .iter_fixed_assignments()
            .map(|a| {
                let st = a.start_time();
                let et = st + a.request().processing_duration();
                let sp = a.start_position();
                let ep = sp + a.request().length();
                (st, et, sp, ep, a)
            })
            .collect();

        spans.sort_by(|a, b| a.0.cmp(&b.0));

        let mut prev_end: Option<TimePoint<i64>> = None;
        let quay_end = SpacePosition::new(config.quay_length().value());
        for (st, et, sp, ep, a) in spans {
            if let Some(pe) = prev_end {
                assert!(st >= pe, "fixed assignments overlap in time");
            }
            prev_end = Some(et);

            assert!(sp <= quay_end);
            assert!(ep <= quay_end);

            for w in a.request().feasible_space_windows() {
                assert!(w.contains(sp));
                assert!(w.contains(ep) || ep == w.end());
            }
            assert_eq!(a.request().length(), ep - sp);
        }
    }

    #[test]
    fn costs_increase_with_length() {
        let config = cfg_relative(999);
        let generator = InstanceGenerator::<Tm, Cm>::new(config.clone());

        let (c_delay_min, c_dev_min) = generator.length_scaled_costs(config.min_length());
        let (c_delay_max, c_dev_max) = generator.length_scaled_costs(config.max_length());

        assert!(c_delay_max.value() >= c_delay_min.value());
        assert!(c_dev_max.value() >= c_dev_min.value());
        assert!(c_delay_max.value() > c_delay_min.value() || c_dev_max.value() > c_dev_min.value());
    }

    #[test]
    fn processing_is_clamped_between_min_and_max_if_present() {
        let config = InstanceGenConfig::new(
            SpaceLength::new(1_000),
            SpaceLength::new(80),
            SpaceLength::new(300),
            SpaceWindowPolicy::FullQuay,
            1,
            5,
            true,
            0,
            0,
            TimePoint::new(500),
            0.0,
            10.0,
            TimeDelta::new(20),
            Some(TimeDelta::new(24)),
            TimeDelta::new(0),
            TimeDelta::new(10),
            TimeDelta::new(20),
            6,
            0.1,
            SpaceLength::new(1),
            Cost::new(1),
            Cost::new(1),
            Cost::new(1_i64),
            SpaceLength::new(1),
            SpaceLength::new(2),
            Cost::new(1_i64),
            Cost::new(1_i64),
            7,
        )
        .unwrap();

        let mut generator = InstanceGenerator::<Tm, Cm>::new(config);
        let ship_len = SpaceLength::new(300);

        for _ in 0..100 {
            let d = generator.sample_processing(ship_len);
            assert!(
                d.value() >= 20 && d.value() <= 24,
                "processing {:?} not clamped",
                d
            );
        }
    }

    #[test]
    fn fixed_assignments_start_no_earlier_than_arrival() {
        let config = cfg_relative(31415);
        let mut generator = InstanceGenerator::<Tm, Cm>::new(config.clone());
        let problem = generator.generate();

        for a in problem.iter_fixed_assignments() {
            assert!(a.start_time() >= a.request().arrival_time());
        }
    }
}
