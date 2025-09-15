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

use std::cmp::Ordering;
use std::fmt::Display;

use dock_alloc_core::{
    SolverVariable,
    cost::Cost,
    space::SpaceLength,
    time::{TimeDelta, TimePoint},
};
use num_traits::{NumCast, PrimInt, Signed, ToPrimitive};
use rand::Rng;

use super::err::{InstanceGenConfigBuildError, QuayTooShortError};
use super::policies::{HalfwidthPolicy, RelativeSpaceWindowPolicy, SpaceWindowPolicy};

/// Configuration for synthetic instance generation (terminal-like units).
#[derive(Debug, Clone, PartialEq)]
pub struct InstanceGenConfig<TimePrimitive, CostPrimitive>
where
    TimePrimitive: PrimInt + Signed + NumCast + ToPrimitive,
    CostPrimitive: PrimInt + Signed + NumCast + Copy,
{
    pub(crate) quay_length: SpaceLength,
    pub(crate) min_ship_length: SpaceLength,
    pub(crate) max_ship_length: SpaceLength,
    pub(crate) space_window_policy: SpaceWindowPolicy,

    pub(crate) movable_windows_min: usize,
    pub(crate) movable_windows_max: usize,
    pub(crate) windows_must_be_disjoint: bool,

    pub(crate) amount_movables: usize,
    pub(crate) amount_fixed: usize,

    pub(crate) horizon: TimePoint<TimePrimitive>,
    pub(crate) lambda_per_time: f64,

    pub(crate) processing_time_sigma: f64,
    pub(crate) min_processing: TimeDelta<TimePrimitive>,
    pub(crate) max_processing: Option<TimeDelta<TimePrimitive>>,
    pub(crate) fixed_gap: TimeDelta<TimePrimitive>,
    pub(crate) processing_mu_base: TimeDelta<TimePrimitive>,
    pub(crate) processing_mu_span: TimeDelta<TimePrimitive>,

    pub(crate) arrival_oversample_mult: usize,
    pub(crate) processing_sigma_floor: f64,
    pub(crate) length_span_epsilon: SpaceLength,

    pub(crate) cost_inc_num: Cost<CostPrimitive>,
    pub(crate) cost_inc_den: Cost<CostPrimitive>,
    pub(crate) min_cost_floor: Cost<CostPrimitive>,

    pub(crate) window_split_left_num: SpaceLength,
    pub(crate) window_split_den: SpaceLength,

    pub(crate) base_cost_per_delay: Cost<CostPrimitive>,
    pub(crate) base_cost_per_dev: Cost<CostPrimitive>,

    pub(crate) seed: u64,
}

impl<T, C> Default for InstanceGenConfig<T, C>
where
    T: SolverVariable + NumCast + ToPrimitive,
    C: SolverVariable + NumCast + Copy,
{
    fn default() -> Self {
        #[inline]
        fn to_t<T: SolverVariable + NumCast>(v: i64) -> T {
            NumCast::from(v).unwrap()
        }
        #[inline]
        fn td<T: SolverVariable + NumCast>(v: i64) -> dock_alloc_core::time::TimeDelta<T> {
            dock_alloc_core::time::TimeDelta::new(to_t::<T>(v))
        }
        #[inline]
        fn tp<T: SolverVariable + NumCast>(v: i64) -> dock_alloc_core::time::TimePoint<T> {
            dock_alloc_core::time::TimePoint::new(to_t::<T>(v))
        }
        #[inline]
        fn cost<C: SolverVariable + NumCast + Copy>(v: i64) -> dock_alloc_core::cost::Cost<C> {
            dock_alloc_core::cost::Cost::new(NumCast::from(v).unwrap())
        }

        let quay_length = SpaceLength::new(1000);
        let min_len = SpaceLength::new(140);
        let max_len = SpaceLength::new(400);
        let seed = 42;

        Self {
            quay_length,
            min_ship_length: min_len,
            max_ship_length: max_len,
            space_window_policy: SpaceWindowPolicy::Halfwidth(HalfwidthPolicy::Relative(
                RelativeSpaceWindowPolicy::new(0.75, SpaceLength::new(80), SpaceLength::new(600)),
            )),

            movable_windows_min: 1,
            movable_windows_max: 5,
            windows_must_be_disjoint: true,

            amount_movables: 70,
            amount_fixed: 50,
            horizon: tp::<T>(14400),

            lambda_per_time: 0.017,
            arrival_oversample_mult: 6,

            processing_time_sigma: 45.0,
            processing_sigma_floor: 10.0,
            min_processing: td::<T>(180),
            max_processing: Some(td::<T>(1800)),
            processing_mu_base: td::<T>(480),
            processing_mu_span: td::<T>(960),

            fixed_gap: td::<T>(30),

            window_split_left_num: SpaceLength::new(1),
            window_split_den: SpaceLength::new(2),
            length_span_epsilon: SpaceLength::new(1),

            base_cost_per_delay: cost::<C>(5),
            base_cost_per_dev: cost::<C>(1),
            cost_inc_num: cost::<C>(1),
            cost_inc_den: cost::<C>(1),
            min_cost_floor: cost::<C>(1),

            seed,
        }
    }
}

impl<TimePrimitive, CostPrimitive> InstanceGenConfig<TimePrimitive, CostPrimitive>
where
    TimePrimitive: PrimInt + Signed + NumCast + ToPrimitive,
    CostPrimitive: PrimInt + Signed + NumCast + Copy,
{
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        quay_length: SpaceLength,
        unord_min_length: SpaceLength,
        unord_max_length: SpaceLength,
        space_window_policy: SpaceWindowPolicy,
        movable_windows_min: usize,
        movable_windows_max: usize,
        windows_must_be_disjoint: bool,
        amount_movables: usize,
        amount_fixed: usize,
        horizon: TimePoint<TimePrimitive>,
        lambda_per_time: f64,
        processing_time_sigma: f64,
        min_processing: TimeDelta<TimePrimitive>,
        max_processing: Option<TimeDelta<TimePrimitive>>,
        fixed_gap: TimeDelta<TimePrimitive>,
        processing_mu_base: TimeDelta<TimePrimitive>,
        processing_mu_span: TimeDelta<TimePrimitive>,
        arrival_oversample_mult: usize,
        processing_sigma_floor: f64,
        length_span_epsilon: SpaceLength,
        cost_inc_num: Cost<CostPrimitive>,
        cost_inc_den: Cost<CostPrimitive>,
        min_cost_floor: Cost<CostPrimitive>,
        window_split_left_num: SpaceLength,
        window_split_den: SpaceLength,
        base_cost_per_delay: Cost<CostPrimitive>,
        base_cost_per_dev: Cost<CostPrimitive>,
        seed: u64,
    ) -> Result<Self, QuayTooShortError> {
        let (min_ship_length, max_ship_length) = match unord_min_length
            .partial_cmp(&unord_max_length)
            .expect("min/max length compare")
        {
            Ordering::Greater => (unord_max_length, unord_min_length),
            _ => (unord_min_length, unord_max_length),
        };

        if quay_length < max_ship_length {
            return Err(QuayTooShortError::new(quay_length, max_ship_length));
        }

        Ok(Self {
            quay_length,
            min_ship_length,
            max_ship_length,
            space_window_policy,
            movable_windows_min,
            movable_windows_max,
            windows_must_be_disjoint,
            amount_movables,
            amount_fixed,
            horizon,
            lambda_per_time,
            processing_time_sigma,
            min_processing,
            max_processing,
            fixed_gap,
            processing_mu_base,
            processing_mu_span,
            arrival_oversample_mult,
            processing_sigma_floor,
            length_span_epsilon,
            cost_inc_num,
            cost_inc_den,
            min_cost_floor,
            window_split_left_num,
            window_split_den,
            base_cost_per_delay,
            base_cost_per_dev,
            seed,
        })
    }

    // getters (public, used externally and by generator)
    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }
    #[inline]
    pub fn min_length(&self) -> SpaceLength {
        self.min_ship_length
    }
    #[inline]
    pub fn max_length(&self) -> SpaceLength {
        self.max_ship_length
    }
    #[inline]
    pub fn space_window_policy(&self) -> &SpaceWindowPolicy {
        &self.space_window_policy
    }
    #[inline]
    pub fn movable_windows_min(&self) -> usize {
        self.movable_windows_min
    }
    #[inline]
    pub fn movable_windows_max(&self) -> usize {
        self.movable_windows_max
    }
    #[inline]
    pub fn windows_must_be_disjoint(&self) -> bool {
        self.windows_must_be_disjoint
    }
    #[inline]
    pub fn amount_movables(&self) -> usize {
        self.amount_movables
    }
    #[inline]
    pub fn amount_fixed(&self) -> usize {
        self.amount_fixed
    }
    #[inline]
    pub fn horizon(&self) -> TimePoint<TimePrimitive> {
        self.horizon
    }
    #[inline]
    pub fn lambda_per_time(&self) -> f64 {
        self.lambda_per_time
    }
    #[inline]
    pub fn processing_time_sigma(&self) -> f64 {
        self.processing_time_sigma
    }
    #[inline]
    pub fn min_processing(&self) -> TimeDelta<TimePrimitive> {
        self.min_processing
    }
    #[inline]
    pub fn max_processing(&self) -> Option<TimeDelta<TimePrimitive>> {
        self.max_processing
    }
    #[inline]
    pub fn fixed_gap(&self) -> TimeDelta<TimePrimitive> {
        self.fixed_gap
    }
    #[inline]
    pub fn seed(&self) -> u64 {
        self.seed
    }
}

impl<TimePrimitive, CostPrimitive> Display for InstanceGenConfig<TimePrimitive, CostPrimitive>
where
    TimePrimitive: SolverVariable + NumCast + ToPrimitive,
    CostPrimitive: SolverVariable + NumCast + Copy,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let max_proc_str = self
            .max_processing
            .map(|p| p.to_string())
            .unwrap_or_else(|| "None".into());
        write!(
            f,
            "InstanceGenConfig {{ \
             quay_length: {}, min_length: {}, max_length: {}, space_window_policy: {}, \
             movable_windows_min: {}, movable_windows_max: {}, windows_must_be_disjoint: {}, \
             amount_movables: {}, amount_fixed: {}, horizon: {}, \
             lambda_per_time: {:.4}, processing_time_sigma: {:.4}, \
             min_processing: {}, max_processing: {}, fixed_gap: {}, \
             processing_mu_base: {}, processing_mu_span: {}, \
             arrival_oversample_mult: {}, processing_sigma_floor: {:.4}, \
             length_span_epsilon: {}, \
             cost_inc_num: {}, cost_inc_den: {}, min_cost_floor: {}, \
             window_split_left_num: {}, window_split_den: {}, \
             base_cost_per_delay: {}, base_cost_per_dev: {}, seed: {} \
             }}",
            self.quay_length,
            self.min_ship_length,
            self.max_ship_length,
            self.space_window_policy,
            self.movable_windows_min,
            self.movable_windows_max,
            self.windows_must_be_disjoint,
            self.amount_movables,
            self.amount_fixed,
            self.horizon,
            self.lambda_per_time,
            self.processing_time_sigma,
            self.min_processing,
            max_proc_str,
            self.fixed_gap,
            self.processing_mu_base,
            self.processing_mu_span,
            self.arrival_oversample_mult,
            self.processing_sigma_floor,
            self.length_span_epsilon,
            self.cost_inc_num,
            self.cost_inc_den,
            self.min_cost_floor,
            self.window_split_left_num,
            self.window_split_den,
            self.base_cost_per_delay,
            self.base_cost_per_dev,
            self.seed
        )
    }
}

/// Builder for `InstanceGenConfig`.
pub struct InstanceGenConfigBuilder<TimePrimitive, CostPrimitive>
where
    TimePrimitive: PrimInt + Signed + NumCast + ToPrimitive,
    CostPrimitive: PrimInt + Signed + NumCast + Copy,
{
    // Required
    quay_length: Option<SpaceLength>,
    min_length: Option<SpaceLength>,
    max_length: Option<SpaceLength>,
    horizon: Option<TimePoint<TimePrimitive>>,
    space_window_policy: Option<SpaceWindowPolicy>,
    amount_movables: Option<usize>,
    amount_fixed: Option<usize>,

    // Optional with defaults
    movable_windows_min: usize,
    movable_windows_max: usize,
    windows_must_be_disjoint: bool,
    lambda_per_time: f64,
    processing_time_sigma: f64,
    min_processing: TimeDelta<TimePrimitive>,
    max_processing: Option<TimeDelta<TimePrimitive>>,
    fixed_gap: TimeDelta<TimePrimitive>,
    processing_mu_base: TimeDelta<TimePrimitive>,
    processing_mu_span: TimeDelta<TimePrimitive>,
    arrival_oversample_mult: usize,
    processing_sigma_floor: f64,
    length_span_epsilon: SpaceLength,
    cost_inc_num: Cost<CostPrimitive>,
    cost_inc_den: Cost<CostPrimitive>,
    min_cost_floor: Cost<CostPrimitive>,
    window_split_left_num: SpaceLength,
    window_split_den: SpaceLength,
    base_cost_per_delay: Cost<CostPrimitive>,
    base_cost_per_dev: Cost<CostPrimitive>,
    seed: u64,
}

impl<TimePrimitive, CostPrimitive> Default
    for InstanceGenConfigBuilder<TimePrimitive, CostPrimitive>
where
    TimePrimitive: SolverVariable + NumCast + ToPrimitive,
    CostPrimitive: SolverVariable + NumCast + Copy,
{
    fn default() -> Self {
        fn to_time_delta<T: SolverVariable + NumCast>(
            v: i64,
        ) -> dock_alloc_core::time::TimeDelta<T> {
            dock_alloc_core::time::TimeDelta::new(NumCast::from(v).unwrap())
        }
        fn to_space_length(v: usize) -> SpaceLength {
            SpaceLength::new(v)
        }
        fn to_cost<C: SolverVariable + NumCast + Copy>(v: i64) -> dock_alloc_core::cost::Cost<C> {
            dock_alloc_core::cost::Cost::new(NumCast::from(v).unwrap())
        }
        let seed = rand::rng().random();

        Self {
            quay_length: None,
            min_length: None,
            max_length: None,
            horizon: None,
            space_window_policy: None,
            amount_movables: None,
            amount_fixed: None,

            movable_windows_min: 1,
            movable_windows_max: 5,
            windows_must_be_disjoint: true,
            lambda_per_time: 0.9,
            processing_time_sigma: 2.5,
            min_processing: to_time_delta(4),
            max_processing: Some(to_time_delta(72)),
            fixed_gap: to_time_delta(2),
            processing_mu_base: to_time_delta(10),
            processing_mu_span: to_time_delta(20),
            arrival_oversample_mult: 6,
            processing_sigma_floor: 0.1,
            length_span_epsilon: to_space_length(1),
            cost_inc_num: to_cost(1),
            cost_inc_den: to_cost(1),
            min_cost_floor: to_cost(1),
            window_split_left_num: to_space_length(1),
            window_split_den: to_space_length(2),
            base_cost_per_delay: to_cost(2),
            base_cost_per_dev: to_cost(1),
            seed,
        }
    }
}

impl<TimePrimitive, CostPrimitive> InstanceGenConfigBuilder<TimePrimitive, CostPrimitive>
where
    TimePrimitive: SolverVariable + NumCast + ToPrimitive,
    CostPrimitive: SolverVariable + NumCast + Copy,
{
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn quay_length(mut self, v: SpaceLength) -> Self {
        self.quay_length = Some(v);
        self
    }
    #[inline]
    pub fn min_length(mut self, v: SpaceLength) -> Self {
        self.min_length = Some(v);
        self
    }
    #[inline]
    pub fn max_length(mut self, v: SpaceLength) -> Self {
        self.max_length = Some(v);
        self
    }
    #[inline]
    pub fn horizon(mut self, v: TimePoint<TimePrimitive>) -> Self {
        self.horizon = Some(v);
        self
    }

    #[inline]
    pub fn space_policy_full_quay(mut self) -> Self {
        self.space_window_policy = Some(SpaceWindowPolicy::full_quay());
        self
    }
    #[inline]
    pub fn space_policy_fixed(mut self, halfwidth: SpaceLength) -> Self {
        self.space_window_policy = Some(SpaceWindowPolicy::fixed(halfwidth));
        self
    }
    #[inline]
    pub fn space_policy_relative(mut self, frac: f64, min: SpaceLength, max: SpaceLength) -> Self {
        self.space_window_policy = Some(SpaceWindowPolicy::relative(frac, min, max));
        self
    }

    pub fn movable_windows_range(mut self, min: usize, max: usize) -> Self {
        self.movable_windows_min = min;
        self.movable_windows_max = max.max(min);
        self
    }
    pub fn windows_must_be_disjoint(mut self, yes: bool) -> Self {
        self.windows_must_be_disjoint = yes;
        self
    }

    #[inline]
    pub fn amount_movables(mut self, v: usize) -> Self {
        self.amount_movables = Some(v);
        self
    }
    #[inline]
    pub fn amount_fixed(mut self, v: usize) -> Self {
        self.amount_fixed = Some(v);
        self
    }

    #[inline]
    pub fn lambda_per_time(mut self, v: f64) -> Self {
        self.lambda_per_time = v;
        self
    }
    #[inline]
    pub fn processing_time_sigma(mut self, v: f64) -> Self {
        self.processing_time_sigma = v;
        self
    }
    #[inline]
    pub fn min_processing(mut self, v: TimeDelta<TimePrimitive>) -> Self {
        self.min_processing = v;
        self
    }
    #[inline]
    pub fn max_processing(mut self, v: Option<TimeDelta<TimePrimitive>>) -> Self {
        self.max_processing = v;
        self
    }
    #[inline]
    pub fn fixed_gap(mut self, v: TimeDelta<TimePrimitive>) -> Self {
        self.fixed_gap = v;
        self
    }
    #[inline]
    pub fn processing_mu_base(mut self, v: TimeDelta<TimePrimitive>) -> Self {
        self.processing_mu_base = v;
        self
    }
    #[inline]
    pub fn processing_mu_span(mut self, v: TimeDelta<TimePrimitive>) -> Self {
        self.processing_mu_span = v;
        self
    }
    #[inline]
    pub fn arrival_oversample_mult(mut self, v: usize) -> Self {
        self.arrival_oversample_mult = v;
        self
    }
    #[inline]
    pub fn processing_sigma_floor(mut self, v: f64) -> Self {
        self.processing_sigma_floor = v;
        self
    }
    #[inline]
    pub fn length_span_epsilon(mut self, v: SpaceLength) -> Self {
        self.length_span_epsilon = v;
        self
    }
    #[inline]
    pub fn cost_inc_num(mut self, v: Cost<CostPrimitive>) -> Self {
        self.cost_inc_num = v;
        self
    }
    #[inline]
    pub fn cost_inc_den(mut self, v: Cost<CostPrimitive>) -> Self {
        self.cost_inc_den = v;
        self
    }
    #[inline]
    pub fn min_cost_floor(mut self, v: Cost<CostPrimitive>) -> Self {
        self.min_cost_floor = v;
        self
    }
    #[inline]
    pub fn window_split_left_num(mut self, v: SpaceLength) -> Self {
        self.window_split_left_num = v;
        self
    }
    #[inline]
    pub fn window_split_den(mut self, v: SpaceLength) -> Self {
        self.window_split_den = v;
        self
    }
    #[inline]
    pub fn base_cost_per_delay(mut self, v: Cost<CostPrimitive>) -> Self {
        self.base_cost_per_delay = v;
        self
    }
    #[inline]
    pub fn base_cost_per_dev(mut self, v: Cost<CostPrimitive>) -> Self {
        self.base_cost_per_dev = v;
        self
    }
    pub fn random_seed(mut self) -> Self {
        self.seed = rand::rng().random();
        self
    }
    #[inline]
    pub fn seed(mut self, v: u64) -> Self {
        self.seed = v;
        self
    }

    pub fn build(
        self,
    ) -> Result<InstanceGenConfig<TimePrimitive, CostPrimitive>, InstanceGenConfigBuildError> {
        use InstanceGenConfigBuildError::*;
        let quay_length = self.quay_length.ok_or(MissingQuayLength)?;
        let min_length = self.min_length.ok_or(MissingMinLength)?;
        let max_length = self.max_length.ok_or(MissingMaxLength)?;
        let horizon = self.horizon.ok_or(MissingHorizon)?;
        let swp = self.space_window_policy.ok_or(MissingSpaceWindowPolicy)?;
        let amt_mov = self.amount_movables.ok_or(MissingAmountMovables)?;
        let amt_fix = self.amount_fixed.ok_or(MissingAmountFixed)?;

        Ok(InstanceGenConfig::new(
            quay_length,
            min_length,
            max_length,
            swp,
            self.movable_windows_min,
            self.movable_windows_max,
            self.windows_must_be_disjoint,
            amt_mov,
            amt_fix,
            horizon,
            self.lambda_per_time,
            self.processing_time_sigma,
            self.min_processing,
            self.max_processing,
            self.fixed_gap,
            self.processing_mu_base,
            self.processing_mu_span,
            self.arrival_oversample_mult,
            self.processing_sigma_floor,
            self.length_span_epsilon,
            self.cost_inc_num,
            self.cost_inc_den,
            self.min_cost_floor,
            self.window_split_left_num,
            self.window_split_den,
            self.base_cost_per_delay,
            self.base_cost_per_dev,
            self.seed,
        )?)
    }
}
