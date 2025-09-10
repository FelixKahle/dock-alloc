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

use crate::model::{Assignment, Fixed, Movable, Problem, ProblemBuilder, Request, RequestId};
use dock_alloc_core::domain::{
    Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use num_traits::{NumCast, PrimInt, Signed, ToPrimitive};
use rand::{Rng, SeedableRng, rngs::SmallRng};
use rand_distr::{Distribution, Exp, Normal, Uniform, uniform::SampleUniform};
use std::{
    cmp::Ordering,
    fmt::{Debug, Display},
};

#[derive(Debug, Clone, PartialEq)]
pub struct RelativeSpaceWindowPolicy {
    pub frac_of_length: f64,
    pub min: SpaceLength,
    pub max: SpaceLength,
}

impl Display for RelativeSpaceWindowPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "RelativeSpaceWindowPolicy {{ frac_of_length: {:.4}, min: {}, max: {} }}",
            self.frac_of_length, self.min, self.max
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum SpaceWindowPolicy {
    FixedHalfwidth(SpaceLength),
    Relative(RelativeSpaceWindowPolicy),
    MinMeasure(SpaceLength),
    FullQuay,
}

impl Display for SpaceWindowPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpaceWindowPolicy::FixedHalfwidth(hw) => {
                write!(f, "SpaceWindowPolicy::FixedHalfwidth({})", hw)
            }
            SpaceWindowPolicy::Relative(r) => {
                write!(f, "SpaceWindowPolicy::Relative({})", r)
            }
            SpaceWindowPolicy::MinMeasure(m) => {
                write!(f, "SpaceWindowPolicy::MinMeasure({})", m)
            }
            SpaceWindowPolicy::FullQuay => write!(f, "SpaceWindowPolicy::FullQuay"),
        }
    }
}

/// Configuration for generating a synthetic berth-allocation instance.
///
/// # Notes
/// - All **lengths** and **positions** are measured along the quay (in slots/units).
/// - All **times** are discrete (integer ticks).
/// - The generator ensures windows fit inside the quay and time horizon.
/// - When Poisson arrivals don’t produce enough ships within the horizon, the
///   generator tops up by sampling times uniformly in `[0, horizon]`.
#[derive(Debug, Clone, PartialEq)]
pub struct InstanceGenConfig<T, C>
where
    T: PrimInt + Signed + NumCast + ToPrimitive,
    C: PrimInt + Signed + NumCast + Copy,
{
    /// Total usable length of the quay.
    ///
    /// All ships must fit inside `[0, quay_length]`. If `quay_length` is
    /// smaller than `max_ship_length`, building the config will fail.
    quay_length: SpaceLength,

    /// Minimum ship length to sample (inclusive).
    ///
    /// The generator draws ship lengths uniformly from
    /// `[min_ship_length, max_ship_length]`.
    /// Keep this ≥ 1 and ≤ `max_ship_length`.
    min_ship_length: SpaceLength,

    /// Maximum ship length to sample (inclusive).
    ///
    /// Must be ≤ `quay_length`. Larger ships imply longer processing times and
    /// usually higher costs (see cost ramp below).
    max_ship_length: SpaceLength,

    /// Policy for how to construct **space windows** (allowed berth intervals)
    /// around a target/assignment.
    ///
    /// Options include full-quay windows, fixed half-width around a target,
    /// a relative half-width based on ship length, or enforcing a minimum
    /// measure (window length). The generator ensures the final window lies
    /// within the quay and is large enough to hold the ship.
    space_window_policy: SpaceWindowPolicy,

    /// Number of **movable** requests to generate.
    ///
    /// Movables are ships without fixed start times/positions; they get
    /// **feasible windows** and a target position, but no preassigned berth.
    amount_movables: usize,

    /// Number of **fixed** assignments to generate.
    ///
    /// Fixed ships are created as already planned runs with concrete start
    /// time/position; the generator guarantees they do **not overlap in time**
    /// and that they sit inside their windows and the quay.
    amount_fixed: usize,

    /// Latest allowed time point for anything in the instance.
    ///
    /// All arrivals and windows must lie within `[0, horizon]`.
    horizon: TimePoint<T>,

    /// **Arrival rate** per time unit for the Poisson process (λ).
    ///
    /// - If `> 0.0`: interarrival times are `Exp(λ)` and we accumulate them
    ///   to get arrival times (rounded to integers).
    /// - If `== 0.0`: we skip Poisson and later fill arrivals uniformly.
    ///
    /// Tip: Larger λ → more arrivals early; smaller λ → sparser arrivals.
    lambda_per_time: f64,

    /// Standard deviation (σ) for **processing time** draws (Normal distribution).
    ///
    /// The mean μ depends on ship length (see `processing_mu_base/span`).
    /// We draw `Normal(μ, σ)`, round to integers, then **clamp** to
    /// `[min_processing, max_processing]` (if max set).
    processing_time_sigma: f64,

    /// **Minimum processing time** allowed after drawing from the Normal.
    ///
    /// Any sampled duration below this is clamped up to this value.
    min_processing: TimeDelta<T>,

    /// Optional **maximum processing time** allowed after drawing.
    ///
    /// If `Some(max)`, any sampled duration above this is clamped down to `max`.
    /// If `None`, there is no upper clamp.
    max_processing: Option<TimeDelta<T>>,

    /// Extra slack allowed at the *end* of the time window.
    ///
    /// For a request with processing time `p` starting at `s`, the latest end
    /// is roughly `s + p + time_slack` (but never beyond `horizon`).
    time_slack: TimeDelta<T>,

    /// Idle time inserted **between fixed assignments**.
    ///
    /// Ensures fixed ships don’t overlap in time; after placing a fixed ship
    /// of duration `p`, the next fixed start is at least `p + fixed_gap` later.
    fixed_gap: TimeDelta<T>,

    /// Base component of the **processing time mean** μ (as time delta).
    ///
    /// The mean processing time scales with ship length using:
    /// `μ(length) = processing_mu_base + processing_mu_span * (length - min) / span`,
    /// where `span` is clamped to at least `max(1, length_span_epsilon)`.
    processing_mu_base: TimeDelta<T>,

    /// Span component of the **processing time mean** μ.
    ///
    /// Larger values make μ grow more strongly from `min_ship_length`
    /// to `max_ship_length`.
    processing_mu_span: TimeDelta<T>,

    /// Caps how many exponential interarrivals we attempt when generating
    /// arrivals from the Poisson process.
    ///
    /// We try up to `n * arrival_oversample_mult` exponential draws to collect
    /// `n = amount_fixed + amount_movables` arrivals **within the horizon**.
    /// If we still don’t have enough, we **top up** with uniform times in
    /// `[0, horizon]` so the instance always has the requested count.
    arrival_oversample_mult: usize,

    /// Lower bound for `processing_time_sigma`.
    ///
    /// Prevents a near-zero σ that would make the Normal almost deterministic.
    /// The effective σ is `max(processing_time_sigma, processing_sigma_floor)`.
    processing_sigma_floor: f64,

    /// Minimum value used for the **length span** in formulas.
    ///
    /// Let `span = max_ship_length - min_ship_length`. To avoid divide-by-zero
    /// (e.g., when min == max), we internally use
    /// `effective_span = max(span, max(1, length_span_epsilon))`.
    length_span_epsilon: SpaceLength,

    /// Numerator for the **length-based cost ramp**.
    ///
    /// For ship length `len`, with `dx = len - min_ship_length` and
    /// `span = effective_span`, we compute
    /// `ramp_factor = (cost_inc_num * dx) / (cost_inc_den * span)`.
    /// Each base cost is then scaled as `base + base * ramp_factor` (floored).
    cost_inc_num: C,

    /// Denominator for the **length-based cost ramp**.
    ///
    /// Larger `cost_inc_den` means a gentler ramp; smaller means steeper.
    cost_inc_den: C,

    /// Minimum allowed **final cost** after scaling.
    ///
    /// After applying the ramp to a base cost, we clamp it up to this floor.
    min_cost_floor: C,

    /// How much of any **extra needed window length** to add on the **left**,
    /// expressed as an integer fraction numerator.
    ///
    /// When a window isn’t long enough to contain the ship, we must expand it
    /// by `need`. We split that as:
    /// `add_left = floor(need * window_split_left_num / window_split_den)`,
    /// `add_right = need - add_left`.
    window_split_left_num: SpaceLength,

    /// Denominator for the window split fraction.
    ///
    /// Example: for a 50/50 split use `left_num = 1`, `den = 2`.
    window_split_den: SpaceLength,

    /// **Base unit cost** per unit of **delay** (before length ramp).
    ///
    /// The final cost for delay grows with ship length according to the
    /// integer ramp described above (and is floored by `min_cost_floor`).
    base_cost_per_delay: C,

    /// **Base unit cost** per unit of **spatial deviation** (before ramp).
    ///
    /// Like delay cost, this is scaled by the same length-based ramp and
    /// then floored by `min_cost_floor`.
    base_cost_per_dev: C,

    /// RNG seed for reproducible generation.
    ///
    /// Use a fixed value to get the same instance again; change it to get
    /// different random draws with the same configuration.
    seed: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuayTooShortError {
    quay_length: SpaceLength,
    max_ship_length: SpaceLength,
}

impl QuayTooShortError {
    fn new(quay_length: SpaceLength, max_ship_length: SpaceLength) -> Self {
        Self {
            quay_length,
            max_ship_length,
        }
    }

    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    pub fn max_ship_length(&self) -> SpaceLength {
        self.max_ship_length
    }
}

impl Display for QuayTooShortError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "QuayTooShortError: quay_length {} is shorter than max ship length {}",
            self.quay_length, self.max_ship_length
        )
    }
}

impl<T, C> InstanceGenConfig<T, C>
where
    T: PrimInt + Signed + NumCast + ToPrimitive,
    C: PrimInt + Signed + NumCast + Copy,
{
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        quay_length: SpaceLength,
        min_length: SpaceLength,
        max_length: SpaceLength,
        space_window_policy: SpaceWindowPolicy,
        amount_movables: usize,
        amount_fixed: usize,
        horizon: TimePoint<T>,
        lambda_per_time: f64,
        processing_time_sigma: f64,
        min_processing: TimeDelta<T>,
        max_processing: Option<TimeDelta<T>>,
        time_slack: TimeDelta<T>,
        fixed_gap: TimeDelta<T>,
        processing_mu_base: TimeDelta<T>,
        processing_mu_span: TimeDelta<T>,
        arrival_oversample_mult: usize,
        processing_sigma_floor: f64,
        length_span_epsilon: SpaceLength,
        cost_inc_num: C,
        cost_inc_den: C,
        min_cost_floor: C,
        window_split_left_num: SpaceLength,
        window_split_den: SpaceLength,
        base_cost_per_delay: C,
        base_cost_per_dev: C,
        seed: u64,
    ) -> Result<Self, QuayTooShortError> {
        let ord = min_length
            .partial_cmp(&max_length)
            .expect("Comparison of min_length and max_length failed");

        let (s, e) = match ord {
            Ordering::Greater => (max_length, min_length),
            _ => (min_length, max_length),
        };

        if quay_length < max_length {
            return Err(QuayTooShortError::new(quay_length, max_length));
        }

        Ok(Self {
            quay_length,
            min_ship_length: s,
            max_ship_length: e,
            space_window_policy,
            amount_movables,
            amount_fixed,
            horizon,
            lambda_per_time,
            processing_time_sigma,
            min_processing,
            max_processing,
            time_slack,
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
    pub fn amount_movables(&self) -> usize {
        self.amount_movables
    }

    #[inline]
    pub fn amount_fixed(&self) -> usize {
        self.amount_fixed
    }

    #[inline]
    pub fn horizon(&self) -> TimePoint<T> {
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
    pub fn min_processing(&self) -> TimeDelta<T> {
        self.min_processing
    }

    #[inline]
    pub fn max_processing(&self) -> Option<TimeDelta<T>> {
        self.max_processing
    }

    #[inline]
    pub fn time_slack(&self) -> TimeDelta<T> {
        self.time_slack
    }

    #[inline]
    pub fn fixed_gap(&self) -> TimeDelta<T> {
        self.fixed_gap
    }

    #[inline]
    pub fn seed(&self) -> u64 {
        self.seed
    }
}

impl<T, C> Display for InstanceGenConfig<T, C>
where
    T: PrimInt + Signed + NumCast + ToPrimitive + Display,
    C: PrimInt + Signed + NumCast + Copy + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let max_proc_str = match self.max_processing {
            Some(p) => format!("{}", p),
            None => "None".to_string(),
        };
        write!(
            f,
            "InstanceGenConfig {{ \
             quay_length: {}, min_length: {}, max_length: {}, space_window_policy: {}, \
             amount_movables: {}, amount_fixed: {}, horizon: {}, \
             lambda_per_time: {:.4}, processing_time_sigma: {:.4}, \
             min_processing: {}, max_processing: {}, time_slack: {}, fixed_gap: {}, \
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
            self.amount_movables,
            self.amount_fixed,
            self.horizon,
            self.lambda_per_time,
            self.processing_time_sigma,
            self.min_processing,
            max_proc_str,
            self.time_slack,
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

pub struct InstanceGenerator<T, C>
where
    T: PrimInt + Signed + NumCast + ToPrimitive + SampleUniform,
    C: PrimInt + Signed + NumCast + Copy,
{
    cfg: InstanceGenConfig<T, C>,
    rng: SmallRng,
    len_dist: Uniform<usize>,
    next_id: u64,
}

impl<T, C> InstanceGenerator<T, C>
where
    T: PrimInt + Signed + NumCast + ToPrimitive + Debug + SampleUniform,
    C: PrimInt + Signed + NumCast + Copy,
{
    pub fn new(cfg: InstanceGenConfig<T, C>) -> Self {
        let seed = cfg.seed();
        Self {
            len_dist: Uniform::new_inclusive(
                cfg.min_ship_length.value(),
                cfg.max_ship_length.value(),
            )
            .expect("valid [min_length, max_length]"),
            cfg,
            rng: SmallRng::seed_from_u64(seed),
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
    pub fn quay_end(&self) -> SpacePosition {
        SpacePosition::new(self.cfg.quay_length.value())
    }

    #[inline]
    pub fn max_start_pos(&self, length: SpaceLength) -> SpacePosition {
        self.quay_end() - length
    }

    pub fn generate(&mut self) -> Problem<T, C> {
        let total = self.cfg.amount_fixed + self.cfg.amount_movables;
        let arrivals = self.sample_arrivals(total);

        let mut builder = ProblemBuilder::<T, C>::new(self.cfg.quay_length);

        let mut fixed_indices: Vec<usize> = (0..self.cfg.amount_fixed).collect();
        fixed_indices.sort_by(|&a, &b| arrivals[a].cmp(&arrivals[b]));

        let fixed_asgs = self.plan_fixed(&fixed_indices, &arrivals);
        for asg in fixed_asgs {
            builder.add_preassigned(asg).expect("This should not fail");
        }

        for ix in self.cfg.amount_fixed..total {
            let req = self.sample_movable(arrivals[ix]);
            builder.add_movable_request(req).unwrap();
        }

        builder.build()
    }

    fn sample_arrivals(&mut self, n: usize) -> Vec<TimePoint<T>> {
        let mut out = Vec::with_capacity(n);
        let mut t_f = 0.0f64;

        if self.cfg.lambda_per_time > 0.0 {
            let exp = Exp::new(self.cfg.lambda_per_time).unwrap();
            for _ in 0..(n * self.cfg.arrival_oversample_mult) {
                t_f += exp.sample(&mut self.rng);
                let rounded = t_f.round() as i64;
                let t_val: T = NumCast::from(rounded.max(0)).expect("i64->T");
                let tp = TimePoint::new(t_val);
                if tp <= self.cfg.horizon {
                    out.push(tp);
                    if out.len() >= n {
                        break;
                    }
                } else {
                    break;
                }
            }
        }

        while out.len() < n {
            let t_val: T = self.rng.random_range(T::zero()..=self.cfg.horizon.value());
            out.push(TimePoint::new(t_val));
        }

        out.sort();
        out.truncate(n);
        out
    }

    #[inline]
    fn sample_length(&mut self) -> SpaceLength {
        SpaceLength::new(self.len_dist.sample(&mut self.rng))
    }

    #[inline]
    fn sample_target_position_for_length(&mut self, length: SpaceLength) -> SpacePosition {
        let max_start = self.cfg.quay_length.saturating_sub(length).value();
        let s = if max_start == 0 {
            0
        } else {
            self.rng.random_range(0..=max_start)
        };
        SpacePosition::new(s)
    }

    #[inline]
    fn length_span(&self) -> SpaceLength {
        let l0 = self.cfg.min_ship_length;
        let l1 = self.cfg.max_ship_length;
        let raw = l1.saturating_sub(l0);
        SpaceLength::new(raw.value().max(self.cfg.length_span_epsilon.value().max(1)))
    }

    fn processing_mean_from_length(&self, length: SpaceLength) -> f64 {
        let l = length;
        let l0 = self.cfg.min_ship_length;
        let span = self.length_span();

        let base = self.cfg.processing_mu_base;
        let span_add = self.cfg.processing_mu_span;
        let dx = l.saturating_sub(l0);

        let dx_f64: f64 = NumCast::from(dx.value()).expect("usize->f64");
        let span_f64: f64 = NumCast::from(span.value()).expect("usize->f64");
        let base_f64: f64 = NumCast::from(base.value()).expect("T->f64");
        let span_add_f64: f64 = NumCast::from(span_add.value()).expect("T->f64");

        base_f64 + (span_add_f64 * dx_f64) / span_f64
    }

    fn sample_processing(&mut self, length: SpaceLength) -> TimeDelta<T> {
        let mu = self.processing_mean_from_length(length);
        let sigma = self
            .cfg
            .processing_time_sigma
            .max(self.cfg.processing_sigma_floor);
        let n = Normal::new(mu, sigma).unwrap();
        let draw_f64 = n.sample(&mut self.rng).round();
        let draw_i64: i64 = NumCast::from(draw_f64).expect("f64->i64");

        let mut v: T = NumCast::from(draw_i64).expect("i64->T");
        if v < self.cfg.min_processing.value() {
            v = self.cfg.min_processing.value();
        }
        if let Some(maxp) = self.cfg.max_processing {
            if v > maxp.value() {
                v = maxp.value();
            }
        }
        TimeDelta::new(v)
    }

    fn length_scaled_costs(&self, length: SpaceLength) -> (Cost<C>, Cost<C>) {
        let l = length;
        let l0 = self.cfg.min_ship_length;
        let span = self.length_span();
        let dx = l.saturating_sub(l0);

        let span_c: C = NumCast::from(span.value()).expect("span usize -> C");
        let dx_c: C = NumCast::from(dx.value()).expect("dx usize -> C");
        let inc_num_c = self.cfg.cost_inc_num;
        let inc_den_c = self.cfg.cost_inc_den;

        let ramp_factor = (inc_num_c * dx_c) / (inc_den_c * span_c);

        let scale_and_floor = |base: C| -> Cost<C> {
            let mut val = base + base * ramp_factor;
            if val < self.cfg.min_cost_floor {
                val = self.cfg.min_cost_floor;
            }
            Cost::new(val)
        };

        (
            scale_and_floor(self.cfg.base_cost_per_delay),
            scale_and_floor(self.cfg.base_cost_per_dev),
        )
    }

    #[inline]
    fn split_left(&self, need: SpaceLength) -> SpaceLength {
        if self.cfg.window_split_den.is_zero() {
            return SpaceLength::zero();
        }
        let left_value = (need.value() * self.cfg.window_split_left_num.value())
            / self.cfg.window_split_den.value();
        SpaceLength::new(left_value)
    }

    fn space_window_for_movable(
        &self,
        target: SpacePosition,
        length: SpaceLength,
    ) -> SpaceInterval {
        match &self.cfg.space_window_policy {
            SpaceWindowPolicy::FullQuay => {
                SpaceInterval::new(SpacePosition::new(0), self.quay_end())
            }

            SpaceWindowPolicy::FixedHalfwidth(hw) => {
                self.fixed_halfwidth_window(target, length, *hw)
            }

            SpaceWindowPolicy::Relative(RelativeSpaceWindowPolicy {
                frac_of_length,
                min,
                max,
            }) => {
                let length_f64: f64 = NumCast::from(length.value()).expect("usize->f64");
                let hw_len_f64 = (*frac_of_length * length_f64).round();
                let hw_len: usize = NumCast::from(hw_len_f64).expect("f64->usize");
                let hw = SpaceLength::new(hw_len.clamp(min.value(), max.value()));
                self.fixed_halfwidth_window(target, length, hw)
            }

            SpaceWindowPolicy::MinMeasure(extra) => {
                let want = SpaceLength::new(length.value() + extra.value());
                self.min_measure_window(target, length, want)
            }
        }
    }

    fn space_window_for_fixed_assignment(
        &self,
        start_pos: SpacePosition,
        length: SpaceLength,
    ) -> SpaceInterval {
        match &self.cfg.space_window_policy {
            SpaceWindowPolicy::FullQuay => {
                SpaceInterval::new(SpacePosition::new(0), self.quay_end())
            }

            SpaceWindowPolicy::FixedHalfwidth(hw) => {
                self.fixed_halfwidth_window_containing_run(start_pos, length, *hw)
            }

            SpaceWindowPolicy::Relative(RelativeSpaceWindowPolicy {
                frac_of_length,
                min,
                max,
            }) => {
                let length_f64: f64 = NumCast::from(length.value()).expect("usize->f64");
                let hw_len_f64 = (*frac_of_length * length_f64).round();
                let hw_len: usize = NumCast::from(hw_len_f64).expect("f64->usize");
                let hw = SpaceLength::new(hw_len.clamp(min.value(), max.value()));
                self.fixed_halfwidth_window_containing_run(start_pos, length, hw)
            }

            SpaceWindowPolicy::MinMeasure(extra) => {
                let want = SpaceLength::new(length.value() + extra.value());
                self.min_measure_window_containing_run(start_pos, length, want)
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
        let mut lo = target.saturating_sub(halfwidth);
        let mut hi = (target + halfwidth).min(quay_end);

        if (hi - lo) < length {
            let need = length - (hi - lo);
            let add_l = self.split_left(need);
            let add_r = need - add_l;

            lo = lo.saturating_sub(add_l);
            hi = (hi + add_r).min(quay_end);

            if (hi - lo) < length {
                lo = SpacePosition::zero();
                hi = (lo + length).min(quay_end);
            }
        }

        SpaceInterval::new(lo, hi)
    }

    fn min_measure_window(
        &self,
        target: SpacePosition,
        length: SpaceLength,
        min_measure: SpaceLength,
    ) -> SpaceInterval {
        let need = if min_measure > length {
            min_measure
        } else {
            length
        };
        let quay_end = self.quay_end();

        let add_l = self.split_left(need);
        let lo = target.saturating_sub(add_l);
        let hi = (lo + need).min(quay_end);
        let lo = if (hi - lo) < need { hi - need } else { lo };

        SpaceInterval::new(lo, hi)
    }

    fn fixed_halfwidth_window_containing_run(
        &self,
        start_pos: SpacePosition,
        length: SpaceLength,
        halfwidth: SpaceLength,
    ) -> SpaceInterval {
        let quay_end = self.quay_end();
        let mut lo = start_pos.saturating_sub(halfwidth);
        let mut hi = (start_pos + length + halfwidth).min(quay_end);

        if (hi - lo) < length {
            hi = (lo + length).min(quay_end);
            lo = hi - length;
        }
        SpaceInterval::new(lo, hi)
    }

    fn min_measure_window_containing_run(
        &self,
        start_pos: SpacePosition,
        length: SpaceLength,
        min_measure: SpaceLength,
    ) -> SpaceInterval {
        let need = if min_measure > length {
            min_measure
        } else {
            length
        };
        let quay_end = self.quay_end();

        let extra = need - length;
        let add_l = self.split_left(extra);

        let lo = start_pos.saturating_sub(add_l);
        let lo = if lo > start_pos { start_pos } else { lo };
        let hi = (lo + need).min(quay_end);
        let lo = if (hi - lo) < need { hi - need } else { lo };

        SpaceInterval::new(lo, hi)
    }

    #[inline]
    fn time_window_containing(&self, start: TimePoint<T>, proc: TimeDelta<T>) -> TimeInterval<T> {
        let mut end = start + proc + self.cfg.time_slack;
        if end > self.cfg.horizon {
            end = self.cfg.horizon;
        }
        let min_end = start + proc;
        if end < min_end {
            end = min_end;
        }
        TimeInterval::new(start, end)
    }

    #[inline]
    fn time_window_from_arrival(
        &self,
        arrival: TimePoint<T>,
        proc: TimeDelta<T>,
    ) -> TimeInterval<T> {
        let min_end = arrival + proc;
        let mut end = min_end + self.cfg.time_slack;
        if end > self.cfg.horizon {
            end = self.cfg.horizon;
        }
        if end < min_end {
            end = min_end;
        }
        TimeInterval::new(arrival, end)
    }

    fn sample_movable(&mut self, arrival: TimePoint<T>) -> Request<Movable, T, C> {
        let length = self.sample_length();
        let proc = self.sample_processing(length);
        let target = self.sample_target_position_for_length(length);
        let (cpd, cdev) = self.length_scaled_costs(length);

        let tw = self.time_window_from_arrival(arrival, proc);
        let sw = self.space_window_for_movable(target, length);

        Request::<Movable, T, C>::new(self.fresh_id(), length, proc, target, cpd, cdev, tw, sw)
            .expect("movable: constructed request must be feasible")
    }

    fn plan_fixed(
        &mut self,
        fixed_sorted: &[usize],
        arrivals: &[TimePoint<T>],
    ) -> Vec<Assignment<Fixed, T, C>> {
        let mut out = Vec::with_capacity(fixed_sorted.len());
        let mut current_time = TimePoint::new(T::zero());

        for &ix in fixed_sorted.iter() {
            let length = self.sample_length();
            let proc = self.sample_processing(length);
            let target = self.sample_target_position_for_length(length);
            let (cpd, cdev) = self.length_scaled_costs(length);

            let arrival = arrivals[ix];
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

            let tw = self.time_window_containing(start, proc);
            let sw = self.space_window_for_fixed_assignment(start_pos, length);
            let req = Request::<Fixed, T, C>::new(
                self.fresh_id(),
                length,
                proc,
                target,
                cpd,
                cdev,
                tw,
                sw,
            )
            .expect("fixed: constructed request must be feasible");

            out.push(Assignment::new(req, start_pos, start));
            current_time = start + proc + self.cfg.fixed_gap;
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dock_alloc_core::domain::SpacePosition;

    type Tm = i64;
    type Cm = i64;

    fn cfg_relative(seed: u64) -> InstanceGenConfig<Tm, Cm> {
        InstanceGenConfig::new(
            SpaceLength::new(1_500), // quay_length
            SpaceLength::new(80),    // min_length
            SpaceLength::new(300),   // max_length
            SpaceWindowPolicy::Relative(RelativeSpaceWindowPolicy {
                frac_of_length: 0.75,
                min: SpaceLength::new(60),
                max: SpaceLength::new(250),
            }),
            25,                       // amount_movables
            5,                        // amount_fixed
            TimePoint::new(96),       // horizon
            0.9,                      // lambda_per_time
            2.5,                      // processing_time_sigma
            TimeDelta::new(4),        // min_processing
            Some(TimeDelta::new(72)), // max_processing
            TimeDelta::new(12),       // time_slack
            TimeDelta::new(2),        // fixed_gap
            TimeDelta::new(10),       // processing_mu_base
            TimeDelta::new(20),       // processing_mu_span
            6,                        // arrival_oversample_mult
            0.1,                      // processing_sigma_floor
            SpaceLength::new(1),      // length_span_epsilon
            1,                        // cost_inc_num (ramp up to +100% at max length)
            1,                        // cost_inc_den
            1,                        // min_cost_floor
            SpaceLength::new(1),      // window_split_left_num (50/50)
            SpaceLength::new(2),      // window_split_den
            2,                        // base_cost_per_delay
            1,                        // base_cost_per_dev
            seed,
        )
        .unwrap()
    }

    #[test]
    fn generate_shapes_and_counts() {
        let cfg = cfg_relative(42);
        let mut generator = InstanceGenerator::<Tm, Cm>::new(cfg.clone());
        let p: Problem<Tm, Cm> = generator.generate();

        assert_eq!(p.movables().len(), cfg.amount_movables());
        assert_eq!(p.preassigned().len(), cfg.amount_fixed());
        assert_eq!(
            p.total_requests(),
            cfg.amount_movables() + cfg.amount_fixed()
        );
        assert!(cfg.quay_length() >= cfg.max_length());
    }

    #[test]
    fn test_movable_requests_feasible() {
        let cfg = cfg_relative(123);
        let mut generator = InstanceGenerator::<Tm, Cm>::new(cfg.clone());
        let p = generator.generate();

        for r in p.iter_movable_requests() {
            assert!(r.length() >= cfg.min_length());
            assert!(r.length() <= cfg.max_length());
            assert!(r.feasible_time_window().duration() >= r.processing_duration());
            assert!(r.feasible_space_window().measure() >= r.length());
            let max_start_pos = SpacePosition::new(cfg.quay_length().value()) - r.length();
            assert!(r.target_position() <= max_start_pos);
        }
    }

    #[test]
    fn test_fixed_assignments_are_non_overlapping_in_time_and_within_quay() {
        let cfg = cfg_relative(777);
        let mut generator = InstanceGenerator::<Tm, Cm>::new(cfg.clone());
        let p = generator.generate();

        let mut spans: Vec<_> = p
            .iter_fixed_assignments()
            .map(|a| {
                let t0 = a.start_time();
                let t1 = t0 + a.request().processing_duration();
                let s0 = a.start_position();
                let s1 = s0 + a.request().length();
                (t0, t1, s0, s1, a)
            })
            .collect();

        spans.sort_by(|a, b| a.0.cmp(&b.0));

        let mut prev_end: Option<TimePoint<i64>> = None;
        let quay_end = SpacePosition::new(cfg.quay_length().value());
        for (t0, t1, s0, s1, a) in spans {
            if let Some(pe) = prev_end {
                assert!(t0 >= pe, "fixed assignments overlap in time");
            }
            prev_end = Some(t1);

            assert!(s0 <= quay_end);
            assert!(s1 <= quay_end);

            let tw = a.request().feasible_time_window();
            let sw = a.request().feasible_space_window();
            assert!(tw.contains(t0));
            assert!(tw.contains(t1) || t1 == tw.end());
            assert!(sw.contains(s0));
            assert!(sw.contains(s1) || s1 == sw.end());

            assert_eq!(a.request().length(), s1 - s0);
        }
    }

    #[test]
    fn costs_increase_with_length() {
        let cfg = cfg_relative(999);
        let generator = InstanceGenerator::<Tm, Cm>::new(cfg.clone());

        let (c_delay_min, c_dev_min) = generator.length_scaled_costs(cfg.min_length());
        let (c_delay_max, c_dev_max) = generator.length_scaled_costs(cfg.max_length());

        assert!(c_delay_max.value() >= c_delay_min.value());
        assert!(c_dev_max.value() >= c_dev_min.value());
        assert!(c_delay_max.value() > c_delay_min.value() || c_dev_max.value() > c_dev_min.value());
    }

    #[test]
    fn windows_match_policy_relative() {
        let cfg = cfg_relative(2024);
        let generator = InstanceGenerator::<Tm, Cm>::new(cfg.clone());

        let short = SpaceLength::new(cfg.min_length().value());
        let long = SpaceLength::new(cfg.max_length().value());

        let target = SpacePosition::new(200);

        let sw_short = generator.space_window_for_movable(target, short);
        let sw_long = generator.space_window_for_movable(target, long);

        assert!(sw_short.measure().value() >= short.value());
        assert!(sw_long.measure().value() >= long.value());
        assert!(sw_short.end().value() <= cfg.quay_length().value());
        assert!(sw_long.end().value() <= cfg.quay_length().value());
    }

    #[test]
    fn processing_is_clamped_between_min_and_max_if_present() {
        let cfg = InstanceGenConfig::new(
            SpaceLength::new(1_000),
            SpaceLength::new(80),
            SpaceLength::new(300),
            SpaceWindowPolicy::FullQuay,
            0,
            0,
            TimePoint::new(500),
            0.0,
            10.0,
            TimeDelta::new(20),       // min
            Some(TimeDelta::new(24)), // max
            TimeDelta::new(0),
            TimeDelta::new(0),
            TimeDelta::new(10),  // processing_mu_base
            TimeDelta::new(20),  // processing_mu_span
            6,                   // arrival_oversample_mult
            0.1,                 // processing_sigma_floor
            SpaceLength::new(1), // length_span_epsilon
            1,                   // cost_inc_num
            1,                   // cost_inc_den
            1_i64,               // min_cost_floor
            SpaceLength::new(1), // window_split_left_num
            SpaceLength::new(2), // window_split_den
            1_i64,               // base_cost_per_delay
            1_i64,               // base_cost_per_dev
            7,
        )
        .unwrap();

        let mut generator = InstanceGenerator::<Tm, Cm>::new(cfg);
        let len = SpaceLength::new(300);

        for _ in 0..100 {
            let d = generator.sample_processing(len);
            assert!(
                d.value() >= 20 && d.value() <= 24,
                "processing {:?} not clamped",
                d
            );
        }
    }
}
