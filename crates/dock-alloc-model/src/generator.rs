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
use dock_alloc_core::{
    cost::Cost,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimeInterval, TimePoint},
};
use num_traits::{NumCast, PrimInt, SaturatingAdd, SaturatingMul, Signed, ToPrimitive};
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

impl RelativeSpaceWindowPolicy {
    pub fn new(frac_of_length: f64, min: SpaceLength, max: SpaceLength) -> Self {
        Self {
            frac_of_length,
            min,
            max,
        }
    }
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
pub enum HalfwidthPolicy {
    Fixed(SpaceLength),
    Relative(RelativeSpaceWindowPolicy),
}

impl Display for HalfwidthPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HalfwidthPolicy::Fixed(hw) => write!(f, "HalfwidthPolicy::Fixed({})", hw),
            HalfwidthPolicy::Relative(r) => write!(f, "HalfwidthPolicy::Relative({})", r),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum SpaceWindowPolicy {
    Halfwidth(HalfwidthPolicy),
    FullQuay,
}

impl SpaceWindowPolicy {
    #[inline]
    pub fn full_quay() -> Self {
        Self::FullQuay
    }
    #[inline]
    pub fn fixed(hw: SpaceLength) -> Self {
        Self::Halfwidth(HalfwidthPolicy::Fixed(hw))
    }

    #[inline]
    pub fn relative(frac: f64, min: SpaceLength, max: SpaceLength) -> Self {
        Self::Halfwidth(HalfwidthPolicy::Relative(RelativeSpaceWindowPolicy::new(
            frac, min, max,
        )))
    }
}

impl Display for SpaceWindowPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpaceWindowPolicy::Halfwidth(hw) => write!(f, "Halfwidth({})", hw),
            SpaceWindowPolicy::FullQuay => write!(f, "FullQuay"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AroundArrivalTimeWindowPolicy<T: PrimInt + Signed> {
    before: TimeDelta<T>,
    after: TimeDelta<T>,
}

impl<T: PrimInt + Signed> AroundArrivalTimeWindowPolicy<T> {
    pub fn new(before: TimeDelta<T>, after: TimeDelta<T>) -> Self {
        Self { before, after }
    }

    #[inline]
    pub fn before(&self) -> TimeDelta<T> {
        self.before
    }

    #[inline]
    pub fn after(&self) -> TimeDelta<T> {
        self.after
    }
}

impl<T: PrimInt + Signed + Display> Display for AroundArrivalTimeWindowPolicy<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "AroundArrivalTimeWindowPolicy {{ before: {}, after: {} }}",
            self.before, self.after
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TimeWindowPolicy<T: PrimInt + Signed> {
    FullHorizon,
    AroundArrival(AroundArrivalTimeWindowPolicy<T>),
}

impl<T: PrimInt + Signed> TimeWindowPolicy<T> {
    #[inline]
    pub fn full_horizon() -> Self {
        Self::FullHorizon
    }

    #[inline]
    pub fn around_arrival(before: TimeDelta<T>, after: TimeDelta<T>) -> Self {
        Self::AroundArrival(AroundArrivalTimeWindowPolicy::new(before, after))
    }
}

impl<T: PrimInt + Signed + Display> Display for TimeWindowPolicy<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TimeWindowPolicy::FullHorizon => write!(f, "FullHorizon"),
            TimeWindowPolicy::AroundArrival(p) => {
                write!(f, "AroundArrival({})", p)
            }
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

    /// Policy for how to construct **space windows** (allowed berth intervals).
    ///
    /// Supported:
    /// - `FullQuay`: use the entire quay `[0, quay_length]`.
    /// - `Halfwidth(HalfwidthPolicy)`: window derived from a half-width,
    ///   either `Fixed(hw)` or `Relative { frac_of_length, min, max }`.
    ///
    /// The generator ensures the final window lies within the quay and can hold the ship.
    space_window_policy: SpaceWindowPolicy,

    /// Policy for how to construct **time windows** (allowed time intervals)
    /// for movable requests.
    time_window_policy: TimeWindowPolicy<T>,

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
    cost_inc_num: Cost<C>,

    /// Denominator for the **length-based cost ramp**.
    ///
    /// Larger `cost_inc_den` means a gentler ramp; smaller means steeper.
    cost_inc_den: Cost<C>,

    /// Minimum allowed **final cost** after scaling.
    ///
    /// After applying the ramp to a base cost, we clamp it up to this floor.
    min_cost_floor: Cost<C>,

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
    base_cost_per_delay: Cost<C>,

    /// **Base unit cost** per unit of **spatial deviation** (before ramp).
    ///
    /// Like delay cost, this is scaled by the same length-based ramp and
    /// then floored by `min_cost_floor`.
    base_cost_per_dev: Cost<C>,

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
        time_window_policy: TimeWindowPolicy<T>,
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
        cost_inc_num: Cost<C>,
        cost_inc_den: Cost<C>,
        min_cost_floor: Cost<C>,
        window_split_left_num: SpaceLength,
        window_split_den: SpaceLength,
        base_cost_per_delay: Cost<C>,
        base_cost_per_dev: Cost<C>,
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
            time_window_policy,
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
    pub fn time_window_policy(&self) -> &TimeWindowPolicy<T> {
        &self.time_window_policy
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
             time_window_policy: {}, amount_movables: {}, amount_fixed: {}, horizon: {}, \
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
            self.time_window_policy,
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

/// Builder for `InstanceGenConfig`
///
/// Defaults chosen to be reasonable for experimentation; adjust as needed.
/// Required before `build()`:
/// - quay_length
/// - min_length, max_length
/// - horizon
/// - space_window_policy
/// - time_window_policy
/// - amount_movables, amount_fixed
pub struct InstanceGenConfigBuilder<T, C>
where
    T: PrimInt + Signed + NumCast + ToPrimitive,
    C: PrimInt + Signed + NumCast + Copy,
{
    // Required
    quay_length: Option<SpaceLength>,
    min_length: Option<SpaceLength>,
    max_length: Option<SpaceLength>,
    horizon: Option<TimePoint<T>>,
    space_window_policy: Option<SpaceWindowPolicy>,
    time_window_policy: Option<TimeWindowPolicy<T>>,
    amount_movables: Option<usize>,
    amount_fixed: Option<usize>,

    // Optional with defaults
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
    cost_inc_num: Cost<C>,
    cost_inc_den: Cost<C>,
    min_cost_floor: Cost<C>,
    window_split_left_num: SpaceLength,
    window_split_den: SpaceLength,
    base_cost_per_delay: Cost<C>,
    base_cost_per_dev: Cost<C>,
    seed: u64,
}

impl<T, C> Default for InstanceGenConfigBuilder<T, C>
where
    T: PrimInt + Signed + NumCast + ToPrimitive,
    C: PrimInt + Signed + NumCast + Copy,
{
    fn default() -> Self {
        // Small helpers to construct generic numeric wrappers from i64
        fn to_td<T: PrimInt + Signed + NumCast>(v: i64) -> TimeDelta<T> {
            TimeDelta::new(NumCast::from(v).expect("NumCast<i64 -> T>"))
        }
        fn to_sl(v: usize) -> SpaceLength {
            SpaceLength::new(v)
        }
        fn to_cost<C: PrimInt + Signed + NumCast + Copy>(v: i64) -> Cost<C> {
            Cost::new(NumCast::from(v).expect("NumCast<i64 -> C>"))
        }

        let seed = rand::rng().random();

        Self {
            // required -> None
            quay_length: None,
            min_length: None,
            max_length: None,
            horizon: None,
            space_window_policy: None,
            time_window_policy: None,
            amount_movables: None,
            amount_fixed: None,

            // optional defaults
            lambda_per_time: 0.9,
            processing_time_sigma: 2.5,
            min_processing: to_td(4),
            max_processing: Some(to_td(72)),
            time_slack: to_td(12),
            fixed_gap: to_td(2),
            processing_mu_base: to_td(10),
            processing_mu_span: to_td(20),
            arrival_oversample_mult: 6,
            processing_sigma_floor: 0.1,
            length_span_epsilon: to_sl(1),
            cost_inc_num: to_cost(1), // linear ramp up to +100% at max length when den=1
            cost_inc_den: to_cost(1),
            min_cost_floor: to_cost(1),
            window_split_left_num: to_sl(1), // 50/50 split
            window_split_den: to_sl(2),
            base_cost_per_delay: to_cost(2),
            base_cost_per_dev: to_cost(1),
            seed,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstanceGenConfigBuildError {
    QuayTooShort(QuayTooShortError),
    MissingQuayLength,
    MissingMinLength,
    MissingMaxLength,
    MissingHorizon,
    MissingSpaceWindowPolicy,
    MissingTimeWindowPolicy,
    MissingAmountMovables,
    MissingAmountFixed,
}

impl Display for InstanceGenConfigBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstanceGenConfigBuildError::QuayTooShort(e) => write!(f, "{}", e),
            InstanceGenConfigBuildError::MissingQuayLength => write!(f, "Missing quay_length"),
            InstanceGenConfigBuildError::MissingMinLength => write!(f, "Missing min_length"),
            InstanceGenConfigBuildError::MissingMaxLength => write!(f, "Missing max_length"),
            InstanceGenConfigBuildError::MissingHorizon => write!(f, "Missing horizon"),
            InstanceGenConfigBuildError::MissingSpaceWindowPolicy => {
                write!(f, "Missing space_window_policy")
            }
            InstanceGenConfigBuildError::MissingTimeWindowPolicy => {
                write!(f, "Missing time_window_policy")
            }
            InstanceGenConfigBuildError::MissingAmountMovables => {
                write!(f, "Missing amount_movables")
            }
            InstanceGenConfigBuildError::MissingAmountFixed => {
                write!(f, "Missing amount_fixed")
            }
        }
    }
}

impl From<QuayTooShortError> for InstanceGenConfigBuildError {
    fn from(e: QuayTooShortError) -> Self {
        InstanceGenConfigBuildError::QuayTooShort(e)
    }
}

impl std::error::Error for InstanceGenConfigBuildError {}

impl<T, C> InstanceGenConfigBuilder<T, C>
where
    T: PrimInt + Signed + NumCast + ToPrimitive,
    C: PrimInt + Signed + NumCast + Copy,
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
    pub fn horizon(mut self, v: TimePoint<T>) -> Self {
        self.horizon = Some(v);
        self
    }

    #[inline]
    pub fn space_policy_full_quay(mut self) -> Self {
        self.space_window_policy = Some(SpaceWindowPolicy::full_quay());
        self
    }

    #[inline]
    pub fn space_policy_fixed(mut self, hw: SpaceLength) -> Self {
        self.space_window_policy = Some(SpaceWindowPolicy::fixed(hw));
        self
    }

    #[inline]
    pub fn space_policy_relative(mut self, frac: f64, min: SpaceLength, max: SpaceLength) -> Self {
        self.space_window_policy = Some(SpaceWindowPolicy::relative(frac, min, max));
        self
    }

    #[inline]
    pub fn time_policy_full_horizon(mut self) -> Self {
        self.time_window_policy = Some(TimeWindowPolicy::full_horizon());
        self
    }

    #[inline]
    pub fn time_policy_around_arrival(mut self, before: TimeDelta<T>, after: TimeDelta<T>) -> Self {
        self.time_window_policy = Some(TimeWindowPolicy::around_arrival(before, after));
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
    pub fn min_processing(mut self, v: TimeDelta<T>) -> Self {
        self.min_processing = v;
        self
    }

    #[inline]
    pub fn max_processing(mut self, v: Option<TimeDelta<T>>) -> Self {
        self.max_processing = v;
        self
    }

    #[inline]
    pub fn time_slack(mut self, v: TimeDelta<T>) -> Self {
        self.time_slack = v;
        self
    }

    #[inline]
    pub fn fixed_gap(mut self, v: TimeDelta<T>) -> Self {
        self.fixed_gap = v;
        self
    }

    #[inline]
    pub fn processing_mu_base(mut self, v: TimeDelta<T>) -> Self {
        self.processing_mu_base = v;
        self
    }

    #[inline]
    pub fn processing_mu_span(mut self, v: TimeDelta<T>) -> Self {
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
    pub fn cost_inc_num(mut self, v: Cost<C>) -> Self {
        self.cost_inc_num = v;
        self
    }

    #[inline]
    pub fn cost_inc_den(mut self, v: Cost<C>) -> Self {
        self.cost_inc_den = v;
        self
    }

    #[inline]
    pub fn min_cost_floor(mut self, v: Cost<C>) -> Self {
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
    pub fn base_cost_per_delay(mut self, v: Cost<C>) -> Self {
        self.base_cost_per_delay = v;
        self
    }

    #[inline]
    pub fn base_cost_per_dev(mut self, v: Cost<C>) -> Self {
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

    pub fn build(self) -> Result<InstanceGenConfig<T, C>, InstanceGenConfigBuildError> {
        let quay_length = self
            .quay_length
            .ok_or(InstanceGenConfigBuildError::MissingQuayLength)?;
        let min_length = self
            .min_length
            .ok_or(InstanceGenConfigBuildError::MissingMinLength)?;
        let max_length = self
            .max_length
            .ok_or(InstanceGenConfigBuildError::MissingMaxLength)?;
        let horizon = self
            .horizon
            .ok_or(InstanceGenConfigBuildError::MissingHorizon)?;
        let space_window_policy = self
            .space_window_policy
            .ok_or(InstanceGenConfigBuildError::MissingSpaceWindowPolicy)?;
        let time_window_policy = self
            .time_window_policy
            .ok_or(InstanceGenConfigBuildError::MissingTimeWindowPolicy)?;
        let amount_movables = self
            .amount_movables
            .ok_or(InstanceGenConfigBuildError::MissingAmountMovables)?;
        let amount_fixed = self
            .amount_fixed
            .ok_or(InstanceGenConfigBuildError::MissingAmountFixed)?;
        Ok(InstanceGenConfig::new(
            quay_length,
            min_length,
            max_length,
            space_window_policy,
            time_window_policy,
            amount_movables,
            amount_fixed,
            horizon,
            self.lambda_per_time,
            self.processing_time_sigma,
            self.min_processing,
            self.max_processing,
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
            self.seed,
        )?)
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

impl<T, C> From<InstanceGenConfig<T, C>> for InstanceGenerator<T, C>
where
    T: PrimInt + Signed + NumCast + ToPrimitive + Debug + SampleUniform,
    C: PrimInt + Signed + NumCast + Copy + SaturatingAdd + SaturatingMul,
{
    fn from(cfg: InstanceGenConfig<T, C>) -> Self {
        Self::new(cfg)
    }
}

impl<T, C> InstanceGenerator<T, C>
where
    T: PrimInt + Signed + NumCast + ToPrimitive + Debug + SampleUniform,
    C: PrimInt + Signed + NumCast + Copy + SaturatingAdd + SaturatingMul,
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

    #[inline]
    fn halfwidth_for(&self, length: SpaceLength) -> Option<SpaceLength> {
        match &self.cfg.space_window_policy {
            SpaceWindowPolicy::FullQuay => None,
            SpaceWindowPolicy::Halfwidth(hp) => match hp {
                HalfwidthPolicy::Fixed(hw) => Some(*hw),
                HalfwidthPolicy::Relative(RelativeSpaceWindowPolicy {
                    frac_of_length,
                    min,
                    max,
                }) => {
                    let length_f64: f64 = NumCast::from(length.value()).expect("usize->f64");
                    let hw_len_f64 = (*frac_of_length * length_f64).round();
                    let hw_len: usize = NumCast::from(hw_len_f64).expect("f64->usize");
                    Some(SpaceLength::new(hw_len.clamp(min.value(), max.value())))
                }
            },
        }
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

        for time_point in arrivals
            .iter()
            .take(total)
            .skip(self.cfg.amount_fixed)
            .copied()
        {
            let req = self.sample_movable(time_point);
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
        if let Some(maxp) = self.cfg.max_processing
            && v > maxp.value()
        {
            v = maxp.value();
        }
        TimeDelta::new(v)
    }

    fn length_scaled_costs(&self, length: SpaceLength) -> (Cost<C>, Cost<C>) {
        let length_delta = length.saturating_sub(self.cfg.min_ship_length);
        let length_span = self.length_span();
        let span_scalar: C = NumCast::from(length_span.value()).expect("span usize -> C");
        let delta_scalar: C = NumCast::from(length_delta.value()).expect("delta usize -> C");
        let increment_cost = self.cfg.cost_inc_num * delta_scalar;
        let base_cost = self.cfg.cost_inc_den * span_scalar;

        let scaling_factor: C = increment_cost.ratio(base_cost).unwrap_or(C::zero());

        let scale_cost = |base: Cost<C>| -> Cost<C> {
            let scaled = base.saturating_add(base.saturating_mul(scaling_factor));
            scaled.max(self.cfg.min_cost_floor)
        };

        (
            scale_cost(self.cfg.base_cost_per_delay),
            scale_cost(self.cfg.base_cost_per_dev),
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

    fn space_window_for_fixed_assignment(
        &self,
        start_pos: SpacePosition,
        length: SpaceLength,
    ) -> SpaceInterval {
        match &self.cfg.space_window_policy {
            SpaceWindowPolicy::FullQuay => {
                SpaceInterval::new(SpacePosition::new(0), self.quay_end())
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

    fn space_window_for_movable(
        &self,
        target: SpacePosition,
        length: SpaceLength,
    ) -> SpaceInterval {
        match &self.cfg.space_window_policy {
            SpaceWindowPolicy::FullQuay => {
                SpaceInterval::new(SpacePosition::new(0), self.quay_end())
            }
            SpaceWindowPolicy::Halfwidth(_) => {
                let hw = self.halfwidth_for(length).expect("halfwidth required");
                self.fixed_halfwidth_window(target, length, hw)
            }
        }
    }

    fn time_window_from_arrival(
        &self,
        arrival: TimePoint<T>,
        proc: TimeDelta<T>,
    ) -> TimeInterval<T> {
        match &self.cfg.time_window_policy {
            TimeWindowPolicy::FullHorizon => {
                let latest_start = self.cfg.horizon.saturating_sub(proc);
                TimeInterval::new(TimePoint::zero(), latest_start + proc)
            }
            TimeWindowPolicy::AroundArrival(policy) => {
                let start = arrival.saturating_sub(policy.before());
                let min_end = arrival + proc;
                let mut end = min_end + policy.after();
                if end > self.cfg.horizon {
                    end = self.cfg.horizon;
                }
                if end < min_end {
                    end = min_end;
                }
                TimeInterval::new(start, end)
            }
        }
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
    use dock_alloc_core::space::SpacePosition;

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
            TimeWindowPolicy::AroundArrival(AroundArrivalTimeWindowPolicy::new(
                8.into(),
                48.into(),
            )),
            25,
            5,
            TimePoint::new(96),
            0.9,
            2.5,
            TimeDelta::new(4),
            Some(TimeDelta::new(72)),
            TimeDelta::new(12),
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
            TimeWindowPolicy::FullHorizon,
            0,
            0,
            TimePoint::new(500),
            0.0,
            10.0,
            TimeDelta::new(20),
            Some(TimeDelta::new(24)),
            TimeDelta::new(0),
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

    #[test]
    fn test_time_window_policies() {
        // Test FullHorizon policy
        let cfg_full = InstanceGenConfig::new(
            SpaceLength::new(1_000),
            SpaceLength::new(80),
            SpaceLength::new(300),
            SpaceWindowPolicy::FullQuay,
            TimeWindowPolicy::FullHorizon,
            5,
            0,
            TimePoint::new(100),
            0.0,
            2.0,
            TimeDelta::new(10),
            Some(TimeDelta::new(20)),
            TimeDelta::new(5),
            TimeDelta::new(2),
            TimeDelta::new(10),
            TimeDelta::new(5),
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
            123,
        )
        .unwrap();

        let mut generator_full = InstanceGenerator::<Tm, Cm>::new(cfg_full);
        let problem_full = generator_full.generate();

        for request in problem_full.iter_movable_requests() {
            let tw = request.feasible_time_window();
            assert_eq!(tw.start(), TimePoint::new(0));
            // Window should be large enough for the ship to complete
            assert!(tw.duration() >= request.processing_duration());
        }
    }
}
