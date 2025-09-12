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
    SolverVariable,
    cost::Cost,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimePoint},
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
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
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
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HalfwidthPolicy::Fixed(halfwidth) => {
                write!(formatter, "HalfwidthPolicy::Fixed({})", halfwidth)
            }
            HalfwidthPolicy::Relative(relative_policy) => {
                write!(formatter, "HalfwidthPolicy::Relative({})", relative_policy)
            }
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
    pub fn fixed(halfwidth: SpaceLength) -> Self {
        Self::Halfwidth(HalfwidthPolicy::Fixed(halfwidth))
    }

    #[inline]
    pub fn relative(frac: f64, min: SpaceLength, max: SpaceLength) -> Self {
        Self::Halfwidth(HalfwidthPolicy::Relative(RelativeSpaceWindowPolicy::new(
            frac, min, max,
        )))
    }
}

impl Display for SpaceWindowPolicy {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpaceWindowPolicy::Halfwidth(halfwidth_policy) => {
                write!(formatter, "Halfwidth({})", halfwidth_policy)
            }
            SpaceWindowPolicy::FullQuay => write!(formatter, "FullQuay"),
        }
    }
}

/// Configuration for generating synthetic berth-allocation instances
/// in **realistic terminal units**:
///
/// - **Time unit:** 1 tick = **1 minute**
/// - **Space unit:** **meter**
///
/// ### What the *defaults* imply (see `Default` impl below)
/// - **Quay:** 2,400 m face; ships between **140–400 m**.
/// - **Horizon:** **3 days** (4,320 min).
/// - **Arrivals:** ~**1 ship/hour** on average (Poisson) → realistic **bursts and gaps**.
/// - **Processing durations:** small ships around **8 h**, largest around **24 h**,
///   clamped to **3–30 h**.
/// - **Movables:** space windows centered by half-width policy (relative to ship size).
/// - **Fixeds:** never overlap; **30 min** buffer between starts.
///
/// Use this to generate datasets that “feel” like a large port’s day-to-day flow.
#[derive(Debug, Clone, PartialEq)]
pub struct InstanceGenConfig<TimePrimitive, CostPrimitive>
where
    TimePrimitive: PrimInt + Signed + NumCast + ToPrimitive,
    CostPrimitive: PrimInt + Signed + NumCast + Copy,
{
    /// **Usable quay length** in meters. All berths/placements must lie within `[0, quay_length]`.
    /// Larger values allow more/larger ships to be present concurrently along the quay face.
    quay_length: SpaceLength,

    /// **Smallest ship LOA** (meters) seen in the mix. Controls the low end of length sampling
    /// and anchors the “short ship” side of processing-time means and cost scaling.
    min_ship_length: SpaceLength,

    /// **Largest ship LOA** (meters). Must be `<= quay_length`.
    /// Drives the “long ship” end of processing-time means and cost scaling.
    max_ship_length: SpaceLength,

    /// **How wide a ship’s allowed berthing interval is** (its feasible space window).
    /// - `FullQuay`: anywhere along the quay.
    /// - `Halfwidth`: window centered around a target (movables) or containing the fixed run,
    ///   with half-width either fixed or **relative to ship length** (longer ships → wider windows).
    ///
    /// If the window is too narrow to fit the ship, it is expanded within quay bounds.
    space_window_policy: SpaceWindowPolicy,

    /// **How many movable requests** to generate. These arrive over time with feasible time/space
    /// windows and a target position but no fixed start; the solver must place them.
    amount_movables: usize,

    /// **How many fixed assignments** to generate. These are pre-planned runs with concrete
    /// start time and position. They never overlap in time and sit inside their windows/quay.
    amount_fixed: usize,

    /// **End of the planning horizon** (minutes). All arrivals and time-window ends are clamped
    /// to this point. Think of this as “we plan for the next N minutes.”
    horizon: TimePoint<TimePrimitive>,

    /// **Average arrival rate per minute** (λ). We simulate a **Poisson process**:
    /// inter-arrival times are exponential. Real-world effect: **bursty** sequences (several ships
    /// in quick succession) interleaved with **quiet gaps**—not evenly spaced arrivals.
    lambda_per_time: f64,

    /// **Spread (σ) of processing times** around the mean (in minutes).
    /// Higher values make durations more variable; a small safety floor is applied so the
    /// distribution never becomes nearly deterministic.
    processing_time_sigma: f64,

    /// **Minimum allowed processing duration** (minutes) after sampling.
    /// Models that a call can’t be unrealistically short even if the draw says so.
    min_processing: TimeDelta<TimePrimitive>,

    /// **Maximum allowed processing duration** (minutes) after sampling. `None` = no hard cap.
    /// Use to bound extreme tails (e.g., operational constraints, shift limits).
    max_processing: Option<TimeDelta<TimePrimitive>>,

    /// **Idle time between fixed assignments** (minutes). Ensures fixeds never overlap;
    /// with `fixed_gap = 30` you get at least a 30-minute buffer before the next fixed can start.
    fixed_gap: TimeDelta<TimePrimitive>,

    /// **Base (short-ship) mean processing time** (minutes). A 140 m ship will hover around this
    /// mean before adding length effects.
    processing_mu_base: TimeDelta<TimePrimitive>,

    /// **Additional mean for the longest ship** (minutes). The mean grows linearly from
    /// `processing_mu_base` at `min_ship_length` to `base + span` at `max_ship_length`.
    /// Real-world effect: larger ships get **longer average service**.
    processing_mu_span: TimeDelta<TimePrimitive>,

    /// **How many exponential draws we attempt** relative to the total number of ships.
    /// Larger values make it more likely that enough Poisson arrivals fall **inside the horizon**
    /// before we top up uniformly.
    arrival_oversample_mult: usize,

    /// **Lower bound on σ** for processing times. Prevents “degenerate” near-zero variance
    /// if someone sets `processing_time_sigma` tiny.
    processing_sigma_floor: f64,

    /// **Safety minimum for length spans** (meters). If min = max length, we still treat the
    /// span as at least this value to avoid divide-by-zero in length-based formulas.
    length_span_epsilon: SpaceLength,

    /// **Numerator** of the length-based **cost ramp**. Longer ships pay more per unit of delay/dev.
    /// This tunes how steeply per-unit costs grow from small to large ships.
    cost_inc_num: Cost<CostPrimitive>,

    /// **Denominator** of the cost ramp. Larger denominator → gentler growth.
    cost_inc_den: Cost<CostPrimitive>,

    /// **Per-unit cost floor** after ramping. Ensures neither delay nor deviation becomes “free”
    /// due to scaling.
    min_cost_floor: Cost<CostPrimitive>,

    /// **How we split extra space when a window is too narrow**: fraction added to the **left**.
    /// With `1/2`, the expansion is 50/50 left/right; with `0/1`, all added to the right.
    window_split_left_num: SpaceLength,

    /// **Split denominator** for the left/right expansion fraction (see above).
    window_split_den: SpaceLength,

    /// **Base per-minute cost of waiting** (before length ramp). Real-world: queueing, tug,
    /// crane readiness, and knock-on schedule effects—delay is often the dominant penalty.
    base_cost_per_delay: Cost<CostPrimitive>,

    /// **Base per-meter cost of spatial deviation** (before length ramp). Real-world: being off the
    /// target berth may induce extra crane travel or internal transport inefficiency.
    base_cost_per_dev: Cost<CostPrimitive>,

    /// **RNG seed** for reproducible instance generation. Fix this to get identical datasets
    /// from run to run; change it for fresh draws with the same configuration.
    seed: u64,
}

impl<T, C> Default for InstanceGenConfig<T, C>
where
    T: SolverVariable + NumCast + ToPrimitive,
    C: SolverVariable + NumCast + Copy,
{
    fn default() -> Self {
        // Helpers to construct typed wrappers from integer literals.
        #[inline]
        fn to_t<T: SolverVariable + NumCast>(v: i64) -> T {
            NumCast::from(v).expect("NumCast<i64 -> T>")
        }
        #[inline]
        fn td<T: SolverVariable + NumCast>(v: i64) -> TimeDelta<T> {
            TimeDelta::new(to_t::<T>(v))
        }
        #[inline]
        fn tp<T: SolverVariable + NumCast>(v: i64) -> TimePoint<T> {
            TimePoint::new(to_t::<T>(v))
        }
        #[inline]
        fn cost<C: SolverVariable + NumCast + Copy>(v: i64) -> Cost<C> {
            Cost::new(NumCast::from(v).expect("NumCast<i64 -> C>"))
        }

        let quay_length = SpaceLength::new(1000); // large quay face
        let min_len = SpaceLength::new(140); // feeder / small container ship
        let max_len = SpaceLength::new(400); // Panamax/Neo-Panamax
        //let seed = rand::rng().random();
        let seed = 42; // fixed seed for reproducibility

        Self {
            // Geometry
            quay_length,
            min_ship_length: min_len,
            max_ship_length: max_len,

            // Space windows: relative half-width (≈ 0.75 * LOA), clamped to [80 m, 600 m]
            space_window_policy: SpaceWindowPolicy::Halfwidth(HalfwidthPolicy::Relative(
                RelativeSpaceWindowPolicy::new(0.75, SpaceLength::new(80), SpaceLength::new(600)),
            )),

            // Mix
            amount_movables: 70,
            amount_fixed: 5,

            // Horizon: 300 days
            horizon: tp::<T>(11520),

            // Arrivals: ≈ 1 ship/hour (Poisson → bursts + gaps)
            lambda_per_time: 0.017,
            arrival_oversample_mult: 6,

            // Processing times (minutes): ~8 h (small) → ~24 h (large), with realistic spread
            processing_time_sigma: 45.0,
            processing_sigma_floor: 10.0,
            min_processing: td::<T>(180),         // ≥ 3 h
            max_processing: Some(td::<T>(1_800)), // ≤ 30 h
            processing_mu_base: td::<T>(480),     // 8 h
            processing_mu_span: td::<T>(960),     // +16 h across min→max LOA

            // Fixed runs: non-overlap with a small real-world buffer
            fixed_gap: td::<T>(30), // 30 min between fixed starts

            // Space window expansion and span safety
            window_split_left_num: SpaceLength::new(1), // 50/50 left-right expansion
            window_split_den: SpaceLength::new(2),
            length_span_epsilon: SpaceLength::new(1),

            // Costs (per minute / per meter), length-ramped
            base_cost_per_delay: cost::<C>(5), // waiting is expensive
            base_cost_per_dev: cost::<C>(1),   // spatial deviation matters less
            cost_inc_num: cost::<C>(1),        // linear ramp with LOA
            cost_inc_den: cost::<C>(1),
            min_cost_floor: cost::<C>(1),

            seed,
        }
    }
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
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "QuayTooShortError: quay_length {} is shorter than max ship length {}",
            self.quay_length, self.max_ship_length
        )
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
        let order = unord_min_length
            .partial_cmp(&unord_max_length)
            .expect("Comparison of min_length and max_length failed");

        let (min_ship_length, max_ship_length) = match order {
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
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let max_proc_str = match self.max_processing {
            Some(p) => format!("{}", p),
            None => "None".to_string(),
        };
        write!(
            formatter,
            "InstanceGenConfig {{ \
              quay_length: {}, min_length: {}, max_length: {}, space_window_policy: {}, \
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
        // Small helpers to construct generic numeric wrappers from i64
        fn to_time_delta<T: SolverVariable + NumCast>(value: i64) -> TimeDelta<T> {
            TimeDelta::new(NumCast::from(value).expect("NumCast<i64 -> T>"))
        }
        fn to_space_length(value: usize) -> SpaceLength {
            SpaceLength::new(value)
        }
        fn to_cost<C: SolverVariable + NumCast + Copy>(value: i64) -> Cost<C> {
            Cost::new(NumCast::from(value).expect("NumCast<i64 -> C>"))
        }

        let seed = rand::rng().random();

        Self {
            // required -> None
            quay_length: None,
            min_length: None,
            max_length: None,
            horizon: None,
            space_window_policy: None,
            amount_movables: None,
            amount_fixed: None,

            // optional defaults
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
            cost_inc_num: to_cost(1), // linear ramp up to +100% at max length when den=1
            cost_inc_den: to_cost(1),
            min_cost_floor: to_cost(1),
            window_split_left_num: to_space_length(1), // 50/50 split
            window_split_den: to_space_length(2),
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
    MissingAmountMovables,
    MissingAmountFixed,
}

impl Display for InstanceGenConfigBuildError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstanceGenConfigBuildError::QuayTooShort(error) => write!(formatter, "{}", error),
            InstanceGenConfigBuildError::MissingQuayLength => {
                write!(formatter, "Missing quay_length")
            }
            InstanceGenConfigBuildError::MissingMinLength => {
                write!(formatter, "Missing min_length")
            }
            InstanceGenConfigBuildError::MissingMaxLength => {
                write!(formatter, "Missing max_length")
            }
            InstanceGenConfigBuildError::MissingHorizon => write!(formatter, "Missing horizon"),
            InstanceGenConfigBuildError::MissingSpaceWindowPolicy => {
                write!(formatter, "Missing space_window_policy")
            }
            InstanceGenConfigBuildError::MissingAmountMovables => {
                write!(formatter, "Missing amount_movables")
            }
            InstanceGenConfigBuildError::MissingAmountFixed => {
                write!(formatter, "Missing amount_fixed")
            }
        }
    }
}

impl From<QuayTooShortError> for InstanceGenConfigBuildError {
    fn from(error: QuayTooShortError) -> Self {
        InstanceGenConfigBuildError::QuayTooShort(error)
    }
}

impl std::error::Error for InstanceGenConfigBuildError {}

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
    pub fn quay_length(mut self, value: SpaceLength) -> Self {
        self.quay_length = Some(value);
        self
    }

    #[inline]
    pub fn min_length(mut self, value: SpaceLength) -> Self {
        self.min_length = Some(value);
        self
    }

    #[inline]
    pub fn max_length(mut self, value: SpaceLength) -> Self {
        self.max_length = Some(value);
        self
    }

    #[inline]
    pub fn horizon(mut self, value: TimePoint<TimePrimitive>) -> Self {
        self.horizon = Some(value);
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

    #[inline]
    pub fn amount_movables(mut self, value: usize) -> Self {
        self.amount_movables = Some(value);
        self
    }

    #[inline]
    pub fn amount_fixed(mut self, value: usize) -> Self {
        self.amount_fixed = Some(value);
        self
    }

    #[inline]
    pub fn lambda_per_time(mut self, value: f64) -> Self {
        self.lambda_per_time = value;
        self
    }

    #[inline]
    pub fn processing_time_sigma(mut self, value: f64) -> Self {
        self.processing_time_sigma = value;
        self
    }

    #[inline]
    pub fn min_processing(mut self, value: TimeDelta<TimePrimitive>) -> Self {
        self.min_processing = value;
        self
    }

    #[inline]
    pub fn max_processing(mut self, value: Option<TimeDelta<TimePrimitive>>) -> Self {
        self.max_processing = value;
        self
    }

    #[inline]
    pub fn fixed_gap(mut self, value: TimeDelta<TimePrimitive>) -> Self {
        self.fixed_gap = value;
        self
    }

    #[inline]
    pub fn processing_mu_base(mut self, value: TimeDelta<TimePrimitive>) -> Self {
        self.processing_mu_base = value;
        self
    }

    #[inline]
    pub fn processing_mu_span(mut self, value: TimeDelta<TimePrimitive>) -> Self {
        self.processing_mu_span = value;
        self
    }

    #[inline]
    pub fn arrival_oversample_mult(mut self, value: usize) -> Self {
        self.arrival_oversample_mult = value;
        self
    }

    #[inline]
    pub fn processing_sigma_floor(mut self, value: f64) -> Self {
        self.processing_sigma_floor = value;
        self
    }

    #[inline]
    pub fn length_span_epsilon(mut self, value: SpaceLength) -> Self {
        self.length_span_epsilon = value;
        self
    }

    #[inline]
    pub fn cost_inc_num(mut self, value: Cost<CostPrimitive>) -> Self {
        self.cost_inc_num = value;
        self
    }

    #[inline]
    pub fn cost_inc_den(mut self, value: Cost<CostPrimitive>) -> Self {
        self.cost_inc_den = value;
        self
    }

    #[inline]
    pub fn min_cost_floor(mut self, value: Cost<CostPrimitive>) -> Self {
        self.min_cost_floor = value;
        self
    }

    #[inline]
    pub fn window_split_left_num(mut self, value: SpaceLength) -> Self {
        self.window_split_left_num = value;
        self
    }

    #[inline]
    pub fn window_split_den(mut self, value: SpaceLength) -> Self {
        self.window_split_den = value;
        self
    }

    #[inline]
    pub fn base_cost_per_delay(mut self, value: Cost<CostPrimitive>) -> Self {
        self.base_cost_per_delay = value;
        self
    }

    #[inline]
    pub fn base_cost_per_dev(mut self, value: Cost<CostPrimitive>) -> Self {
        self.base_cost_per_dev = value;
        self
    }

    pub fn random_seed(mut self) -> Self {
        self.seed = rand::rng().random();
        self
    }

    #[inline]
    pub fn seed(mut self, value: u64) -> Self {
        self.seed = value;
        self
    }

    pub fn build(
        self,
    ) -> Result<InstanceGenConfig<TimePrimitive, CostPrimitive>, InstanceGenConfigBuildError> {
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
            amount_movables,
            amount_fixed,
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
    TimePrimitive: SolverVariable + NumCast + ToPrimitive + Debug + SampleUniform,
    CostPrimitive: SolverVariable + NumCast + Copy + SaturatingAdd + SaturatingMul,
{
    fn from(config: InstanceGenConfig<TimePrimitive, CostPrimitive>) -> Self {
        Self::new(config)
    }
}

impl<TimePrimitive, CostPrimitive> InstanceGenerator<TimePrimitive, CostPrimitive>
where
    TimePrimitive: SolverVariable + NumCast + ToPrimitive + Debug + SampleUniform,
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
            config,
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
                HalfwidthPolicy::Fixed(fixed_halfwidth) => Some(*fixed_halfwidth),
                HalfwidthPolicy::Relative(RelativeSpaceWindowPolicy {
                    frac_of_length,
                    min,
                    max,
                }) => {
                    let length_as_f64: f64 = NumCast::from(length.value()).expect("usize->f64");
                    let halfwidth_as_f64 = (*frac_of_length * length_as_f64).round();
                    let halfwidth_as_usize: usize =
                        NumCast::from(halfwidth_as_f64).expect("f64->usize");
                    Some(SpaceLength::new(
                        halfwidth_as_usize.clamp(min.value(), max.value()),
                    ))
                }
            },
        }
    }

    pub fn generate(&mut self) -> Problem<TimePrimitive, CostPrimitive> {
        let total_requests = self.config.amount_fixed + self.config.amount_movables;
        let arrivals = self.sample_arrivals(total_requests);

        let mut builder =
            ProblemBuilder::<TimePrimitive, CostPrimitive>::new(self.config.quay_length);

        let mut fixed_indices: Vec<usize> = (0..self.config.amount_fixed).collect();
        fixed_indices.sort_by(|&a, &b| arrivals[a].cmp(&arrivals[b]));

        let fixed_assignments = self.plan_fixed(&fixed_indices, &arrivals);
        for assignment in fixed_assignments {
            builder
                .add_preassigned(assignment)
                .expect("This should not fail");
        }

        for time_point in arrivals
            .iter()
            .take(total_requests)
            .skip(self.config.amount_fixed)
            .copied()
        {
            let request = self.sample_movable(time_point);
            builder.add_movable_request(request).unwrap();
        }

        builder.build()
    }

    fn sample_arrivals(&mut self, count: usize) -> Vec<TimePoint<TimePrimitive>> {
        let mut arrivals = Vec::with_capacity(count);
        let mut current_time_float = 0.0f64;

        if self.config.lambda_per_time > 0.0 {
            let exp = Exp::new(self.config.lambda_per_time).unwrap();
            for _ in 0..(count * self.config.arrival_oversample_mult) {
                current_time_float += exp.sample(&mut self.rng);
                let rounded_time = current_time_float.round() as i64;
                let time_value: TimePrimitive = NumCast::from(rounded_time.max(0)).expect("i64->T");
                let time_point = TimePoint::new(time_value);
                if time_point < self.config.horizon {
                    arrivals.push(time_point);
                    if arrivals.len() >= count {
                        break;
                    }
                } else {
                    break;
                }
            }
        }

        while arrivals.len() < count {
            let time_value: TimePrimitive = self
                .rng
                .random_range(TimePrimitive::zero()..self.config.horizon.value());
            arrivals.push(TimePoint::new(time_value));
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
        let start_position_value = if max_start == 0 {
            0
        } else {
            self.rng.random_range(0..=max_start)
        };
        SpacePosition::new(start_position_value)
    }

    #[inline]
    fn length_span(&self) -> SpaceLength {
        let min_length = self.config.min_ship_length;
        let max_length = self.config.max_ship_length;
        let raw_span = max_length.saturating_sub(min_length);
        SpaceLength::new(
            raw_span
                .value()
                .max(self.config.length_span_epsilon.value().max(1)),
        )
    }

    fn processing_mean_from_length(&self, length: SpaceLength) -> f64 {
        let min_ship_len = self.config.min_ship_length;
        let length_span = self.length_span();

        let base_mu = self.config.processing_mu_base;
        let span_mu = self.config.processing_mu_span;
        let length_delta = length.saturating_sub(min_ship_len);

        let dx_f64: f64 = NumCast::from(length_delta.value()).expect("usize->f64");
        let span_f64: f64 = NumCast::from(length_span.value()).expect("usize->f64");
        let base_f64: f64 = NumCast::from(base_mu.value()).expect("T->f64");
        let span_add_f64: f64 = NumCast::from(span_mu.value()).expect("T->f64");

        base_f64 + (span_add_f64 * dx_f64) / span_f64
    }

    fn sample_processing(&mut self, length: SpaceLength) -> TimeDelta<TimePrimitive> {
        let mean = self.processing_mean_from_length(length);
        let standard_deviation = self
            .config
            .processing_time_sigma
            .max(self.config.processing_sigma_floor);
        let normal_distribution = Normal::new(mean, standard_deviation).unwrap();
        let draw_f64 = normal_distribution.sample(&mut self.rng).round();
        let draw_i64: i64 = NumCast::from(draw_f64).expect("f64->i64");

        let mut clamped_duration_value: TimePrimitive = NumCast::from(draw_i64).expect("i64->T");
        if clamped_duration_value < self.config.min_processing.value() {
            clamped_duration_value = self.config.min_processing.value();
        }
        if let Some(max_processing) = self.config.max_processing
            && clamped_duration_value > max_processing.value()
        {
            clamped_duration_value = max_processing.value();
        }
        TimeDelta::new(clamped_duration_value)
    }

    fn length_scaled_costs(
        &self,
        length: SpaceLength,
    ) -> (Cost<CostPrimitive>, Cost<CostPrimitive>) {
        let length_delta = length.saturating_sub(self.config.min_ship_length);
        let length_span = self.length_span();
        let span_scalar: CostPrimitive =
            NumCast::from(length_span.value()).expect("span usize -> C");
        let delta_scalar: CostPrimitive =
            NumCast::from(length_delta.value()).expect("delta usize -> C");
        let increment_cost = self.config.cost_inc_num * delta_scalar;
        let base_cost = self.config.cost_inc_den * span_scalar;

        let scaling_factor: CostPrimitive = increment_cost
            .ratio(base_cost)
            .unwrap_or(CostPrimitive::zero());

        let scale_cost = |base: Cost<CostPrimitive>| -> Cost<CostPrimitive> {
            let scaled = base.saturating_add(base.saturating_mul(scaling_factor));
            scaled.max(self.config.min_cost_floor)
        };

        (
            scale_cost(self.config.base_cost_per_delay),
            scale_cost(self.config.base_cost_per_dev),
        )
    }

    #[inline]
    fn split_left(&self, needed_length: SpaceLength) -> SpaceLength {
        if self.config.window_split_den.is_zero() {
            return SpaceLength::zero();
        }
        let left_value = (needed_length.value() * self.config.window_split_left_num.value())
            / self.config.window_split_den.value();
        SpaceLength::new(left_value)
    }

    fn space_window_for_fixed_assignment(
        &self,
        start_pos: SpacePosition,
        length: SpaceLength,
    ) -> SpaceInterval {
        match &self.config.space_window_policy {
            SpaceWindowPolicy::FullQuay => {
                SpaceInterval::new(SpacePosition::new(0), self.quay_end())
            }
            SpaceWindowPolicy::Halfwidth(_) => {
                let halfwidth = self.halfwidth_for(length).expect("halfwidth required");
                self.fixed_halfwidth_window_containing_run(start_pos, length, halfwidth)
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
        let mut window_start = target.saturating_sub(halfwidth);
        let mut window_end = (target + halfwidth).min(quay_end);

        if (window_end - window_start) < length {
            let needed_expansion = length - (window_end - window_start);
            let left_expansion = self.split_left(needed_expansion);
            let right_expansion = needed_expansion - left_expansion;

            window_start = window_start.saturating_sub(left_expansion);
            window_end = (window_end + right_expansion).min(quay_end);

            if (window_end - window_start) < length {
                window_start = SpacePosition::zero();
                window_end = (window_start + length).min(quay_end);
            }
        }

        SpaceInterval::new(window_start, window_end)
    }

    fn fixed_halfwidth_window_containing_run(
        &self,
        start_pos: SpacePosition,
        length: SpaceLength,
        halfwidth: SpaceLength,
    ) -> SpaceInterval {
        let quay_end = self.quay_end();
        let mut window_start = start_pos.saturating_sub(halfwidth);
        let mut window_end = (start_pos + length + halfwidth).min(quay_end);

        if (window_end - window_start) < length {
            window_end = (window_start + length).min(quay_end);
            window_start = window_end - length;
        }
        SpaceInterval::new(window_start, window_end)
    }

    fn space_window_for_movable(
        &self,
        target: SpacePosition,
        length: SpaceLength,
    ) -> SpaceInterval {
        match &self.config.space_window_policy {
            SpaceWindowPolicy::FullQuay => {
                SpaceInterval::new(SpacePosition::new(0), self.quay_end())
            }
            SpaceWindowPolicy::Halfwidth(_) => {
                let halfwidth = self.halfwidth_for(length).expect("halfwidth required");
                self.fixed_halfwidth_window(target, length, halfwidth)
            }
        }
    }

    fn sample_movable(
        &mut self,
        arrival: TimePoint<TimePrimitive>,
    ) -> Request<Movable, TimePrimitive, CostPrimitive> {
        let length = self.sample_length();
        let processing_duration = self.sample_processing(length);
        let target = self.sample_target_position_for_length(length);
        let (cost_per_delay, cost_per_deviation) = self.length_scaled_costs(length);
        let space_window = self.space_window_for_movable(target, length);

        Request::<Movable, TimePrimitive, CostPrimitive>::new(
            self.fresh_id(),
            length,
            arrival,
            processing_duration,
            target,
            cost_per_delay,
            cost_per_deviation,
            space_window,
        )
        .expect("movable: constructed request must be feasible")
    }

    fn plan_fixed(
        &mut self,
        fixed_sorted: &[usize],
        arrivals: &[TimePoint<TimePrimitive>],
    ) -> Vec<Assignment<Fixed, TimePrimitive, CostPrimitive>> {
        let mut fixed_assignments = Vec::with_capacity(fixed_sorted.len());
        let mut current_time = TimePoint::new(TimePrimitive::zero());

        for &arrival_index in fixed_sorted.iter() {
            let length = self.sample_length();
            let processing_duration = self.sample_processing(length);
            let target = self.sample_target_position_for_length(length);
            let (cost_per_delay, cost_per_deviation) = self.length_scaled_costs(length);

            let arrival = arrivals[arrival_index];
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

            let request = Request::<Fixed, TimePrimitive, CostPrimitive>::new(
                self.fresh_id(),
                length,
                arrival,
                processing_duration,
                target,
                cost_per_delay,
                cost_per_deviation,
                space_window,
            )
            .expect("fixed: constructed request must be feasible");

            fixed_assignments.push(Assignment::new(request, start_pos, start));
            current_time = start + processing_duration + self.config.fixed_gap;
        }
        fixed_assignments
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
    fn test_movable_requests_feasible() {
        let config = cfg_relative(123);
        let mut generator = InstanceGenerator::<Tm, Cm>::new(config.clone());
        let problem = generator.generate();

        for request in problem.iter_movable_requests() {
            assert!(request.length() >= config.min_length());
            assert!(request.length() <= config.max_length());
            assert!(request.feasible_space_window().measure() >= request.length());
            let max_start_pos = SpacePosition::new(config.quay_length().value()) - request.length();
            assert!(request.target_position() <= max_start_pos);
        }
    }

    #[test]
    fn test_fixed_assignments_are_non_overlapping_in_time_and_within_quay() {
        let config = cfg_relative(777);
        let mut generator = InstanceGenerator::<Tm, Cm>::new(config.clone());
        let problem = generator.generate();

        let mut spans: Vec<_> = problem
            .iter_fixed_assignments()
            .map(|assignment| {
                let start_time = assignment.start_time();
                let end_time = start_time + assignment.request().processing_duration();
                let start_pos = assignment.start_position();
                let end_pos = start_pos + assignment.request().length();
                (start_time, end_time, start_pos, end_pos, assignment)
            })
            .collect();

        spans.sort_by(|a, b| a.0.cmp(&b.0));

        let mut previous_end_time: Option<TimePoint<i64>> = None;
        let quay_end = SpacePosition::new(config.quay_length().value());
        for (start_time, end_time, start_pos, end_pos, assignment) in spans {
            if let Some(previous_end) = previous_end_time {
                assert!(
                    start_time >= previous_end,
                    "fixed assignments overlap in time"
                );
            }
            previous_end_time = Some(end_time);

            assert!(start_pos <= quay_end);
            assert!(end_pos <= quay_end);

            let space_window = assignment.request().feasible_space_window();
            assert!(space_window.contains(start_pos));
            assert!(space_window.contains(end_pos) || end_pos == space_window.end());

            assert_eq!(assignment.request().length(), end_pos - start_pos);
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
    fn windows_match_policy_relative() {
        let config = cfg_relative(2024);
        let generator = InstanceGenerator::<Tm, Cm>::new(config.clone());

        let short_ship = SpaceLength::new(config.min_length().value());
        let long_ship = SpaceLength::new(config.max_length().value());

        let target_pos = SpacePosition::new(200);

        let sw_short = generator.space_window_for_movable(target_pos, short_ship);
        let sw_long = generator.space_window_for_movable(target_pos, long_ship);

        assert!(sw_short.measure().value() >= short_ship.value());
        assert!(sw_long.measure().value() >= long_ship.value());
        assert!(sw_short.end().value() <= config.quay_length().value());
        assert!(sw_long.end().value() <= config.quay_length().value());
    }

    #[test]
    fn processing_is_clamped_between_min_and_max_if_present() {
        let config = InstanceGenConfig::new(
            SpaceLength::new(1_000),
            SpaceLength::new(80),
            SpaceLength::new(300),
            SpaceWindowPolicy::FullQuay,
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
            let duration = generator.sample_processing(ship_len);
            assert!(
                duration.value() >= 20 && duration.value() <= 24,
                "processing {:?} not clamped",
                duration
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
