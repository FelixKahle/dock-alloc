use std::hint::black_box;

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use dock_alloc_core::{
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimeInterval, TimePoint},
};
use dock_alloc_solver::{
    berth::{berthocc::BerthOccupancy, quay::IntervalSetQuay},
    domain::SpaceTimeRectangle,
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

// ---------- Scenario knobs (realistic quay) ----------
const SEED: u64 = 0xD0C_A11C; // deterministic RNG for reproducibility

// Time: 2 months at 1-hour resolution
const DAYS: i64 = 60;
const HORIZON_H: i64 = 24 * DAYS; // 1440 hours

// Typical ship stays: 2–3 days (in hours)
const STAY_MIN_H: i64 = 48;
const STAY_MAX_H: i64 = 72;

// Quay geometry: ~800 m discretized into 1 m segments (adjust as your S means)
const S_LEN: usize = 800;

// Ships: short feeder to biggish vessels (meters ~= segments here)
const SHIP_LEN_MIN: usize = 60; // 60 m
const SHIP_LEN_MAX: usize = 280; // 280 m

// Arrival intensity: ~ 6 per day on average (Poisson-like via exponential gaps)
const ARRIVALS_PER_DAY: f64 = 6.0; // tune to taste

// Query workload (per pass)
const PASS_WINDOWS: usize = 5_000;

// ----------------------------------------------------

type T = i64;
type Q = IntervalSetQuay;
type BO = BerthOccupancy<T, Q>;

#[inline]
fn pos(x: usize) -> SpacePosition {
    SpacePosition::new(x)
}
#[inline]
fn len(x: usize) -> SpaceLength {
    SpaceLength::new(x)
}
#[inline]
fn si(a: usize, b: usize) -> SpaceInterval {
    SpaceInterval::new(pos(a), pos(b))
}
#[inline]
fn tp(t: T) -> TimePoint<T> {
    TimePoint::new(t)
}
#[inline]
fn ti(a: T, b: T) -> TimeInterval<T> {
    TimeInterval::new(tp(a), tp(b))
}
#[inline]
fn rect(tw: TimeInterval<T>, s: SpaceInterval) -> SpaceTimeRectangle<T> {
    SpaceTimeRectangle::new(s, tw)
}

// Draw exponential(λ) in hours for inter-arrival times
fn exp_gap_hours<R: Rng + ?Sized>(rng: &mut R, lambda_per_hour: f64) -> i64 {
    // Inverse CDF: -ln(U)/λ
    let u: f64 = rng.random::<f64>().clamp(1e-12, 1.0 - 1e-12);
    let gap = -u.ln() / lambda_per_hour;
    gap.max(1.0).round() as i64 // at least 1 hour
}

// Build a baseline occupancy by simulating arrivals over 2 months.
fn build_fragmented_base() -> BO {
    let mut rng = ChaCha8Rng::seed_from_u64(SEED);
    let mut b = BO::new(len(S_LEN));

    // Convert arrivals/day to arrivals/hour
    let lambda_per_hour = ARRIVALS_PER_DAY / 24.0;

    let mut t = 0_i64;
    while t < HORIZON_H {
        // Draw next arrival gap
        t += exp_gap_hours(&mut rng, lambda_per_hour);
        if t >= HORIZON_H {
            break;
        }

        // Draw stay in [48h, 72h]
        let stay_h = rng.random_range(STAY_MIN_H..=STAY_MAX_H);
        let end_t = (t + stay_h).min(HORIZON_H);

        // Draw ship length and a random feasible berth start
        let ship_len = rng.random_range(SHIP_LEN_MIN..=SHIP_LEN_MAX).min(S_LEN);
        let start_pos = rng.random_range(0..=(S_LEN - ship_len));
        let space = si(start_pos, start_pos + ship_len);

        // Occupy that rectangle (idempotent if overlapping others)
        let tw = ti(t, end_t);
        let r = rect(tw, space);
        // Ignore OOB here; we keep the generator in-bounds by construction.
        b.occupy(&r).expect("in-bounds occupy");
    }
    b
}

// Run a “pass”: produce realistic requests and enumerate feasible free slots.
fn run_query_pass(bo: &BO) {
    let mut rng = ChaCha8Rng::seed_from_u64(SEED ^ 0xBEEF);

    for _ in 0..PASS_WINDOWS {
        // Request duration ~ 2–3 days
        let dur_h = rng.random_range(STAY_MIN_H..=STAY_MAX_H);
        let duration = TimeDelta::new(dur_h);

        // Choose a time window where the request might start (a few days wide)
        let win_span_h = rng.random_range(24..=96) as i64; // 1–4 days
        let a = rng.random_range(0..=HORIZON_H.saturating_sub(win_span_h));
        let tw = ti(a, a + win_span_h);

        // Require a realistic ship length
        let required = len(rng.random_range(SHIP_LEN_MIN..=SHIP_LEN_MAX).min(S_LEN));

        // Search anywhere along the quay
        let bounds = si(0, S_LEN);

        // Iterate feasible slots (start-times × berth-intervals)
        // black_box to prevent optimizer from eliding the work
        let count = bo
            .iter_free_slots(tw, duration, required, bounds)
            .fold(0usize, |acc, _slot| acc + 1);
        black_box(count);
    }
}

// -------------- Criterion wiring --------------
fn bench_quay_realistic(c: &mut Criterion) {
    // Build the fragmented base once per sample (measured as part of the batch setup)
    c.bench_function("realistic_quay_free_slot_search_booleanvec", |bch| {
        bch.iter_batched(
            || build_fragmented_base(),
            |bo| run_query_pass(&bo),
            BatchSize::LargeInput,
        );
    });
}

// If you want to compare multiple encodings, duplicate the group with different `Q` aliases.
// e.g. swap `use your_crate_name::berth::quay::BitPackedQuay as Q;` above and rename the function.

criterion_group!(quay, bench_quay_realistic);
criterion_main!(quay);
