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

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use dock_alloc_core::{
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimeInterval, TimePoint},
};
use dock_alloc_solver::{
    berth::{prelude::BerthOccupancy, quay::BTreeMapQuay, slice::SliceView},
    domain::SpaceTimeRectangle,
};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::hint::black_box;

type T = i64;
type BO = BerthOccupancy<T, BTreeMapQuay>;

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
fn rect(tw: TimeInterval<T>, si: SpaceInterval) -> SpaceTimeRectangle<T> {
    SpaceTimeRectangle::new(si, tw)
}

// Build a base berth occupancy with periodic busy/free structure to create timeline keys.
fn build_base(quay_len: usize, t_upper: T) -> BO {
    let mut berth = BO::new(len(quay_len));
    // Periodic occupancy: every 20 ticks, block for 10 ticks the central band [200, 800)
    // This creates timeline keys and a good mix of free/occupied intervals.
    let band = si(200.min(quay_len.saturating_sub(1)), 800.min(quay_len));
    let step: T = 20;
    let span: T = 10;
    let mut t = 0;
    while t + span <= t_upper {
        if !band.is_empty() {
            let _ = berth.occupy(&rect(ti(t, t + span), band));
        }
        t += step;
    }
    berth
}

fn build_overlay<'a>(
    berth: &BO,
) -> dock_alloc_solver::berth::overlay::BerthOccupancyOverlay<'_, '_, T, BTreeMapQuay> {
    let mut ov = berth.overlay();
    // Make a sub-band free across most of the window to simulate overlay undoing base blocks.
    let _ = ov.free(&rect(ti(100, 900), si(450, 550)));
    // Add an extra occupied strip on otherwise-free areas.
    let _ = ov.occupy(&rect(ti(50, 950), si(50, 100)));
    ov
}

fn gen_query_rects(
    quay_len: usize,
    t_upper: T,
    count: usize,
    seed: u64,
) -> Vec<SpaceTimeRectangle<T>> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
        let t0 = rng.random_range(0..t_upper.saturating_sub(10));
        let dur: T = rng.random_range(1..=20);
        let a = rng.random_range(0..quay_len);
        let b = (a + rng.random_range(1..=100)).min(quay_len);
        out.push(rect(ti(t0, (t0 + dur).min(t_upper)), si(a, b)));
    }
    out
}

fn bench_is_free(c: &mut Criterion) {
    let quay_len = 1024usize;
    let t_upper: T = 1000;

    let berth = build_base(quay_len, t_upper);
    let overlay = build_overlay(&berth);
    let rects = gen_query_rects(quay_len, t_upper, 1000, 42);

    let mut group = c.benchmark_group("overlay_is_free");
    group.bench_function("is_free_mixed_overlay", |b| {
        b.iter(|| {
            let mut cnt = 0usize;
            for r in &rects {
                if overlay.is_free(r).unwrap() {
                    cnt += 1;
                }
            }
            black_box(cnt)
        })
    });
    group.bench_function("is_occupied_mixed_overlay", |b| {
        b.iter(|| {
            let mut cnt = 0usize;
            for r in &rects {
                if overlay.is_occupied(r).unwrap() {
                    cnt += 1;
                }
            }
            black_box(cnt)
        })
    });
    group.finish();
}

fn bench_iter_free_slots(c: &mut Criterion) {
    let quay_len = 1024usize;
    let t_upper: T = 1000;

    let berth = build_base(quay_len, t_upper);
    let overlay = build_overlay(&berth);

    let bounds = si(0, quay_len);
    let mut group = c.benchmark_group("overlay_iter_free_slots");

    for &dur in &[1_i64, 5, 20, 100] {
        group.bench_function(format!("duration_{}", dur), |b| {
            b.iter(|| {
                let it =
                    overlay.iter_free_slots(ti(0, t_upper), TimeDelta::new(dur), len(10), bounds);
                // Consume without allocating large vectors
                let mut n = 0usize;
                for slot in it {
                    black_box(slot.slot());
                    n += 1;
                }
                black_box(n)
            })
        });
    }

    group.finish();
}

fn bench_iter_free_regions(c: &mut Criterion) {
    let quay_len = 1024usize;
    let t_upper: T = 1000;

    let berth = build_base(quay_len, t_upper);
    let overlay = build_overlay(&berth);

    let bounds = si(0, quay_len);
    let mut group = c.benchmark_group("overlay_iter_free_regions");

    for &dur in &[1_i64, 5, 20, 100] {
        group.bench_function(format!("duration_{}", dur), |b| {
            b.iter(|| {
                let it =
                    overlay.iter_free_regions(ti(0, t_upper), TimeDelta::new(dur), len(10), bounds);
                // Consume without allocating large vectors
                let mut n = 0usize;
                for region in it {
                    black_box(region.region());
                    n += 1;
                }
                black_box(n)
            })
        });
    }

    group.finish();
}

fn bench_next_key_after(c: &mut Criterion) {
    let quay_len = 1024usize;
    let t_upper: T = 2000;

    let berth = build_base(quay_len, t_upper);
    let overlay = build_overlay(&berth);

    let mut group = c.benchmark_group("overlay_next_key_after");

    group.bench_function("scan_keys", |b| {
        b.iter(|| {
            // Walk through all ascending keys using SliceView::next_key_after
            let mut count = 0usize;
            let mut cur = tp(-1);
            while let Some(next) = overlay.next_key_after(cur) {
                cur = next;
                count += 1;
            }
            black_box(count)
        })
    });

    group.finish();
}

fn gen_rects_apply(
    quay_len: usize,
    count: usize,
    t_upper: T,
    seed: u64,
) -> Vec<SpaceTimeRectangle<T>> {
    let mut rng = StdRng::seed_from_u64(seed); // reproducible “randomness”
    let mut rects = Vec::with_capacity(count);

    for _ in 0..count {
        // Random start time and duration
        let t0: T = rng.random_range(0..t_upper.saturating_sub(20));
        let dur: T = rng.random_range(5..=15); // variable duration
        let t1 = (t0 + dur).min(t_upper);

        // Random spatial interval
        let a = rng.random_range(0..quay_len);
        let max_width = quay_len.saturating_sub(a);
        let w = rng.random_range(5..=max_width.max(5)); // at least 5 wide
        let b = (a + w).min(quay_len);

        rects.push(rect(ti(t0, t1), si(a, b)));
    }

    rects
}

fn bench_overlay_mut_ops(c: &mut Criterion) {
    let quay_len = 1024usize;
    let t_upper: T = 1000;

    // Fixed set of rectangles to apply per iteration
    let rects_apply = gen_rects_apply(quay_len, 100, t_upper, 0xDEADBEEF);
    let mut group = c.benchmark_group("overlay_mut_ops");

    // Use batched setup so each measurement starts from a fresh overlay
    group.bench_function("occupy_then_free_batched", |b| {
        b.iter_batched(
            // Setup: return only the base Box
            || Box::new(build_base(quay_len, t_upper)),
            // Routine: construct the overlay from the Box, then run the ops
            |berth_box| {
                let mut ov = build_overlay(&*berth_box);
                for (j, r) in rects_apply.iter().enumerate() {
                    if j % 2 == 0 {
                        let _ = ov.occupy(r);
                    } else {
                        let _ = ov.free(r);
                    }
                }
                black_box(ov.into_commit())
            },
            BatchSize::SmallInput,
        );
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_is_free,
    bench_iter_free_slots,
    bench_iter_free_regions,
    bench_next_key_after,
    bench_overlay_mut_ops
);
criterion_main!(benches);
