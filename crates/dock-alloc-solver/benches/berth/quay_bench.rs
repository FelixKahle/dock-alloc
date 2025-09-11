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

use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use dock_alloc_core::space::{SpaceInterval, SpaceLength, SpacePosition};
use dock_alloc_solver::berth::quay::{
    BTreeMapQuay, BitPackedQuay, BooleanVecQuay, QuayRead, QuayWrite,
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::{env, hint::black_box};

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

#[derive(Clone, Copy)]
enum OpKind {
    Free,
    Occupy,
}
#[derive(Clone, Copy)]
struct Op {
    kind: OpKind,
    a: usize,
    b: usize,
}
#[derive(Clone, Copy)]
struct Query {
    a: usize,
    b: usize,
}
#[derive(Clone, Copy)]
struct IterReq {
    req: usize,
    a: usize,
    b: usize,
}

fn gen_ops(size: usize, n: usize, rng: &mut impl Rng) -> Vec<Op> {
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        let a = rng.random_range(0..=size);
        let max_w = size.saturating_sub(a);
        let w = rng.random_range(0..=max_w.min(128));
        let b = (a + w).min(size);
        let kind = if i % 2 == 0 {
            OpKind::Free
        } else {
            OpKind::Occupy
        };
        out.push(Op { kind, a, b });
    }
    out
}

fn gen_queries(size: usize, n: usize, rng: &mut impl Rng) -> Vec<Query> {
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let a = rng.random_range(0..=size);
        let max_w = size.saturating_sub(a);
        let w = rng.random_range(0..=max_w.min(256));
        let b = (a + w).min(size);
        out.push(Query { a, b });
    }
    out
}
fn gen_iter_reqs(size: usize, n: usize, rng: &mut impl Rng) -> Vec<IterReq> {
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let req = rng.random_range(1..=size.max(1).min(256));
        let a = rng.random_range(0..=size);
        let max_w = size.saturating_sub(a);
        let w = rng.random_range(0..=max_w);
        let b = (a + w).min(size);
        out.push(IterReq { req, a, b });
    }
    out
}

fn prepare_fragmented_quay<Q: QuayRead + QuayWrite>(
    size: usize,
    initially_free: bool,
    ops: &[Op],
) -> Q {
    let mut q = Q::new(len(size), initially_free);
    for &Op { kind, a, b } in ops {
        let _ = match kind {
            OpKind::Free => q.free(si(a, b)),
            OpKind::Occupy => q.occupy(si(a, b)),
        };
    }
    q
}

fn register_apply<Q: QuayRead + QuayWrite>(
    c: &mut Criterion,
    name: &str,
    size: usize,
    ops_n: usize,
) {
    let mut group = c.benchmark_group(format!("quay_apply/{name}"));
    group.throughput(Throughput::Elements(ops_n as u64));

    let mut rng = ChaCha8Rng::seed_from_u64(0xA11CE_DEAD_BEEF);
    let ops = gen_ops(size, ops_n, &mut rng);

    for &init_free in &[false, true] {
        let label = if init_free { "init_free" } else { "init_occ" };
        group.bench_function(BenchmarkId::new("apply", label), |b| {
            b.iter_batched(
                || Q::new(len(size), init_free),
                |mut q| {
                    for &Op { kind, a, b } in &ops {
                        let _ = match kind {
                            OpKind::Free => q.free(si(a, b)),
                            OpKind::Occupy => q.occupy(si(a, b)),
                        };
                    }
                    black_box(q);
                },
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

fn register_queries<Q: QuayRead + QuayWrite>(
    c: &mut Criterion,
    name: &str,
    size: usize,
    ops_n: usize,
    queries_n: usize,
) {
    let mut group = c.benchmark_group(format!("quay_queries/{name}"));
    group.throughput(Throughput::Elements(queries_n as u64));

    let mut rng = ChaCha8Rng::seed_from_u64(0xFEED_FACE_CAFE_BABE);
    let ops = gen_ops(size, ops_n, &mut rng);
    let queries = gen_queries(size, queries_n, &mut rng);

    for &init_free in &[false, true] {
        let quay = prepare_fragmented_quay::<Q>(size, init_free, &ops);
        let label = if init_free { "init_free" } else { "init_occ" };
        group.bench_function(BenchmarkId::new("check", label), |b| {
            b.iter(|| {
                let mut free_cnt = 0usize;
                let mut occ_cnt = 0usize;
                for &Query { a, b } in &queries {
                    if quay.check_free(si(a, b)).unwrap() {
                        free_cnt += 1;
                    }
                    if quay.check_occupied(si(a, b)).unwrap() {
                        occ_cnt += 1;
                    }
                }
                black_box((free_cnt, occ_cnt))
            })
        });
    }
    group.finish();
}

fn register_iterate<Q: QuayRead + QuayWrite>(
    c: &mut Criterion,
    name: &str,
    size: usize,
    ops_n: usize,
    iters_n: usize,
) {
    let mut group = c.benchmark_group(format!("quay_iter/{name}"));
    group.throughput(Throughput::Elements(iters_n as u64));

    let mut rng = ChaCha8Rng::seed_from_u64(0x1234_5678_9ABC_DEF0);
    let ops = gen_ops(size, ops_n, &mut rng);
    let iters = gen_iter_reqs(size, iters_n, &mut rng);

    for &init_free in &[false, true] {
        let quay = prepare_fragmented_quay::<Q>(size, init_free, &ops);
        let label = if init_free { "init_free" } else { "init_occ" };
        group.bench_function(BenchmarkId::new("iter", label), |b| {
            b.iter(|| {
                let mut count = 0usize;
                for &IterReq { req, a, b } in &iters {
                    for iv in quay.iter_free_intervals(len(req), si(a, b)) {
                        black_box(&iv);
                        count += 1;
                    }
                }
                black_box(count)
            })
        });
    }
    group.finish();
}

fn register_mixed<Q: QuayRead + QuayWrite>(
    c: &mut Criterion,
    name: &str,
    size: usize,
    ops_n: usize,
    queries_n: usize,
    iters_n: usize,
) {
    let mut group = c.benchmark_group(format!("quay_mixed/{name}"));

    let mut rng = ChaCha8Rng::seed_from_u64(0xD00D_F00D_F0F0);
    let ops = gen_ops(size, ops_n, &mut rng);
    let queries = gen_queries(size, queries_n, &mut rng);
    let iters = gen_iter_reqs(size, iters_n, &mut rng);

    for &init_free in &[false, true] {
        let label = if init_free { "init_free" } else { "init_occ" };
        group.bench_function(BenchmarkId::new("mixed", label), |b| {
            b.iter_batched(
                || prepare_fragmented_quay::<Q>(size, init_free, &ops),
                |mut q| {
                    for &Op { kind, a, b } in &ops[0..ops.len().min(256)] {
                        let _ = match kind {
                            OpKind::Free => q.free(si(a, b)),
                            OpKind::Occupy => q.occupy(si(a, b)),
                        };
                    }
                    let mut acc = 0usize;
                    for &Query { a, b } in &queries[0..queries.len().min(1000)] {
                        if q.check_free(si(a, b)).unwrap() {
                            acc ^= 1;
                        }
                        if q.check_occupied(si(a, b)).unwrap() {
                            acc ^= 2;
                        }
                    }
                    for &IterReq { req, a, b } in &iters[0..iters.len().min(500)] {
                        for iv in q.iter_free_intervals(len(req), si(a, b)) {
                            acc ^= iv.start().value() ^ iv.end().value();
                        }
                    }
                    black_box(acc);
                },
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

macro_rules! register_impl {
    ($c:expr, $name:expr, $ty:ty, $size:expr, $ops:expr, $queries:expr, $iters:expr) => {{
        register_apply::<$ty>($c, $name, $size, $ops);
        register_queries::<$ty>($c, $name, $size, $ops, $queries);
        register_iterate::<$ty>($c, $name, $size * 2, $ops * 2, $iters); // iterate uses a larger size, like before
        register_mixed::<$ty>($c, $name, $size, $ops, $queries / 2, $iters / 2);
    }};
}

fn quay_benches(c: &mut Criterion) {
    // Defaults (override with env)
    let size = env::var("QUAY_SIZE")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(4096usize);
    let ops_n = env::var("QUAY_OPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(6_000usize);
    let queries = env::var("QUAY_QUERIES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(10_000usize);
    let iters_n = env::var("QUAY_ITERS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(5_000usize);

    let impls = env::var("QUAY_IMPLS").unwrap_or_else(|_| "btreemap,boolvec,bitpacked".to_string());
    let want_btree = impls.contains("btreemap");
    let want_boolvec = impls.contains("boolvec");
    let want_bitpack = impls.contains("bitpacked");

    if want_btree {
        register_impl!(c, "btreemap", BTreeMapQuay, size, ops_n, queries, iters_n);
    }
    if want_boolvec {
        register_impl!(c, "boolvec", BooleanVecQuay, size, ops_n, queries, iters_n);
    }
    if want_bitpack {
        register_impl!(c, "bitpacked", BitPackedQuay, size, ops_n, queries, iters_n);
    }
}

// Register all benchmarks
criterion_group!(benches, quay_benches);
criterion_main!(benches);
