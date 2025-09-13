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

use criterion::{
    BatchSize, BenchmarkGroup, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main,
    measurement::WallTime,
};
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

fn register_apply_for_impl<Q: QuayRead + QuayWrite>(
    group: &mut BenchmarkGroup<'_, WallTime>,
    impl_label: &str,
    size: usize,
    ops_n: usize,
) {
    group.throughput(Throughput::Elements(ops_n as u64));

    let mut rng = ChaCha8Rng::seed_from_u64(0xA11C_EDEA_DBEE_F000);
    let ops = gen_ops(size, ops_n, &mut rng);

    for &init_free in &[false, true] {
        let label = format!(
            "{impl_label}/{}",
            if init_free { "init_free" } else { "init_occ" }
        );
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
}

fn register_queries_for_impl<Q: QuayRead + QuayWrite>(
    group: &mut BenchmarkGroup<'_, WallTime>,
    impl_label: &str,
    size: usize,
    ops_n: usize,
    queries_n: usize,
) {
    group.throughput(Throughput::Elements(queries_n as u64));

    let mut rng = ChaCha8Rng::seed_from_u64(0xFEED_FACE_CAFE_BABE);
    let ops = gen_ops(size, ops_n, &mut rng);
    let queries = gen_queries(size, queries_n, &mut rng);

    for &init_free in &[false, true] {
        let quay = prepare_fragmented_quay::<Q>(size, init_free, &ops);
        let label = format!(
            "{impl_label}/{}",
            if init_free { "init_free" } else { "init_occ" }
        );
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
}

fn register_iter_for_impl<Q: QuayRead + QuayWrite>(
    group: &mut BenchmarkGroup<'_, WallTime>,
    impl_label: &str,
    size: usize,
    ops_n: usize,
    iters_n: usize,
) {
    group.throughput(Throughput::Elements(iters_n as u64));

    let mut rng = ChaCha8Rng::seed_from_u64(0x1234_5678_9ABC_DEF0);
    let ops = gen_ops(size, ops_n, &mut rng);
    let iters = gen_iter_reqs(size, iters_n, &mut rng);

    for &init_free in &[false, true] {
        let quay = prepare_fragmented_quay::<Q>(size, init_free, &ops);
        let label = format!(
            "{impl_label}/{}",
            if init_free { "init_free" } else { "init_occ" }
        );
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
}

fn register_mixed_for_impl<Q: QuayRead + QuayWrite>(
    group: &mut BenchmarkGroup<'_, WallTime>,
    impl_label: &str,
    size: usize,
    ops_n: usize,
    queries_n: usize,
    iters_n: usize,
) {
    let mut rng = ChaCha8Rng::seed_from_u64(0xD00D_F00D_F0F0);
    let ops = gen_ops(size, ops_n, &mut rng);
    let queries = gen_queries(size, queries_n, &mut rng);
    let iters = gen_iter_reqs(size, iters_n, &mut rng);

    for &init_free in &[false, true] {
        let label = format!(
            "{impl_label}/{}",
            if init_free { "init_free" } else { "init_occ" }
        );
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
                    for &Query { a, b } in &queries[0..queries.len().min(1_000)] {
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
}

#[derive(Clone, Copy)]
struct Impls {
    btree: bool,
    boolvec: bool,
    bitpack: bool,
}
impl Impls {
    fn from_env() -> Self {
        let s = env::var("QUAY_IMPLS").unwrap_or_else(|_| "btreemap,boolvec,bitpacked".to_string());
        Self {
            btree: s.contains("btreemap"),
            boolvec: s.contains("boolvec"),
            bitpack: s.contains("bitpacked"),
        }
    }
}

fn register_apply_all(c: &mut Criterion, size: usize, ops_n: usize, impls: Impls) {
    let mut group = c.benchmark_group("quay_apply");
    if impls.btree {
        register_apply_for_impl::<BTreeMapQuay>(&mut group, "btreemap", size, ops_n);
    }
    if impls.boolvec {
        register_apply_for_impl::<BooleanVecQuay>(&mut group, "boolvec", size, ops_n);
    }
    if impls.bitpack {
        register_apply_for_impl::<BitPackedQuay>(&mut group, "bitpacked", size, ops_n);
    }
    group.finish();
}

fn register_queries_all(
    c: &mut Criterion,
    size: usize,
    ops_n: usize,
    queries_n: usize,
    impls: Impls,
) {
    let mut group = c.benchmark_group("quay_queries");
    if impls.btree {
        register_queries_for_impl::<BTreeMapQuay>(&mut group, "btreemap", size, ops_n, queries_n);
    }
    if impls.boolvec {
        register_queries_for_impl::<BooleanVecQuay>(&mut group, "boolvec", size, ops_n, queries_n);
    }
    if impls.bitpack {
        register_queries_for_impl::<BitPackedQuay>(&mut group, "bitpacked", size, ops_n, queries_n);
    }
    group.finish();
}

fn register_iter_all(c: &mut Criterion, size: usize, ops_n: usize, iters_n: usize, impls: Impls) {
    // iterate uses a larger arena like before
    let size2 = size * 2;
    let ops2 = ops_n * 2;
    let mut group = c.benchmark_group("quay_iter");
    if impls.btree {
        register_iter_for_impl::<BTreeMapQuay>(&mut group, "btreemap", size2, ops2, iters_n);
    }
    if impls.boolvec {
        register_iter_for_impl::<BooleanVecQuay>(&mut group, "boolvec", size2, ops2, iters_n);
    }
    if impls.bitpack {
        register_iter_for_impl::<BitPackedQuay>(&mut group, "bitpacked", size2, ops2, iters_n);
    }
    group.finish();
}

fn register_mixed_all(
    c: &mut Criterion,
    size: usize,
    ops_n: usize,
    queries_n: usize,
    iters_n: usize,
    impls: Impls,
) {
    let mut group = c.benchmark_group("quay_mixed");
    if impls.btree {
        register_mixed_for_impl::<BTreeMapQuay>(
            &mut group,
            "btreemap",
            size,
            ops_n,
            queries_n / 2,
            iters_n / 2,
        );
    }
    if impls.boolvec {
        register_mixed_for_impl::<BooleanVecQuay>(
            &mut group,
            "boolvec",
            size,
            ops_n,
            queries_n / 2,
            iters_n / 2,
        );
    }
    if impls.bitpack {
        register_mixed_for_impl::<BitPackedQuay>(
            &mut group,
            "bitpacked",
            size,
            ops_n,
            queries_n / 2,
            iters_n / 2,
        );
    }
    group.finish();
}

fn quay_benches(c: &mut Criterion) {
    let size: usize = env::var("QUAY_SIZE")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(4096);
    let ops_n: usize = env::var("QUAY_OPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(6_000);
    let queries_n: usize = env::var("QUAY_QUERIES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(10_000);
    let iters_n: usize = env::var("QUAY_ITERS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(5_000);
    let impls = Impls::from_env();

    register_apply_all(c, size, ops_n, impls);
    register_queries_all(c, size, ops_n, queries_n, impls);
    register_iter_all(c, size, ops_n, iters_n, impls);
    register_mixed_all(c, size, ops_n, queries_n, iters_n, impls);
}

criterion_group!(benches, quay_benches);
criterion_main!(benches);
