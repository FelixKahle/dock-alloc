// Copyright 2025 Felix Kahle. All rights reserved.

#include "benchmark/benchmark.h"
#include "dockalloc/solver/timeline.h"

namespace dockalloc::solver
{
    static void BM_IsFree_10000Slots(benchmark::State& state)
    {
        BitPackedTimeline<uint64_t, uint64_t> t(10'000'000);
        t.Reserve(1000, 100000);
        for (auto _ : state)
        {
            benchmark::DoNotOptimize(t.IsFree(1000, 10000));
        }
    }

    BENCHMARK(BM_IsFree_10000Slots);

    static void BM_Reserve_10000Slots(benchmark::State& state)
    {
        BitPackedTimeline<uint64_t, uint64_t> t(10'000'000);
        for (auto _ : state)
        {
            t.Reserve(1000, 10000);
            benchmark::ClobberMemory();
        }
    }

    BENCHMARK(BM_Reserve_10000Slots);

    static void BM_Free_10000Slots(benchmark::State& state)
    {
        BitPackedTimeline<uint64_t, uint64_t> t(10'000'000);
        t.Reserve(1000, 10000);
        for (auto _ : state)
        {
            t.Free(1000, 10000);
            benchmark::ClobberMemory();
        }
    }

    BENCHMARK(BM_Free_10000Slots);

    BENCHMARK_MAIN();
}
