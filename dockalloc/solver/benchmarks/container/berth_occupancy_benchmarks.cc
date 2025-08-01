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

#include "benchmark/benchmark.h"
#include "dockalloc/solver/container/berth_occupancy.h"

namespace dockalloc::solver
{
    static void BM_DefaultConstructor(benchmark::State& st)
    {
        for (auto _ : st)
        {
            BerthOccupancy<uint64_t, uint64_t> bo(st.range(0));
            benchmark::DoNotOptimize(bo);
        }
    }

    BENCHMARK(BM_DefaultConstructor)->Arg(1024)->Arg(1024 * 1024);

    static void BM_SizeConstructor(benchmark::State& st)
    {
        const size_t n = st.range(0);
        for (auto _ : st)
        {
            BerthOccupancy<uint64_t, uint64_t> bo(n);
            benchmark::DoNotOptimize(bo);
        }
    }

    BENCHMARK(BM_SizeConstructor)->Arg(1024)->Arg(1024 * 1024);

    static void BM_Occupy(benchmark::State& st)
    {
        const size_t n = st.range(0);
        constexpr core::TimeInterval<uint64_t> interval{0, 100};
        const core::SegmentRange<uint64_t> range{0, n / 2};
        for (auto _ : st)
        {
            BerthOccupancy<uint64_t, uint64_t> bo(n);
            bo.Occupy(interval, range);
            benchmark::ClobberMemory();
        }
    }

    BENCHMARK(BM_Occupy)->Arg(1024)->Arg(1024 * 1024);

    static void BM_Free(benchmark::State& st)
    {
        const size_t n = st.range(0);
        constexpr core::TimeInterval<uint64_t> interval{0, 100};
        const core::SegmentRange<uint64_t> range{0, n / 2};
        for (auto _ : st)
        {
            BerthOccupancy<uint64_t, uint64_t> bo(n);
            bo.Free(interval, range);
            benchmark::ClobberMemory();
        }
    }

    BENCHMARK(BM_Free)->Arg(1024)->Arg(1024 * 1024);

    static void BM_IsFree(benchmark::State& st)
    {
        const size_t n = st.range(0);
        constexpr core::TimeInterval<uint64_t> interval{0, 100};
        const core::SegmentRange<uint64_t> range{0, n / 2};
        // pre-populate a mixed timeline
        BerthOccupancy<uint64_t, uint64_t> bo(n);
        bo.Occupy(interval, range);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(bo.IsFree(interval, range));
        }
    }

    BENCHMARK(BM_IsFree)->Arg(1024)->Arg(1024 * 1024);

    static void BM_IsOccupied(benchmark::State& st)
    {
        const size_t n = st.range(0);
        constexpr core::TimeInterval<uint64_t> interval{0, 100};
        const core::SegmentRange<uint64_t> range{0, n / 2};
        BerthOccupancy<uint64_t, uint64_t> bo(n);
        bo.Occupy(interval, range);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(bo.IsOccupied(interval, range));
        }
    }

    BENCHMARK(BM_IsOccupied)->Arg(1024)->Arg(1024 * 1024);

    static void BM_GetQuaySegmentCount(benchmark::State& st)
    {
        const BerthOccupancy<uint64_t, uint64_t> bo(1024);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(bo.GetQuaySegmentCount());
        }
    }

    BENCHMARK(BM_GetQuaySegmentCount);

    static void BM_GetTimeEventCount(benchmark::State& st)
    {
        BerthOccupancy<uint64_t, uint64_t> bo(1024);
        // introduce several splits
        for (uint64_t t = 1; t <= 100; ++t)
        {
            bo.Occupy({t - 1, t}, {0, 1});
        }
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(bo.GetTimeEventCount());
        }
    }

    BENCHMARK(BM_GetTimeEventCount);

    static void BM_PopulatedIsOccupied(benchmark::State& st)
    {
        const size_t num_segments = st.range(0);
        BerthOccupancy<uint64_t, uint64_t> bo(num_segments);

        constexpr uint64_t event_step = 10;
        constexpr size_t num_events = 1000;
        for (size_t k = 0; k < num_events; ++k)
        {
            const uint64_t t0 = k * event_step;
            core::TimeInterval<uint64_t> interval{t0, t0 + event_step};
            core::SegmentRange<uint64_t> range{30, std::min<size_t>(200, num_segments)};
            bo.Occupy(interval, range);
        }

        size_t idx = 0;
        for (auto _ : st)
        {
            // Wrap around our seeded time span
            const uint64_t t0 = (idx * event_step) % (num_events * event_step);
            core::TimeInterval<uint64_t> qti{t0, t0 + event_step};

            core::SegmentRange<uint64_t> qsr{30, std::min<size_t>(200, num_segments)};
            benchmark::DoNotOptimize(bo.IsOccupied(qti, qsr));

            ++idx;
        }
    }

    BENCHMARK(BM_PopulatedIsOccupied)->Arg(1024)->Arg(1024 * 1024);
}

BENCHMARK_MAIN();
