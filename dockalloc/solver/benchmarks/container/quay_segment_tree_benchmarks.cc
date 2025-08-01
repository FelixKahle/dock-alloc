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

#include <benchmark/benchmark.h>
#include <random>
#include <sys/stat.h>

#include "dockalloc/solver/include/container/quay_segment_tree.h"

namespace dockalloc::solver
{
    static void BM_QuaySegmentTree_Construction(benchmark::State& state)
    {
        const auto size = static_cast<uint32_t>(state.range(0));

        for (auto _ : state)
        {
            QuaySegmentTree<uint32_t> tree(size);
            benchmark::DoNotOptimize(tree);
        }

        state.SetComplexityN(size);
    }

    static void BM_QuaySegmentTree_Occupy(benchmark::State& state)
    {
        const auto size = static_cast<uint32_t>(state.range(0));
        QuaySegmentTree<uint32_t> tree(size);

        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<uint32_t> start_dist(0, size - 1);
        std::uniform_int_distribution<uint32_t> length_dist(1, size / 10);

        for (auto _ : state)
        {
            const auto start = start_dist(gen);
            const auto length = std::min(length_dist(gen), size - start);
            const core::SegmentRange<uint32_t> range{start, start + length};

            tree.Occupy(range);
            benchmark::DoNotOptimize(tree);
        }

        state.SetComplexityN(size);
    }

    static void BM_QuaySegmentTree_Free(benchmark::State& state)
    {
        const auto size = static_cast<uint32_t>(state.range(0));
        QuaySegmentTree<uint32_t> tree(size);

        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<uint32_t> start_dist(0, size - 1);
        std::uniform_int_distribution<uint32_t> length_dist(1, size / 10);

        for (auto _ : state)
        {
            const auto start = start_dist(gen);
            const auto length = std::min(length_dist(gen), size - start);
            const core::SegmentRange<uint32_t> range{start, start + length};

            tree.Free(range);
            benchmark::DoNotOptimize(tree);
        }

        state.SetComplexityN(size);
    }

    static void BM_QuaySegmentTree_IsRangeFree(benchmark::State& state)
    {
        const auto size = static_cast<uint32_t>(state.range(0));
        QuaySegmentTree<uint32_t> tree(size);

        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<uint32_t> start_dist(0, size - 1);
        std::uniform_int_distribution<uint32_t> length_dist(1, size / 10);

        for (auto _ : state)
        {
            const auto start = start_dist(gen);
            const auto length = std::min(length_dist(gen), size - start);
            const core::SegmentRange<uint32_t> range{start, start + length};

            bool result = tree.IsRangeFree(range);
            benchmark::DoNotOptimize(result);
        }

        state.SetComplexityN(size);
    }

    static void BM_QuaySegmentTree_FindFree(benchmark::State& state)
    {
        const auto size = static_cast<uint32_t>(state.range(0));
        QuaySegmentTree<uint32_t> tree(size);

        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<uint32_t> occupy_start(0, size - 1);
        std::uniform_int_distribution<uint32_t> occupy_length(1, size / 20);

        for (int i = 0; i < size / 50; ++i)
        {
            const auto start = occupy_start(gen);
            const auto length = std::min(occupy_length(gen), size - start);
            tree.Occupy(core::SegmentRange<uint32_t>{start, start + length});
        }

        std::uniform_int_distribution<uint32_t> find_size_dist(1, size / 10);

        for (auto _ : state)
        {
            const auto find_size = find_size_dist(gen);
            auto result = tree.FindFree(find_size);
            benchmark::DoNotOptimize(result);
        }

        state.SetComplexityN(size);
    }

    static void BM_QuaySegmentTree_Mixed(benchmark::State& state)
    {
        const auto size = static_cast<uint32_t>(state.range(0));
        QuaySegmentTree<uint32_t> tree(size);

        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<uint32_t> start_dist(0, size - 1);
        std::uniform_int_distribution<uint32_t> length_dist(1, size / 10);
        std::uniform_int_distribution<int> op_dist(0, 3);

        for (auto _ : state)
        {
            const auto start = start_dist(gen);
            const auto length = std::min(length_dist(gen), size - start);
            const core::SegmentRange<uint32_t> range{start, start + length};

            switch (op_dist(gen))
            {
            case 0:
                tree.Occupy(range);
                break;
            case 1:
                tree.Free(range);
                break;
            case 2:
                {
                    bool result = tree.IsRangeFree(range);
                    benchmark::DoNotOptimize(result);
                    break;
                }
            case 3:
                {
                    auto result = tree.FindFree(length);
                    benchmark::DoNotOptimize(result);
                    break;
                }
            default: std::abort();
            }
        }

        state.SetComplexityN(size);
    }

    BENCHMARK(BM_QuaySegmentTree_Construction)
    ->RangeMultiplier(2)->Range(64, 1024 * 1024)
    ->Complexity(benchmark::oN);

    BENCHMARK(BM_QuaySegmentTree_Occupy)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oLogN);

    BENCHMARK(BM_QuaySegmentTree_Free)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oLogN);

    BENCHMARK(BM_QuaySegmentTree_IsRangeFree)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oLogN);

    BENCHMARK(BM_QuaySegmentTree_FindFree)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oLogN);

    BENCHMARK(BM_QuaySegmentTree_Mixed)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oLogN);
}

BENCHMARK_MAIN();
