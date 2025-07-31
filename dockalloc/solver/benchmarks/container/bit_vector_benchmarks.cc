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
#include "dockalloc/solver/container/bit_vector.h"

namespace dockalloc::solver
{
    static void BM_DefaultConstructor(benchmark::State& st)
    {
        for (auto _ : st)
        {
            BitVector<uint64_t> bv;
            benchmark::DoNotOptimize(bv);
        }
    }

    BENCHMARK(BM_DefaultConstructor);

    static void BM_SizeConstructor(benchmark::State& st)
    {
        const size_t n = st.range(0);
        for (auto _ : st)
        {
            BitVector<uint64_t> bv(n);
            benchmark::DoNotOptimize(bv);
        }
    }

    BENCHMARK(BM_SizeConstructor)->Arg(1024)->Arg(1024 * 1024);

    static void BM_SizeConstructorAllSet(benchmark::State& st)
    {
        const size_t n = st.range(0);
        for (auto _ : st)
        {
            BitVector<uint64_t> bv(n, true);
            benchmark::DoNotOptimize(bv);
        }
    }

    BENCHMARK(BM_SizeConstructorAllSet)->Arg(1024)->Arg(1024 * 1024);

    static void BM_GetBitCount(benchmark::State& st)
    {
        BitVector<uint64_t> bv(1024 * 1024);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(bv.GetBitCount());
        }
    }

    BENCHMARK(BM_GetBitCount);

    static void BM_GetWordCount(benchmark::State& st)
    {
        BitVector<uint64_t> bv(1024 * 1024);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(bv.GetWordCount());
        }
    }

    BENCHMARK(BM_GetWordCount);

    static void BM_ResizeUpDown(benchmark::State& st)
    {
        BitVector<uint64_t> bv(1024);
        for (auto _ : st)
        {
            bv.Resize(1024 * 1024);
            benchmark::ClobberMemory();
            bv.Resize(1024);
        }
    }

    BENCHMARK(BM_ResizeUpDown);

    static void BM_IsBitSet(benchmark::State& st)
    {
        BitVector<uint64_t> bv(1024 * 1024, true);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(bv.IsBitSet(0));
        }
    }

    BENCHMARK(BM_IsBitSet);

    static void BM_GetBitOperator(benchmark::State& st)
    {
        BitVector<uint64_t> bv(1024 * 1024, true);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(bv[0]);
        }
    }

    BENCHMARK(BM_GetBitOperator);

    static void BM_SetBit(benchmark::State& st)
    {
        BitVector<uint64_t> bv(1024 * 1024, false);
        size_t idx = 0;
        for (auto _ : st)
        {
            bv.SetBit(idx % bv.GetBitCount());
            benchmark::ClobberMemory();
            ++idx;
        }
    }

    BENCHMARK(BM_SetBit);

    static void BM_ClearBit(benchmark::State& st)
    {
        BitVector<uint64_t> bv(1024 * 1024, true);
        size_t idx = 0;
        for (auto _ : st)
        {
            bv.ClearBit(idx % bv.GetBitCount());
            benchmark::ClobberMemory();
            ++idx;
        }
    }

    BENCHMARK(BM_ClearBit);

    static void BM_SetBits(benchmark::State& st)
    {
        BitVector<uint64_t> bv(1024 * 1024, false);
        for (auto _ : st)
        {
            bv.SetBits(0, bv.GetBitCount());
            benchmark::ClobberMemory();
            bv.ClearBits(0, bv.GetBitCount());
        }
    }

    BENCHMARK(BM_SetBits);

    static void BM_AreBitsSet(benchmark::State& st)
    {
        BitVector<uint64_t> bv(1024 * 1024, true);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(bv.AreBitsSet(0, bv.GetBitCount()));
        }
    }

    BENCHMARK(BM_AreBitsSet);

    static void BM_AreBitsClear(benchmark::State& st)
    {
        BitVector<uint64_t> bv(1024 * 1024, false);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(bv.AreBitsClear(0, bv.GetBitCount()));
        }
    }

    BENCHMARK(BM_AreBitsClear);

    static void BM_ClearBits(benchmark::State& st)
    {
        BitVector<uint64_t> bv(1024 * 1024, true);
        for (auto _ : st)
        {
            bv.ClearBits(0, bv.GetBitCount());
            benchmark::ClobberMemory();
            bv.SetBits(0, bv.GetBitCount());
        }
    }

    BENCHMARK(BM_ClearBits);

    static void BM_FindClearRange(benchmark::State& st)
    {
        const BitVector<uint64_t> bv(1024 * 1024, false);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(bv.FindClearRange(0, bv.GetBitCount(), 64));
        }
    }

    BENCHMARK(BM_FindClearRange);

    static void BM_Equality(benchmark::State& st)
    {
        BitVector<uint64_t> a(1024 * 1024, true), b(1024 * 1024, true);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(a == b);
        }
    }

    BENCHMARK(BM_Equality);

    static void BM_Inequality(benchmark::State& st)
    {
        BitVector<uint64_t> a(1024 * 1024, true), b(1024 * 1024, false);
        for (auto _ : st)
        {
            benchmark::DoNotOptimize(a != b);
        }
    }

    BENCHMARK(BM_Inequality);
}

BENCHMARK_MAIN();
