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
#include "dockalloc/solver/include/container/bit_vector.h"

namespace dockalloc::solver
{
    // Benchmark für die Konstruktion des BitVectors
    static void BM_BitVector_Construction(benchmark::State& state)
    {
        const auto size = static_cast<size_t>(state.range(0));

        for (auto _ : state)
        {
            BitVector<uint64_t> bit_vector(size);
            benchmark::DoNotOptimize(bit_vector);
        }

        state.SetComplexityN(size);
    }

    // Benchmark für Einzelbit-Operationen (SetBit)
    static void BM_BitVector_SetBit(benchmark::State& state)
    {
        const auto size = static_cast<size_t>(state.range(0));
        BitVector<uint64_t> bit_vector(size);

        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<size_t> bit_dist(0, size - 1);

        for (auto _ : state)
        {
            const auto bit_index = bit_dist(gen);
            bit_vector.SetBit(bit_index);
            benchmark::DoNotOptimize(bit_vector);
        }

        state.SetComplexityN(size);
    }

    // Benchmark für Einzelbit-Operationen (ClearBit)
    static void BM_BitVector_ClearBit(benchmark::State& state)
    {
        const auto size = static_cast<size_t>(state.range(0));
        BitVector<uint64_t> bit_vector(size, true); // Alle Bits auf 1 setzen

        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<size_t> bit_dist(0, size - 1);

        for (auto _ : state)
        {
            const auto bit_index = bit_dist(gen);
            bit_vector.ClearBit(bit_index);
            benchmark::DoNotOptimize(bit_vector);
        }

        state.SetComplexityN(size);
    }

    // Benchmark für Bereichs-Operationen (SetBits)
    static void BM_BitVector_SetBits(benchmark::State& state)
    {
        const auto size = static_cast<size_t>(state.range(0));
        BitVector<uint64_t> bit_vector(size);

        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<size_t> start_dist(0, size - 1);
        std::uniform_int_distribution<size_t> length_dist(1, size / 10);

        for (auto _ : state)
        {
            const auto start = start_dist(gen);
            const auto length = std::min(length_dist(gen), size - start);
            const auto end = start + length;

            bit_vector.SetBits(start, end);
            benchmark::DoNotOptimize(bit_vector);
        }

        state.SetComplexityN(size);
    }

    // Benchmark für Bereichs-Operationen (ClearBits)
    static void BM_BitVector_ClearBits(benchmark::State& state)
    {
        const auto size = static_cast<size_t>(state.range(0));
        BitVector<uint64_t> bit_vector(size, true);

        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<size_t> start_dist(0, size - 1);
        std::uniform_int_distribution<size_t> length_dist(1, size / 10);

        for (auto _ : state)
        {
            const auto start = start_dist(gen);
            const auto length = std::min(length_dist(gen), size - start);
            const auto end = start + length;

            bit_vector.ClearBits(start, end);
            benchmark::DoNotOptimize(bit_vector);
        }

        state.SetComplexityN(size);
    }

    // Benchmark für Query-Operationen (IsBitSet)
    static void BM_BitVector_IsBitSet(benchmark::State& state)
    {
        const auto size = static_cast<size_t>(state.range(0));
        BitVector<uint64_t> bit_vector(size);

        // Zufällige Bits setzen
        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<size_t> bit_dist(0, size - 1);
        for (size_t i = 0; i < size / 10; ++i)
        {
            bit_vector.SetBit(bit_dist(gen));
        }

        for (auto _ : state)
        {
            const auto bit_index = bit_dist(gen);
            bool result = bit_vector.IsBitSet(bit_index);
            benchmark::DoNotOptimize(result);
        }

        state.SetComplexityN(size);
    }

    // Benchmark für Bereichs-Query-Operationen (AreBitsSet)
    static void BM_BitVector_AreBitsSet(benchmark::State& state)
    {
        const auto size = static_cast<size_t>(state.range(0));
        BitVector<uint64_t> bit_vector(size);

        // Teilweise Bits setzen
        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<size_t> bit_dist(0, size - 1);
        for (size_t i = 0; i < size / 20; ++i)
        {
            const auto start = bit_dist(gen);
            const auto length = std::min(static_cast<size_t>(64), size - start);
            bit_vector.SetBits(start, start + length);
        }

        std::uniform_int_distribution<size_t> start_dist(0, size - 1);
        std::uniform_int_distribution<size_t> length_dist(1, size / 10);

        for (auto _ : state)
        {
            const auto start = start_dist(gen);
            const auto length = std::min(length_dist(gen), size - start);
            const auto end = start + length;

            bool result = bit_vector.AreBitsSet(start, end);
            benchmark::DoNotOptimize(result);
        }

        state.SetComplexityN(size);
    }

    // Benchmark für FindClearRange-Operationen
    static void BM_BitVector_FindClearRange(benchmark::State& state)
    {
        const auto size = static_cast<size_t>(state.range(0));
        BitVector<uint64_t> bit_vector(size);

        // Teilweise besetzen für realistischere Bedingungen
        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<size_t> occupy_start(0, size - 1);
        std::uniform_int_distribution<size_t> occupy_length(1, size / 20);

        for (int i = 0; i < size / 50; ++i)
        {
            const auto start = occupy_start(gen);
            const auto length = std::min(occupy_length(gen), size - start);
            bit_vector.SetBits(start, start + length);
        }

        std::uniform_int_distribution<size_t> find_size_dist(1, size / 10);

        for (auto _ : state)
        {
            const auto find_size = find_size_dist(gen);
            auto result = bit_vector.FindClearRange(0, size, find_size);
            benchmark::DoNotOptimize(result);
        }

        state.SetComplexityN(size);
    }

    // Benchmark für Resize-Operationen
    static void BM_BitVector_Resize(benchmark::State& state)
    {
        const auto initial_size = static_cast<size_t>(state.range(0));
        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<size_t> new_size_dist(initial_size / 2, initial_size * 2);

        for (auto _ : state)
        {
            BitVector<uint64_t> bit_vector(initial_size);
            const auto new_size = new_size_dist(gen);

            bit_vector.Resize(new_size);
            benchmark::DoNotOptimize(bit_vector);
        }

        state.SetComplexityN(initial_size);
    }

    // Benchmark für gemischte Operationen
    static void BM_BitVector_Mixed(benchmark::State& state)
    {
        const auto size = static_cast<size_t>(state.range(0));
        BitVector<uint64_t> bit_vector(size);

        std::random_device rd;
        std::mt19937 gen(rd());
        std::uniform_int_distribution<size_t> start_dist(0, size - 1);
        std::uniform_int_distribution<size_t> length_dist(1, size / 10);
        std::uniform_int_distribution<int> op_dist(0, 5);

        for (auto _ : state)
        {
            const auto start = start_dist(gen);
            const auto length = std::min(length_dist(gen), size - start);
            const auto end = start + length;

            switch (op_dist(gen))
            {
            case 0:
                bit_vector.SetBits(start, end);
                break;
            case 1:
                bit_vector.ClearBits(start, end);
                break;
            case 2:
                {
                    bool result = bit_vector.AreBitsSet(start, end);
                    benchmark::DoNotOptimize(result);
                    break;
                }
            case 3:
                {
                    bool result = bit_vector.AreBitsClear(start, end);
                    benchmark::DoNotOptimize(result);
                    break;
                }
            case 4:
                {
                    auto result = bit_vector.FindClearRange(0, size, length);
                    benchmark::DoNotOptimize(result);
                    break;
                }
            case 5:
                {
                    bool result = bit_vector.IsBitSet(start);
                    benchmark::DoNotOptimize(result);
                    break;
                }
            default: std::abort();
            }
        }

        state.SetComplexityN(size);
    }

    BENCHMARK(BM_BitVector_Construction)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oN);

    BENCHMARK(BM_BitVector_SetBit)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::o1);

    BENCHMARK(BM_BitVector_ClearBit)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::o1);

    BENCHMARK(BM_BitVector_SetBits)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oN);

    BENCHMARK(BM_BitVector_ClearBits)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oN);

    BENCHMARK(BM_BitVector_IsBitSet)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::o1);

    BENCHMARK(BM_BitVector_AreBitsSet)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oN);

    BENCHMARK(BM_BitVector_FindClearRange)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oN);

    BENCHMARK(BM_BitVector_Resize)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oN);

    BENCHMARK(BM_BitVector_Mixed)
        ->RangeMultiplier(2)->Range(64, 1024 * 1024)
        ->Complexity(benchmark::oN);
}

BENCHMARK_MAIN();
