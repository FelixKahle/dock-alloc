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

#include <vector>
#include "gtest/gtest.h"
#include "dockalloc/solver/bit_span.h"
#include "dockalloc/core/memory/aligned_allocator.h"
#if DOCK_ALLOC_SOLVER_BIT_SPAN_USE_SIMD
#include "xsimd/xsimd.hpp"
#endif

namespace dockalloc::solver
{
#if DOCK_ALLOC_SOLVER_BIT_SPAN_USE_SIMD
    static constexpr size_t kAlignment = alignof(xsimd::batch<uint8_t>);
    static_assert(kAlignment >= alignof(uint8_t), "SIMD alignment must be at least the alignment of uint8_t");
#else
    static constexpr size_t kAlignment = alignof(uint8_t);
#endif


    template <typename StorageType, typename Allocator>
        requires std::unsigned_integral<StorageType>
    static size_t CalculateBitCount(const std::vector<StorageType, Allocator>& data)
    {
        return data.size() * std::numeric_limits<StorageType>::digits;
    }

    template <typename StorageType>
        requires std::unsigned_integral<StorageType>
    static StorageType AllSetBits()
    {
        return std::numeric_limits<StorageType>::max();
    }

    template <typename StorageType>
        requires std::unsigned_integral<StorageType>
    static StorageType NoSetBits()
    {
        return StorageType{0};
    }

    TEST(BitSpanTest, IsBitSetWithSetBit)
    {
        std::vector<uint8_t, core::AlignedAllocator<uint8_t, kAlignment>> data(4, std::numeric_limits<uint8_t>::max());
        const size_t bit_count = CalculateBitCount(data);
        const core::AlignedStorage<uint8_t, kAlignment> aligned_storage(data.data());
        const BitSpan<core::AlignedStorage<uint8_t, kAlignment>> span(aligned_storage, bit_count);


        for (size_t i = 0; i < bit_count; i++)
        {
            EXPECT_TRUE(span.IsBitSet(i));
        }
    }

    TEST(BitSpanTest, IsBitSetWithClearBit)
    {
        std::vector<uint8_t, core::AlignedAllocator<uint8_t, kAlignment>> data(4, 0);
        const size_t bit_count = CalculateBitCount(data);
        const core::AlignedStorage<uint8_t, 64> aligned_storage(data.data());
        const BitSpan<core::AlignedStorage<uint8_t, 64>> span(aligned_storage, bit_count);

        for (size_t i = 0; i < bit_count; i++)
        {
            EXPECT_FALSE(span.IsBitSet(i));
        }
    }

    TEST(BitSpanTest, FindFreeRangeZeroLength)
    {
        std::vector<uint8_t, core::AlignedAllocator<uint8_t, kAlignment>> data(2, 0xFF); // all ones, but n=0 is special
        const size_t bit_count = CalculateBitCount(data);
        const core::AlignedStorage<uint8_t, kAlignment> aligned_storage(data.data());
        const BitSpan<core::AlignedStorage<uint8_t, kAlignment>> span(aligned_storage, bit_count);

        // n=0 should return 'from' as long as from < to
        const auto r1 = span.FindClearRange(0, bit_count, 0);
        EXPECT_TRUE(r1.has_value());
        EXPECT_EQ(r1.value(), 0u);

        // if from == to, even n=0 is invalid
        const auto r2 = span.FindClearRange(bit_count, bit_count, 0);
        EXPECT_FALSE(r2.has_value());
    }

    TEST(BitSpanTest, FindFreeRangeAllClear)
    {
        std::vector<uint8_t, core::AlignedAllocator<uint8_t, kAlignment>> data(3, 0x00); // all bits clear
        const size_t bit_count = CalculateBitCount(data);
        const core::AlignedStorage<uint8_t, kAlignment> aligned_storage(data.data());
        const BitSpan<core::AlignedStorage<uint8_t, kAlignment>> span(aligned_storage, bit_count);

        const auto whole = span.FindClearRange(0, bit_count, bit_count);
        EXPECT_TRUE(whole.has_value());
        EXPECT_EQ(whole.value(), 0u);
        const auto too_big = span.FindClearRange(0, bit_count, bit_count + 1);
        EXPECT_FALSE(too_big.has_value());
        const auto sub = span.FindClearRange(4, 4 + 5, 5);
        EXPECT_TRUE(sub.has_value());
        EXPECT_EQ(sub.value(), 4u);
    }

    TEST(BitSpanTest, FindFreeRangeAllSet)
    {
        std::vector<uint8_t, core::AlignedAllocator<uint8_t, kAlignment>> data(5, std::numeric_limits<uint8_t>::max());
        const size_t bit_count = CalculateBitCount(data);
        const core::AlignedStorage<uint8_t, kAlignment> aligned_storage(data.data());
        const BitSpan<core::AlignedStorage<uint8_t, kAlignment>> span(aligned_storage, bit_count);

        for (size_t n = 1; n <= bit_count; ++n)
        {
            auto r = span.FindClearRange(0, bit_count, n);
            EXPECT_FALSE(r.has_value()) << "n=" << n;
        }
    }

    TEST(BitSpanTest, FindFreeRangeSingleWordPattern)
    {
        std::vector<uint8_t, core::AlignedAllocator<uint8_t, kAlignment>> data = {0xF0};
        const size_t bit_count = CalculateBitCount(data);
        const core::AlignedStorage<uint8_t, kAlignment> aligned_storage(data.data());
        const BitSpan<core::AlignedStorage<uint8_t, kAlignment>> span(aligned_storage, bit_count);

        const auto r1 = span.FindClearRange(0, bit_count, 3);
        EXPECT_TRUE(r1.has_value());
        EXPECT_EQ(r1.value(), 0u);

        const auto r2 = span.FindClearRange(0, bit_count, 4);
        EXPECT_TRUE(r2.has_value());
        EXPECT_EQ(r2.value(), 0u);

        const auto r3 = span.FindClearRange(0, bit_count, 5);
        EXPECT_FALSE(r3.has_value());
    }

    TEST(BitSpanTest, FindFreeRangeCrossWord)
    {
        std::vector<uint8_t, core::AlignedAllocator<uint8_t, kAlignment>> data = {0xF0, 0x0F};
        const size_t bit_count = CalculateBitCount(data);
        const core::AlignedStorage<uint8_t, kAlignment> aligned_storage(data.data());
        const BitSpan<core::AlignedStorage<uint8_t, kAlignment>> span(aligned_storage, bit_count);

        const auto r1 = span.FindClearRange(0, bit_count, 4);
        EXPECT_TRUE(r1.has_value());
        EXPECT_EQ(r1.value(), 0u);

        const auto r2 = span.FindClearRange(0, bit_count, 5);
        EXPECT_FALSE(r2.has_value());

        const auto r3 = span.FindClearRange(8, bit_count, 4);
        EXPECT_TRUE(r3.has_value());
        EXPECT_EQ(r3.value(), 12u);
    }
}
