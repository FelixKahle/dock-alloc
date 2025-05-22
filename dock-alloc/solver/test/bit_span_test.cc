// Copyright 2025 Felix Kahle. All rights reserved.

#include <vector>
#include "gtest/gtest.h"
#include "dockalloc/solver/bit_span.h"

namespace dockalloc::solver
{
    template <typename StorageType>
        requires std::unsigned_integral<StorageType>
    static size_t CalculateBitCount(const std::vector<StorageType>& data)
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
        std::vector data(4, std::numeric_limits<uint8_t>::max());
        const size_t bit_count = CalculateBitCount(data);
        const BitSpan bit_span(data.data(), bit_count);


        for (size_t i = 0; i < bit_count; i++)
        {
            EXPECT_TRUE(bit_span.IsBitSet(i));
        }
    }

    TEST(BitSpanTest, IsBitSetWithClearBit)
    {
        std::vector<uint8_t> data(4, 0);
        const size_t bit_count = CalculateBitCount(data);
        const BitSpan bit_span(data.data(), bit_count);

        for (size_t i = 0; i < bit_count; i++)
        {
            EXPECT_FALSE(bit_span.IsBitSet(i));
        }
    }
}
