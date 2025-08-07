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

#include <gtest/gtest.h>
#include <vector>
#include <algorithm>
#include <iterator>
#include "dockalloc/solver/container/bit_vector.h"

namespace dockalloc::solver
{
    template <typename T>
    class BitVectorTest : public testing::Test
    {
    protected:
        using WordType = T;
        using BitVectorType = BitVector<WordType>;
        static constexpr int kBits = BitVectorType::kBitsPerWord;
    };

    using WordTypes = testing::Types<uint8_t, uint16_t, uint32_t, uint64_t>;
    TYPED_TEST_SUITE(BitVectorTest, WordTypes);

    TYPED_TEST(BitVectorTest, DefaultConstructor)
    {
        BitVector<TypeParam> bv;
        EXPECT_EQ(bv.GetBitCount(), 0u);
        EXPECT_EQ(bv.GetWordCount(), 0u);
    }

    TYPED_TEST(BitVectorTest, SizedConstructorZero)
    {
        constexpr size_t n = BitVectorTest<TypeParam>::kBits * 3 + 5;
        BitVector<TypeParam> bv(n);
        EXPECT_EQ(bv.GetBitCount(), n);
        EXPECT_EQ(bv.GetWordCount(), (n + BitVectorTest<TypeParam>::kBits - 1) / BitVectorTest<TypeParam>::kBits);
        // all bits must be zero
        for (size_t i = 0; i < n; ++i)
        {
            EXPECT_FALSE(bv.GetBit(i));
        }
    }

    TYPED_TEST(BitVectorTest, SizedConstructorAllOnes)
    {
        constexpr size_t n = BitVectorTest<TypeParam>::kBits * 2 + 7;
        BitVector<TypeParam> bv(n, true);
        EXPECT_EQ(bv.GetBitCount(), n);
        // bits beyond last valid should remain zero after mask
        for (size_t i = 0; i < n; ++i)
        {
            EXPECT_TRUE(bv.GetBit(i));
        }
    }

    TYPED_TEST(BitVectorTest, ClearAndSetAll)
    {
        BitVector<TypeParam> bv(100);
        bv.SetAll(true);
        for (size_t i = 0; i < 100; ++i)
            EXPECT_TRUE(bv.IsBitSet(i));
        bv.SetAll(false);
        for (size_t i = 0; i < 100; ++i)
            EXPECT_FALSE(bv.IsBitSet(i));
        bv.Clear();
        EXPECT_EQ(bv.GetBitCount(), 0u);
        EXPECT_EQ(bv.GetWordCount(), 0u);
    }

    TYPED_TEST(BitVectorTest, ResizeGrowShrink)
    {
        BitVector<TypeParam> bv(10, false);
        bv.Resize(20, true);
        EXPECT_EQ(bv.GetBitCount(), 20u);
        for (size_t i = 0; i < 10; ++i)
            EXPECT_FALSE(bv.IsBitSet(i));
        for (size_t i = 10; i < 20; ++i)
            EXPECT_TRUE(bv.IsBitSet(i));
        bv.Resize(5);
        EXPECT_EQ(bv.GetBitCount(), 5u);
        for (size_t i = 0; i < 5; ++i)
            EXPECT_FALSE(bv.IsBitSet(i));
    }

    TYPED_TEST(BitVectorTest, SetClearBit)
    {
        BitVector<TypeParam> bv(16);
        bv.SetBit(3);
        EXPECT_TRUE(bv.IsBitSet(3));
        bv.ClearBit(3);
        EXPECT_FALSE(bv.IsBitSet(3));
    }

    TYPED_TEST(BitVectorTest, SetClearBitsRange)
    {
        BitVector<TypeParam> bv(64);
        bv.SetBits(5, 15);
        EXPECT_TRUE(bv.AreBitsSet(5, 15));
        EXPECT_FALSE(bv.AreBitsClear(5, 15));
        bv.ClearBits(8, 12);
        EXPECT_FALSE(bv.AreBitsSet(5, 15));
        EXPECT_TRUE(bv.AreBitsClear(8, 12));
    }

    TYPED_TEST(BitVectorTest, FindFirstClearRange)
    {
        BitVector<TypeParam> bv(32, true);
        EXPECT_EQ(bv.FindFirstClearRange(0, 32, 1), std::nullopt);
        bv.ClearBits(10, 15);
        auto found = bv.FindFirstClearRange(0, 32, 3);
        ASSERT_TRUE(found.has_value());
        EXPECT_EQ(found.value(), 10u);
    }

    TYPED_TEST(BitVectorTest, OperatorBracketAndAssignment)
    {
        BitVector<TypeParam> bv(8);
        bv[2] = true;
        EXPECT_TRUE(bv[2]);
        bv[2] = false;
        EXPECT_FALSE(static_cast<bool>(bv[2]));
        // copy assignment
        bv[4] = bv[2];
        EXPECT_FALSE(bv[4]);
    }

    TYPED_TEST(BitVectorTest, BitwiseAndOperators)
    {
        BitVector<TypeParam> a(16, true);
        BitVector<TypeParam> b(16, false);
        b.SetBits(4, 8);
        auto c = a & b;
        for (size_t i = 0; i < 16; ++i)
        {
            EXPECT_EQ(c.IsBitSet(i), b.IsBitSet(i));
        }
        a &= b;
        EXPECT_EQ(a, c);
    }

    TYPED_TEST(BitVectorTest, EqualityInequality)
    {
        BitVector<TypeParam> x(20, true);
        BitVector<TypeParam> y(20, true);
        EXPECT_TRUE(x == y);
        EXPECT_FALSE(x != y);
        y.ClearBit(5);
        EXPECT_FALSE(x == y);
        EXPECT_TRUE(x != y);
    }

    TYPED_TEST(BitVectorTest, IteratorTraversal)
    {
        constexpr size_t n = 20;
        BitVector<TypeParam> bv(n, false);
        // set even bits
        for (size_t i = 0; i < n; i += 2)
        {
            bv.SetBit(i);
        }
        size_t idx = 0;
        for (bool bit : bv)
        {
            EXPECT_EQ(bit, (idx % 2 == 0));
            ++idx;
        }
        EXPECT_EQ(idx, n);
    }

    TYPED_TEST(BitVectorTest, FreeRangeIteratorBasicIteration)
    {
        using BitVectorType = typename TestFixture::BitVectorType;
        BitVectorType bv(100); // All bits are initially clear (0)

        // Create two blocks of set bits, leaving three free ranges:
        // [0, 15), [25, 60), [70, 100)
        bv.SetBits(15, 25);
        bv.SetBits(60, 70);

        constexpr size_t search_len = 10;
        std::vector<size_t> found_positions;
        std::vector<size_t> expected_positions;

        // Expected positions from range [0, 15) -> last start is 15-10=5
        for (size_t i = 0; i <= 5; ++i)
        {
            expected_positions.push_back(i);
        }
        // Expected positions from range [25, 60) -> last start is 60-10=50
        for (size_t i = 25; i <= 50; ++i)
        {
            expected_positions.push_back(i);
        }
        // Expected positions from range [70, 100) -> last start is 100-10=90
        for (size_t i = 70; i <= 90; ++i)
        {
            expected_positions.push_back(i);
        }

        for (auto it = bv.BeginFreeRanges(search_len); it != bv.EndFreeRanges(); ++it)
        {
            found_positions.push_back(*it);
        }

        EXPECT_EQ(found_positions.size(), expected_positions.size());
        EXPECT_EQ(found_positions, expected_positions);
    }

    TYPED_TEST(BitVectorTest, FreeRangeIteratorEdgeCases)
    {
        using BitVectorType = typename TestFixture::BitVectorType;

        // Case 1: Vector is completely full. Iterator should be empty.
        {
            BitVectorType bv(50, true);
            auto begin = bv.BeginFreeRanges(1);
            auto end = bv.EndFreeRanges();
            EXPECT_EQ(begin, end);
        }
        // Case 2: Vector is completely empty. Should yield all possible positions.
        {
            BitVectorType bv(40, false);
            constexpr size_t search_len = 10;
            std::vector<size_t> found_positions;
            // Expected: 0, 1, ..., 30. (40 - 10)
            for (auto it = bv.BeginFreeRanges(search_len); it != bv.EndFreeRanges(); ++it)
            {
                found_positions.push_back(*it);
            }
            EXPECT_EQ(found_positions.size(), 31u);
            EXPECT_EQ(found_positions.front(), 0u);
            EXPECT_EQ(found_positions.back(), 30u);
        }
        // Case 3: Search length is too long to fit.
        {
            BitVectorType bv(100, false);
            auto begin = bv.BeginFreeRanges(101); // Search for 101 in a 100-bit vector
            auto end = bv.EndFreeRanges();
            EXPECT_EQ(begin, end);
        }
        // Case 4: No single free range is long enough.
        {
            BitVectorType bv(100, false);
            // Create free blocks of 9 bits separated by 1 set bit.
            for (size_t i = 9; i < 100; i += 10)
            {
                bv.SetBit(i);
            }
            auto begin = bv.BeginFreeRanges(10); // Search for a 10-bit block
            auto end = bv.EndFreeRanges();
            EXPECT_EQ(begin, end);
        }
    }
}
