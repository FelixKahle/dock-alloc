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

#include "gtest/gtest.h"
#include "dockalloc/solver/container/bit_vector.h"

namespace dockalloc::solver
{
    template <typename T>
    class BitVectorTest : public testing::Test
    {
    protected:
        using WordType = T;
        static constexpr int kBits = BitVector<WordType>::kBitsPerWord;
    };

    using WordTypes = testing::Types<uint8_t, uint16_t, uint32_t, uint64_t>;
    TYPED_TEST_SUITE(BitVectorTest, WordTypes);

    TYPED_TEST(BitVectorTest, DefaultConstructor)
    {
        BitVector<TypeParam> bv;
        EXPECT_EQ(bv.GetBitCount(), 0);
    }

    TYPED_TEST(BitVectorTest, ConstructorClear)
    {
        const size_t N = this->kBits * 2 + 3;
        BitVector<TypeParam> bv(N);
        EXPECT_EQ(bv.GetBitCount(), N);
        for (size_t i = 0; i < N; ++i)
        {
            EXPECT_FALSE(bv.IsBitSet(i)) << "bit " << i << " should be clear";
            EXPECT_TRUE(bv.IsBitClear(i)) << "bit " << i << " should be clear";
        }
    }

    TYPED_TEST(BitVectorTest, ConstructorAllSet)
    {
        const size_t N = this->kBits + 5;
        BitVector<TypeParam> bv(N, true);
        EXPECT_EQ(bv.GetBitCount(), N);
        for (size_t i = 0; i < N; ++i)
        {
            EXPECT_TRUE(bv.IsBitSet(i)) << "bit " << i << " should be set";
            EXPECT_FALSE(bv.IsBitClear(i)) << "bit " << i << " should be set";
        }
    }

    TYPED_TEST(BitVectorTest, SetAndClearSingleBits)
    {
        const size_t N = this->kBits + 1;
        BitVector<TypeParam> bv(N);
        bv.SetBit(0);
        bv.SetBit(N - 1);
        EXPECT_TRUE(bv.GetBit(0));
        EXPECT_TRUE(bv.GetBit(N-1));
        bv.ClearBit(0);
        bv.ClearBit(N - 1);
        EXPECT_FALSE(bv.GetBit(0));
        EXPECT_FALSE(bv.GetBit(N-1));
    }

    TYPED_TEST(BitVectorTest, AreBitsSetAndClear)
    {
        const size_t N = this->kBits * 3;
        BitVector<TypeParam> bv(N);
        EXPECT_TRUE(bv.AreBitsClear(0, N));
        EXPECT_FALSE(bv.AreBitsSet(0, N));
        bv.SetBits(this->kBits / 2, this->kBits + this->kBits / 2);
        EXPECT_TRUE(bv.AreBitsSet(this->kBits/2, this->kBits + this->kBits/2));
        EXPECT_FALSE(bv.AreBitsSet(0, N));
        EXPECT_FALSE(bv.AreBitsClear(this->kBits/2, this->kBits + this->kBits/2));
    }

    TYPED_TEST(BitVectorTest, RangeSetAndClear)
    {
        const size_t N = this->kBits * 2;
        BitVector<TypeParam> bv(N);
        const size_t from = this->kBits - 3;
        const size_t to = this->kBits + 4;
        bv.SetBits(from, to);
        for (size_t i = from; i < to; ++i)
        {
            EXPECT_TRUE(bv[i]) << "bit " << i << " should be set";
        }
        bv.ClearBits(from + 2, to - 2);
        for (size_t i = from + 2; i < to - 2; ++i)
        {
            EXPECT_FALSE(bv[i]) << "bit " << i << " should be clear";
        }
        EXPECT_TRUE(bv[from]);
        EXPECT_TRUE(bv[to-1]);
    }

    TYPED_TEST(BitVectorTest, ProxyReferenceAssignment)
    {
        constexpr size_t N = 10;
        BitVector<TypeParam> bv(N);
        bv[3] = true;
        EXPECT_TRUE(bv[3]);
        bv[3] = false;
        EXPECT_FALSE(bv[3]);
        bv[5] = true;
        bv[7] = bv[5];
        EXPECT_TRUE(bv[7]);
    }

    TYPED_TEST(BitVectorTest, FindClearRangeSimple)
    {
        const size_t N = this->kBits + 5;
        BitVector<TypeParam> bv(N, true);
        bv.ClearBits(4, 4 + 3);
        auto opt = bv.FindClearRange(0, N, 3);
        ASSERT_TRUE(opt.has_value());
        EXPECT_EQ(opt.value(), 4u);
        EXPECT_FALSE(bv.FindClearRange(0, N, N+1).has_value());
        auto zero = bv.FindClearRange(2, 5, 0);
        ASSERT_TRUE(zero.has_value());
        EXPECT_EQ(zero.value(), 2u);
    }

    TYPED_TEST(BitVectorTest, ResizeUpAndDown)
    {
        BitVector<TypeParam> bv(5, true);
        bv.Resize(10, false);
        EXPECT_EQ(bv.GetBitCount(), 10u);
        for (size_t i = 5; i < 10; ++i)
        {
            EXPECT_FALSE(bv[i]);
        }
        bv.Resize(15, true);
        for (size_t i = 10; i < 15; ++i)
        {
            EXPECT_TRUE(bv[i]);
        }
        // shrink
        bv.Resize(7);
        EXPECT_EQ(bv.GetBitCount(), 7u);
        // kBits beyond 7 are inaccessible
        // shrink to zero
        bv.Resize(0);
        EXPECT_EQ(bv.GetBitCount(), 0u);
    }

    TYPED_TEST(BitVectorTest, ConstAndNonConstAccess)
    {
        constexpr size_t N = 8;
        BitVector<TypeParam> bv(N);
        bv.SetBits(2, 5);
        const BitVector<TypeParam>& cbv = bv;
        for (size_t i = 0; i < N; ++i)
        {
            EXPECT_EQ(static_cast<bool>(cbv[i]), bv[i]);
        }
    }

    TYPED_TEST(BitVectorTest, EqualityOperator)
    {
        {
            const auto K = static_cast<size_t>(this->kBits);
            const size_t N = K + 7;
            BitVector<TypeParam> a(N), b(N);

            const std::vector<size_t> positions = {
                static_cast<size_t>(0),
                static_cast<size_t>(3),
                static_cast<size_t>(K - 1),
                static_cast<size_t>(N - 1)
            };
            for (size_t p : positions)
            {
                a.SetBit(p);
                b.SetBit(p);
            }
            EXPECT_TRUE(a == b);
            EXPECT_FALSE(a != b);
        }
        {
            BitVector<TypeParam> a1(10), b1(11);
            EXPECT_FALSE(a1 == b1);
            EXPECT_TRUE(a1 != b1);
            const auto K = static_cast<size_t>(this->kBits);
            const size_t N = K + 5;
            BitVector<TypeParam> a2(N, true), b2(N, true);

            const auto flip = static_cast<size_t>(2 * sizeof(TypeParam));
            a2.ClearBit(flip);

            EXPECT_FALSE(a2 == b2);
            EXPECT_TRUE(a2 != b2);
        }
    }
}
