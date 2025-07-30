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
#include "dockalloc/solver/container/free_interval.h"

namespace dockalloc::solver
{
    // Test fixture for FreeInterval to avoid repeating common setup
    template <typename T>
    class FreeIntervalTest : public ::testing::Test
    {
    };

    // Define a typed test suite for different unsigned integral types
    using FreeIntervalTypes = ::testing::Types<uint8_t, uint16_t, uint32_t, uint64_t>;
    TYPED_TEST_SUITE(FreeIntervalTest, FreeIntervalTypes);

    // Test default constructor
    TYPED_TEST(FreeIntervalTest, DefaultConstructor)
    {
        FreeInterval<TypeParam> interval{};
        EXPECT_EQ(interval.GetStart(), static_cast<TypeParam>(0));
        EXPECT_EQ(interval.GetLength(), static_cast<TypeParam>(0));
        EXPECT_TRUE(interval.IsEmpty());
        EXPECT_EQ(interval.End(), static_cast<TypeParam>(0));
    }

    // Test parameterized constructor and getters
    TYPED_TEST(FreeIntervalTest, ParameterizedConstructorAndGetters)
    {
        FreeInterval<TypeParam> interval(static_cast<TypeParam>(10), static_cast<TypeParam>(5));
        EXPECT_EQ(interval.GetStart(), static_cast<TypeParam>(10));
        EXPECT_EQ(interval.GetLength(), static_cast<TypeParam>(5));
        EXPECT_FALSE(interval.IsEmpty());
        EXPECT_EQ(interval.End(), static_cast<TypeParam>(15));
    }

    // Test IsEmpty method
    TYPED_TEST(FreeIntervalTest, IsEmpty)
    {
        FreeInterval<TypeParam> empty_interval(static_cast<TypeParam>(0), static_cast<TypeParam>(0));
        EXPECT_TRUE(empty_interval.IsEmpty());

        FreeInterval<TypeParam> non_empty_interval(static_cast<TypeParam>(1), static_cast<TypeParam>(1));
        EXPECT_FALSE(non_empty_interval.IsEmpty());

        FreeInterval<TypeParam> zero_length_interval(static_cast<TypeParam>(100), static_cast<TypeParam>(0));
        EXPECT_TRUE(zero_length_interval.IsEmpty());
    }

    // Test equality operator (==)
    TYPED_TEST(FreeIntervalTest, EqualityOperator)
    {
        FreeInterval<TypeParam> interval1(static_cast<TypeParam>(0), static_cast<TypeParam>(0));
        FreeInterval<TypeParam> interval2(static_cast<TypeParam>(0), static_cast<TypeParam>(0));
        FreeInterval<TypeParam> interval3(static_cast<TypeParam>(10), static_cast<TypeParam>(5));
        FreeInterval<TypeParam> interval4(static_cast<TypeParam>(10), static_cast<TypeParam>(5));
        FreeInterval<TypeParam> interval5(static_cast<TypeParam>(10), static_cast<TypeParam>(6)); // Different length
        FreeInterval<TypeParam> interval6(static_cast<TypeParam>(11), static_cast<TypeParam>(5)); // Different start

        EXPECT_TRUE(interval1 == interval2);
        EXPECT_TRUE(interval3 == interval4);
        EXPECT_FALSE(interval3 == interval5);
        EXPECT_FALSE(interval3 == interval6);
        EXPECT_FALSE(interval1 == interval3);
    }

    // Test inequality operator (!=)
    TYPED_TEST(FreeIntervalTest, InequalityOperator)
    {
        FreeInterval<TypeParam> interval1(static_cast<TypeParam>(0), static_cast<TypeParam>(0));
        FreeInterval<TypeParam> interval2(static_cast<TypeParam>(10), static_cast<TypeParam>(5));
        FreeInterval<TypeParam> interval3(static_cast<TypeParam>(10), static_cast<TypeParam>(6));

        EXPECT_TRUE(interval1 != interval2);
        EXPECT_TRUE(interval2 != interval3);
        EXPECT_FALSE(interval1 != FreeInterval<TypeParam>(static_cast<TypeParam>(0), static_cast<TypeParam>(0)));
    }

    // Test less-than operator (<)
    TYPED_TEST(FreeIntervalTest, LessThanOperator)
    {
        FreeInterval<TypeParam> interval1(static_cast<TypeParam>(10), static_cast<TypeParam>(5));
        FreeInterval<TypeParam> interval2(static_cast<TypeParam>(10), static_cast<TypeParam>(6));
        // Same start, greater length
        FreeInterval<TypeParam> interval3(static_cast<TypeParam>(11), static_cast<TypeParam>(5));
        // Greater start, same length
        FreeInterval<TypeParam> interval4(static_cast<TypeParam>(9), static_cast<TypeParam>(5));
        // Smaller start, same length

        EXPECT_TRUE(interval1 < interval2);
        EXPECT_TRUE(interval1 < interval3);
        EXPECT_FALSE(interval1 < interval4);
        EXPECT_FALSE(interval1 < interval1); // Not strictly less than
    }

    // Test Abseil stringify function
    TYPED_TEST(FreeIntervalTest, AbslStringify)
    {
        FreeInterval<TypeParam> interval1(static_cast<TypeParam>(0), static_cast<TypeParam>(0));
        EXPECT_EQ(absl::StrFormat("%v", interval1), "[0, 0)");

        FreeInterval<TypeParam> interval2(static_cast<TypeParam>(10), static_cast<TypeParam>(5));
        EXPECT_EQ(absl::StrFormat("%v", interval2), "[10, 15)");

        FreeInterval<TypeParam> interval3(static_cast<TypeParam>(100), static_cast<TypeParam>(0));
        EXPECT_EQ(absl::StrFormat("%v", interval3), "[100, 100)");

        // Test with max values for the type
        FreeInterval<TypeParam> interval4(std::numeric_limits<TypeParam>::max() - static_cast<TypeParam>(10),
                                          static_cast<TypeParam>(10));
        EXPECT_EQ(absl::StrFormat("%v", interval4),
                  absl::StrFormat("[%v, %v)", std::numeric_limits<TypeParam>::max() - static_cast<TypeParam>(10),
                      std::numeric_limits<TypeParam>::max()));
    }
}
