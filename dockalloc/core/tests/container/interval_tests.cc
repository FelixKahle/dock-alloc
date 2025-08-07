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
#include "absl/hash/hash_testing.h"
#include "dockalloc/core/container/interval.h"

namespace dockalloc::core
{
    static_assert(AbslHashable<Interval<int32_t>>, "Interval<int32_t> should be hashable with Absl");
    static_assert(AbslFormattable<Interval<int32_t>>, "Interval<int32_t> should be stringify able with Absl");

    TEST(IntervalTest, ConstructorSwappedValues)
    {
        constexpr Interval i(5, 1);
        EXPECT_EQ(i.GetStart(), 1);
        EXPECT_EQ(i.GetEnd(), 5);
    }

    TEST(IntervalTest, GetStartEnd)
    {
        constexpr Interval i(1.5, 4.5);
        EXPECT_DOUBLE_EQ(i.GetStart(), 1.5);
        EXPECT_DOUBLE_EQ(i.GetEnd(), 4.5);
    }

    TEST(IntervalTest, MidpointIntegerEven)
    {
        constexpr Interval i(2, 6);
        EXPECT_EQ(i.Midpoint(), 4);
    }

    TEST(IntervalTest, MidpointIntegerOdd)
    {
        constexpr Interval i(2, 7);
        // (7 - 2) / 2 = 2, start + 2 = 4
        EXPECT_EQ(i.Midpoint(), 4);
    }

    TEST(IntervalTest, MidpointFloating)
    {
        constexpr Interval i(1.0, 3.0);
        EXPECT_DOUBLE_EQ(i.Midpoint(), 2.0);
    }

    TEST(IntervalTest, MidpointCustomReturnType)
    {
        constexpr Interval i(1, 4);
        constexpr auto mid = i.Midpoint<double>();
        EXPECT_DOUBLE_EQ(mid, 2.5);
    }

    TEST(IntervalTest, IsEmpty)
    {
        constexpr Interval empty(1, 1);
        EXPECT_TRUE(empty.IsEmpty());
        constexpr Interval nonEmpty(1, 2);
        EXPECT_FALSE(nonEmpty.IsEmpty());
    }

    TEST(IntervalTest, Length)
    {
        constexpr Interval i(3, 8);
        EXPECT_EQ(i.Length(), 5);
    }

    TEST(IntervalTest, ContainsValueInsideOutside)
    {
        constexpr Interval i(1, 5);
        EXPECT_TRUE(i.Contains(1));
        EXPECT_TRUE(i.Contains(4));
        EXPECT_FALSE(i.Contains(5));
        EXPECT_FALSE(i.Contains(0));
    }

    TEST(IntervalTest, ContainsIntervalTrueFalse)
    {
        constexpr Interval outer(1, 10);
        constexpr Interval inner(2, 5);
        constexpr Interval overlap(5, 15);
        EXPECT_TRUE(outer.ContainsInterval(inner));
        EXPECT_FALSE(outer.ContainsInterval(overlap));
    }

    TEST(IntervalTest, IntersectsTrueFalse)
    {
        constexpr Interval a(1, 5);
        constexpr Interval b(4, 8);
        constexpr Interval c(5, 10);
        EXPECT_TRUE(a.Intersects(b));
        EXPECT_FALSE(a.Intersects(c));
    }

    TEST(IntervalTest, IntersectionValidAndEmpty)
    {
        constexpr Interval a(1, 5);
        constexpr Interval b(3, 7);
        constexpr auto inter = a.Intersection(b);
        ASSERT_TRUE(inter.has_value());
        EXPECT_EQ(inter.value(), Interval(3, 5));

        constexpr Interval c(5, 10);
        constexpr auto none = a.Intersection(c);
        EXPECT_FALSE(none.has_value());
    }

    TEST(IntervalTest, ClampValidAndEmpty)
    {
        constexpr Interval i(1, 10);
        constexpr Interval boundary(3, 8);
        constexpr auto clamped = i.Clamp(boundary);
        ASSERT_TRUE(clamped.has_value());
        EXPECT_EQ(clamped.value(), Interval(3, 8));

        constexpr Interval disjoint(10, 12);
        constexpr auto emptyOpt = i.Clamp(disjoint);
        EXPECT_FALSE(emptyOpt.has_value());
    }

    TEST(IntervalTest, EqualityInequality)
    {
        constexpr Interval a(2, 6);
        constexpr Interval b(2, 6);
        constexpr Interval c(2.0, 6.0);
        constexpr Interval d(3, 7);

        EXPECT_TRUE(a == b);
        EXPECT_TRUE(a == c);
        EXPECT_FALSE(a != b);
        EXPECT_FALSE(a == d);
    }

    TEST(IntervalTest, AbslStringifyFormat)
    {
        Interval i(1, 3);
        const std::string s = absl::StrFormat("%v", i);
        EXPECT_EQ(s, "[1, 3)");
    }

    TEST(IntervalTest, HashCorrectness)
    {
        const std::vector values = {
            Interval(1, 3),
            Interval(1, 3),
            Interval(2, 4),
        };
        EXPECT_TRUE(absl::VerifyTypeImplementsAbslHashCorrectly(values));
    }
}
