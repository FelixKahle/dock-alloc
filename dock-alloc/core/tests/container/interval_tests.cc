// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "absl/hash/hash_testing.h"
#include "dockalloc/core/container/interval.h"

namespace dockalloc::core
{
    TEST(IntervalTest, ConstructorSwappedValues)
    {
        constexpr Interval<int> i(5, 1);
        EXPECT_EQ(i.GetStart(), 1);
        EXPECT_EQ(i.GetEnd(), 5);
    }

    TEST(IntervalTest, GetStartEnd)
    {
        constexpr Interval<double> i(1.5, 4.5);
        EXPECT_DOUBLE_EQ(i.GetStart(), 1.5);
        EXPECT_DOUBLE_EQ(i.GetEnd(), 4.5);
    }

    TEST(IntervalTest, MidpointIntegerEven)
    {
        constexpr Interval<int> i(2, 6);
        EXPECT_EQ(i.Midpoint(), 4);
    }

    TEST(IntervalTest, MidpointIntegerOdd)
    {
        constexpr Interval<int> i(2, 7);
        // (7 - 2) / 2 = 2, start + 2 = 4
        EXPECT_EQ(i.Midpoint(), 4);
    }

    TEST(IntervalTest, MidpointFloating)
    {
        constexpr Interval<double> i(1.0, 3.0);
        EXPECT_DOUBLE_EQ(i.Midpoint(), 2.0);
    }

    TEST(IntervalTest, MidpointCustomReturnType)
    {
        constexpr Interval<int> i(1, 4);
        constexpr double mid = i.Midpoint<double>();
        EXPECT_DOUBLE_EQ(mid, 2.5);
    }

    TEST(IntervalTest, IsEmpty)
    {
        constexpr Interval<int> empty(1, 1);
        EXPECT_TRUE(empty.IsEmpty());
        constexpr Interval<int> nonEmpty(1, 2);
        EXPECT_FALSE(nonEmpty.IsEmpty());
    }

    TEST(IntervalTest, Length)
    {
        constexpr Interval<int> i(3, 8);
        EXPECT_EQ(i.Length(), 5);
    }

    TEST(IntervalTest, ContainsValueInsideOutside)
    {
        constexpr Interval<int> i(1, 5);
        EXPECT_TRUE(i.Contains(1));
        EXPECT_TRUE(i.Contains(4));
        EXPECT_FALSE(i.Contains(5));
        EXPECT_FALSE(i.Contains(0));
    }

    TEST(IntervalTest, ContainsIntervalTrueFalse)
    {
        constexpr Interval<int> outer(1, 10);
        constexpr Interval<int> inner(2, 5);
        constexpr Interval<int> overlap(5, 15);
        EXPECT_TRUE(outer.ContainsInterval(inner));
        EXPECT_FALSE(outer.ContainsInterval(overlap));
    }

    TEST(IntervalTest, IntersectsTrueFalse)
    {
        constexpr Interval<int> a(1, 5);
        constexpr Interval<int> b(4, 8);
        constexpr Interval<int> c(5, 10);
        EXPECT_TRUE(a.Intersects(b));
        EXPECT_FALSE(a.Intersects(c));
    }

    TEST(IntervalTest, IntersectionValidAndEmpty)
    {
        constexpr Interval<int> a(1, 5);
        constexpr Interval<int> b(3, 7);
        constexpr auto inter = a.Intersection(b);
        ASSERT_TRUE(inter.has_value());
        EXPECT_EQ(inter.value(), Interval<int>(3, 5));

        constexpr Interval<int> c(5, 10);
        constexpr auto none = a.Intersection(c);
        EXPECT_FALSE(none.has_value());
    }

    TEST(IntervalTest, ClampValidAndEmpty)
    {
        constexpr Interval<int> i(1, 10);
        constexpr Interval<int> boundary(3, 8);
        constexpr auto clamped = i.Clamp(boundary);
        ASSERT_TRUE(clamped.has_value());
        EXPECT_EQ(clamped.value(), Interval<int>(3, 8));

        constexpr Interval<int> disjoint(10, 12);
        constexpr auto emptyOpt = i.Clamp(disjoint);
        EXPECT_FALSE(emptyOpt.has_value());
    }

    TEST(IntervalTest, EqualityInequality)
    {
        constexpr Interval<int> a(2, 6);
        constexpr Interval<int> b(2, 6);
        constexpr Interval<double> c(2.0, 6.0);
        constexpr Interval<int> d(3, 7);

        EXPECT_TRUE(a == b);
        EXPECT_TRUE(a == c);
        EXPECT_FALSE(a != b);
        EXPECT_FALSE(a == d);
    }

    TEST(IntervalTest, AbslStringifyFormat)
    {
        Interval<int> i(1, 3);
        const std::string s = absl::StrFormat("%v", i);
        EXPECT_EQ(s, "[1, 3)");
    }

    TEST(IntervalTest, HashCorrectness)
    {
        const std::vector<Interval<int>> values = {
            Interval<int>(1, 3),
            Interval<int>(1, 3),
            Interval<int>(2, 4),
        };
        EXPECT_TRUE(absl::VerifyTypeImplementsAbslHashCorrectly(values));
    }
}
