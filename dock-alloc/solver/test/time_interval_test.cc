// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/time_interval.h"

namespace dockalloc::solver
{
    TEST(TimeInterval, InitializesCorrectly)
    {
        constexpr TimeInterval<uint32_t> first_interval(1, 5);
        EXPECT_EQ(first_interval.GetStart(), 1);
        EXPECT_EQ(first_interval.GetEnd(), 5);

        constexpr TimeInterval<uint32_t> second_interval(10, 8);
        EXPECT_EQ(second_interval.GetStart(), 8);
        EXPECT_EQ(second_interval.GetEnd(), 10);

        constexpr TimeInterval<uint32_t> third_interval = first_interval;
        EXPECT_EQ(third_interval.GetStart(), 1);
        EXPECT_EQ(third_interval.GetEnd(), 5);

        constexpr auto fourth_interval = TimeInterval<uint32_t>(1, 5);
        EXPECT_EQ(fourth_interval.GetStart(), 1);
        EXPECT_EQ(fourth_interval.GetEnd(), 5);
    }

    TEST(TimeInterval, Duration)
    {
        constexpr TimeInterval<uint32_t> first_interval(1, 5);
        EXPECT_EQ(first_interval.GetDuration(), 4);

        constexpr TimeInterval<uint32_t> second_interval(10, 10);
        EXPECT_EQ(second_interval.GetDuration(), 0);
    }

    TEST(TimeInterval, Midpoint)
    {
        constexpr TimeInterval<uint32_t> int_interval(2, 6);
        EXPECT_EQ(int_interval.GetMidpoint(), 4);

        constexpr TimeInterval<float> float_interval(2.5, 7.5);
        EXPECT_DOUBLE_EQ(float_interval.GetMidpoint(), 5.0);
    }

    TEST(TimeInterval, IsEmpty)
    {
        constexpr TimeInterval<uint32_t> interval(3, 3);
        EXPECT_TRUE(interval.IsEmpty());

        constexpr TimeInterval<uint32_t> non_empty(2, 5);
        EXPECT_FALSE(non_empty.IsEmpty());
    }

    TEST(TimeInterval, EqualityAndInequality)
    {
        constexpr TimeInterval<uint32_t> a(1, 5);
        constexpr TimeInterval<uint32_t> b(1, 5);
        constexpr TimeInterval<uint32_t> c(2, 6);

        EXPECT_TRUE(a == b);
        EXPECT_FALSE(a != b);
        EXPECT_FALSE(a == c);
        EXPECT_TRUE(a != c);
    }

    TEST(TimeInterval, ContainsPoint)
    {
        constexpr TimeInterval<uint32_t> interval(3, 7);

        EXPECT_TRUE(interval.Contains(3));
        EXPECT_TRUE(interval.Contains(5));
        EXPECT_TRUE(interval.Contains(7));
        EXPECT_FALSE(interval.Contains(2));
        EXPECT_FALSE(interval.Contains(8));
    }

    TEST(TimeInterval, ContainsInterval)
    {
        constexpr TimeInterval<uint32_t> outer(2, 10);
        constexpr TimeInterval<uint32_t> inner(4, 8);
        constexpr TimeInterval<uint32_t> edge_touch(2, 10);
        constexpr TimeInterval<uint32_t> outside(0, 11);

        EXPECT_TRUE(outer.Contains(inner));
        EXPECT_TRUE(outer.Contains(edge_touch));
        EXPECT_FALSE(outer.Contains(outside));
    }

    TEST(TimeInterval, Intersects)
    {
        constexpr TimeInterval<uint32_t> a(1, 5);
        constexpr TimeInterval<uint32_t> b(4, 8);
        constexpr TimeInterval<uint32_t> c(6, 9);
        constexpr TimeInterval<uint32_t> d(5, 5);

        EXPECT_TRUE(a.Intersects(b));
        EXPECT_FALSE(a.Intersects(c));
        EXPECT_TRUE(a.Intersects(d));
    }

    TEST(TimeInterval, Intersection)
    {
        constexpr TimeInterval<uint32_t> a(1, 5);
        constexpr TimeInterval<uint32_t> b(3, 7);

        constexpr auto result = a.Intersection(b);

        ASSERT_TRUE(result.has_value());
        EXPECT_EQ(result->GetStart(), 3);
        EXPECT_EQ(result->GetEnd(), 5);

        constexpr TimeInterval<uint32_t> c(6, 8);
        constexpr auto no_result = a.Intersection(c);

        EXPECT_FALSE(no_result.has_value());
    }

    TEST(TimeInterval, ShiftBy)
    {
        constexpr TimeInterval<uint32_t> interval(5, 10);
        constexpr auto shifted = interval.ShiftBy(3);

        EXPECT_EQ(shifted.GetStart(), 8);
        EXPECT_EQ(shifted.GetEnd(), 13);
    }

    TEST(TimeInterval, Clamp)
    {
        constexpr TimeInterval<uint32_t> source(5, 15);
        constexpr TimeInterval<uint32_t> bounds(8, 12);
        constexpr auto clamped = source.Clamp(bounds);

        ASSERT_TRUE(clamped.has_value());
        EXPECT_EQ(clamped->GetStart(), 8);
        EXPECT_EQ(clamped->GetEnd(), 12);

        constexpr TimeInterval<uint32_t> outside(1, 3);
        constexpr auto fail = outside.Clamp(bounds);
        EXPECT_FALSE(fail.has_value());
    }

    TEST(TimeInterval, AbslStringify)
    {
        constexpr TimeInterval<uint32_t> interval(4, 10);
        const std::string formatted = absl::StrFormat("%v", interval);
        EXPECT_EQ(formatted, "[4, 10]");
    }
}
