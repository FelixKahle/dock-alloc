// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/time_interval.h"

namespace dockalloc::solver
{
    TEST(TimeIntervalTest, ConstructsCorrectly)
    {
        constexpr TimeInterval<uint32_t> interval(5, 10);
        EXPECT_EQ(interval.GetStart(), 5);
        EXPECT_EQ(interval.GetEnd(), 10);
    }

    TEST(TimeIntervalTest, MidpointIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval1(10, 20);
        EXPECT_EQ(interval1.Midpoint(), 15);

        constexpr TimeInterval<uint32_t> interval2(5, 10);
        EXPECT_EQ(interval2.Midpoint<double>(), 7.5);
    }

    TEST(TimeIntervalTest, IsEmptyIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval1(5, 10);
        EXPECT_FALSE(interval1.IsEmpty());

        constexpr TimeInterval<uint32_t> interval2(5, 5);
        EXPECT_TRUE(interval2.IsEmpty());
    }

    TEST(TimeIntervalTest, DurationIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval(5, 10);
        EXPECT_EQ(interval.Duration(), 5);
    }

    TEST(TimeIntervalTest, ContainsIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval(2, 100);
        for (uint32_t i = 2; i < 100; ++i)
        {
            EXPECT_TRUE(interval.Contains(i));
        }
        EXPECT_FALSE(interval.Contains(1));
        EXPECT_FALSE(interval.Contains(100));
        EXPECT_FALSE(interval.Contains(101));
    }

    TEST(TimeIntervalTest, ContainsIntervalIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval1(2, 100);
        constexpr TimeInterval<uint32_t> interval2(5, 10);

        EXPECT_TRUE(interval1.ContainsInterval(interval2));
        EXPECT_FALSE(interval2.ContainsInterval(interval1));

        constexpr TimeInterval<uint32_t> interval3(5, 105);
        EXPECT_FALSE(interval1.ContainsInterval(interval3));
    }

    TEST(TimeIntervalTest, IntersectsIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval1(2, 100);
        constexpr TimeInterval<uint32_t> interval2(5, 10);
        EXPECT_TRUE(interval1.Intersects(interval2));

        constexpr TimeInterval<uint32_t> interval3(101, 200);
        EXPECT_FALSE(interval1.Intersects(interval3));
    }

    TEST(TimeIntervalTest, IntersectionIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval1(2, 100);
        constexpr TimeInterval<uint32_t> interval2(5, 10);
        constexpr auto intersection = interval1.Intersection(interval2);

        ASSERT_TRUE(intersection.has_value());
        EXPECT_EQ(intersection->GetStart(), 5);
        EXPECT_EQ(intersection->GetEnd(), 10);

        constexpr TimeInterval<uint32_t> interval3(101, 200);
        constexpr auto empty_intersection = interval1.Intersection(interval3);

        EXPECT_FALSE(empty_intersection.has_value());
    }

    TEST(TimeIntervalTest, ShiftByIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval(5, 10);
        constexpr auto shifted_interval = interval.ShiftBy(3);

        EXPECT_EQ(shifted_interval.GetStart(), 8);
        EXPECT_EQ(shifted_interval.GetEnd(), 13);
    }

    TEST(TimeIntervalTest, ClampIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval(5, 10);
        constexpr TimeInterval<uint32_t> boundary(7, 12);
        constexpr auto clamped_interval = interval.Clamp(boundary);

        ASSERT_TRUE(clamped_interval.has_value());
        EXPECT_EQ(clamped_interval->GetStart(), 7);
        EXPECT_EQ(clamped_interval->GetEnd(), 10);

        constexpr TimeInterval<uint32_t> no_overlap_boundary(11, 15);
        constexpr auto no_overlap_clamp = interval.Clamp(no_overlap_boundary);

        EXPECT_FALSE(no_overlap_clamp.has_value());

        constexpr TimeInterval<uint32_t> interval2(10, 20);
        constexpr TimeInterval<uint32_t> empty_boundary(15, 15);
        constexpr auto result = interval2.Clamp(empty_boundary);

        EXPECT_FALSE(result.has_value());
    }
}
