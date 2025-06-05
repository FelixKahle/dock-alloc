// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/core/time/time_interval.h"

namespace dockalloc::core::test
{
    static_assert(sizeof(TimeInterval<uint32_t>) == 2 * sizeof(uint32_t),
                  "TimeInterval should have two uint32_t members");

    TEST(TimeIntervalTest, ConstructsCorrectly)
    {
        constexpr TimeInterval<uint32_t> interval(5, 10);
        EXPECT_EQ(interval.GetStart(), 5);
        EXPECT_EQ(interval.GetEnd(), 10);
    }

    TEST(TimeIntervalTest, ConstructorSwapsStartEnd)
    {
        constexpr TimeInterval<uint32_t> interval(10, 5);
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

    TEST(TimeIntervalTest, IsEmptyReturnsTrueForZeroLength)
    {
        constexpr TimeInterval<uint32_t> interval(5, 5);
        EXPECT_TRUE(interval.IsEmpty());
    }

    TEST(TimeIntervalTest, IsEmptyReturnsFalseForNonZeroLength)
    {
        constexpr TimeInterval<uint32_t> interval(5, 10);
        EXPECT_FALSE(interval.IsEmpty());
    }

    TEST(TimeIntervalTest, DurationIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval(5, 10);
        EXPECT_EQ(interval.Duration(), 5);
    }

    TEST(TimeIntervalTest, ContainsReturnsTrueForContainedValues)
    {
        constexpr TimeInterval<uint32_t> interval(2, 100);
        for (uint32_t i = 2; i < 100; ++i)
        {
            EXPECT_TRUE(interval.Contains(i));
        }
    }

    TEST(TimeIntervalTest, ContainsReturnsFalseForOutsideValues)
    {
        constexpr TimeInterval<uint32_t> interval(2, 100);
        EXPECT_FALSE(interval.Contains(1));
        EXPECT_FALSE(interval.Contains(100));
        EXPECT_FALSE(interval.Contains(101));
    }

    TEST(TimeIntervalTest, ContainsIntervalIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval1(2, 100);
        constexpr TimeInterval<uint32_t> interval2(5, 10);
        constexpr TimeInterval<uint32_t> interval3(5, 105);

        EXPECT_TRUE(interval1.ContainsInterval(interval2));
        EXPECT_FALSE(interval2.ContainsInterval(interval1));
        EXPECT_FALSE(interval1.ContainsInterval(interval3));
    }

    TEST(TimeIntervalTest, IntersectsIsCorrect)
    {
        constexpr TimeInterval<uint32_t> interval1(2, 100);
        constexpr TimeInterval<uint32_t> interval2(5, 10);
        constexpr TimeInterval<uint32_t> interval3(101, 200);

        EXPECT_TRUE(interval1.Intersects(interval2));
        EXPECT_FALSE(interval1.Intersects(interval3));
    }

    TEST(TimeIntervalTest, IntersectionReturnsValidRangeIfOverlapExists)
    {
        constexpr TimeInterval<uint32_t> interval1(2, 100);
        constexpr TimeInterval<uint32_t> interval2(5, 10);
        constexpr auto intersection = interval1.Intersection(interval2);

        ASSERT_TRUE(intersection.has_value());
        EXPECT_EQ(intersection->GetStart(), 5);
        EXPECT_EQ(intersection->GetEnd(), 10);
    }

    TEST(TimeInterval, IntersectionReturnsEmptyIfNoOverlap)
    {
        constexpr TimeInterval<uint32_t> interval1(2, 100);
        constexpr TimeInterval<uint32_t> interval3(101, 200);
        constexpr auto intersection = interval1.Intersection(interval3);

        EXPECT_FALSE(intersection.has_value());
    }

    TEST(TimeIntervalTest, ClampReturnsCorrectClampedInterval)
    {
        constexpr TimeInterval<uint32_t> interval(5, 10);
        constexpr TimeInterval<uint32_t> boundary(7, 12);
        constexpr auto clamped_interval = interval.Clamp(boundary);

        ASSERT_TRUE(clamped_interval.has_value());
        EXPECT_EQ(clamped_interval->GetStart(), 7);
        EXPECT_EQ(clamped_interval->GetEnd(), 10);
    }

    TEST(TimeIntervalTest, ClampReturnsEmptyIfNoOverlap)
    {
        constexpr TimeInterval<uint32_t> interval(5, 10);
        constexpr TimeInterval<uint32_t> boundary(11, 15);
        constexpr auto clamped = interval.Clamp(boundary);

        EXPECT_FALSE(clamped.has_value());
    }

    TEST(TimeIntervalTest, ClampReturnsEmptyIfBoundaryIsEmpty)
    {
        constexpr TimeInterval<uint32_t> interval(10, 20);
        constexpr TimeInterval<uint32_t> empty_boundary(15, 15);
        constexpr auto clamped = interval.Clamp(empty_boundary);

        EXPECT_FALSE(clamped.has_value());
    }

    TEST(TimeIntervalTest, EqualityOperatorWorks)
    {
        constexpr TimeInterval<uint32_t> interval1(5, 10);
        constexpr TimeInterval<uint32_t> interval2(5, 10);
        constexpr TimeInterval<uint32_t> interval3(5, 15);

        EXPECT_TRUE(interval1 == interval2);
        EXPECT_FALSE(interval1 == interval3);
        EXPECT_FALSE(interval1 != interval2);
        EXPECT_TRUE(interval1 != interval3);
    }

    TEST(TimeIntervalTest, InequalityOperatorWorks)
    {
        constexpr TimeInterval<uint32_t> interval1(5, 10);
        constexpr TimeInterval<uint32_t> interval2(5, 10);
        constexpr TimeInterval<uint32_t> interval3(5, 15);

        EXPECT_FALSE(interval1 != interval2);
        EXPECT_TRUE(interval1 != interval3);
        EXPECT_TRUE(interval1 == interval2);
        EXPECT_FALSE(interval1 == interval3);
    }

    TEST(TimeIntervalTest, EqualityOperatorWorksAcrossDifferentTypes)
    {
        constexpr TimeInterval<uint32_t> interval(5, 10);
        constexpr TimeInterval<uint64_t> same_interval(5, 10);

        EXPECT_TRUE(interval == same_interval);
        EXPECT_FALSE(interval != same_interval);
    }
}
