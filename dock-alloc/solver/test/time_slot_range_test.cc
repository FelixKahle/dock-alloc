// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/time_slot_range.h"

// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/time_slot_range.h"

namespace dockalloc::solver
{
    TEST(TimeSlotRangeTest, ConstructsCorrectly)
    {
        constexpr TimeSlotRange range(5, 10);
        EXPECT_EQ(range.GetStart(), 5);
        EXPECT_EQ(range.GetEnd(), 10);
    }

    TEST(TimeSlotRangeTest, LengthReturnsCorrectValues)
    {
        constexpr TimeSlotRange range1(5, 10);
        EXPECT_EQ(range1.Length(), 5);

        constexpr TimeSlotRange range2(10, 10);
        EXPECT_EQ(range2.Length(), 0);

        constexpr TimeSlotRange range3(0, 1);
        EXPECT_EQ(range3.Length(), 1);
    }

    TEST(TimeSlotRangeTest, IsEmptyReturnsTrueForZeroLength)
    {
        constexpr TimeSlotRange range(10, 10);
        EXPECT_TRUE(range.IsEmpty());
    }

    TEST(TimeSlotRangeTest, IsEmptyReturnsFalseForNonZeroLength)
    {
        constexpr TimeSlotRange range1(5, 10);
        constexpr TimeSlotRange range2(0, 1);

        EXPECT_FALSE(range1.IsEmpty());
        EXPECT_FALSE(range2.IsEmpty());
    }

    TEST(TimeSlotRangeTest, FromLengthCreatesCorrectRange)
    {
        constexpr TimeSlotRange range = TimeSlotRange::FromLength(5, 3);
        EXPECT_EQ(range.GetStart(), 5);
        EXPECT_EQ(range.GetEnd(), 8);
    }

    TEST(TimeSlotRangeTest, FromLengthWithZeroLengthCreatesEmptyRange)
    {
        constexpr TimeSlotRange range = TimeSlotRange::FromLength(5, 0);
        EXPECT_EQ(range.GetStart(), 5);
        EXPECT_EQ(range.GetEnd(), 5);
        EXPECT_TRUE(range.IsEmpty());
    }

    TEST(TimeSlotRangeTest, EqualityOperatorWorks)
    {
        constexpr TimeSlotRange range1(5, 10);
        constexpr TimeSlotRange range2(5, 10);
        constexpr TimeSlotRange range3(5, 11);

        EXPECT_TRUE(range1 == range2);
        EXPECT_FALSE(range1 == range3);
    }

    TEST(TimeSlotRangeTest, InequalityOperatorWorks)
    {
        constexpr TimeSlotRange range1(5, 10);
        constexpr TimeSlotRange range2(5, 10);
        constexpr TimeSlotRange range3(5, 11);

        EXPECT_FALSE(range1 != range2);
        EXPECT_TRUE(range1 != range3);
    }
}
