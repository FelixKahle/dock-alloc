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

    TEST(TimeSlotRangeTest, LengthIsCorrect)
    {
        constexpr TimeSlotRange first_range(5, 10);
        EXPECT_EQ(first_range.Length(), 5);

        constexpr TimeSlotRange second_range(10, 10);
        EXPECT_EQ(second_range.Length(), 0);

        constexpr TimeSlotRange third_range(0, 1);
        EXPECT_EQ(third_range.Length(), 1);
    }

    TEST(TimeSlotRangeTest, IsEmptyIsCorrect)
    {
        constexpr TimeSlotRange first_range(5, 10);
        EXPECT_FALSE(first_range.IsEmpty());

        constexpr TimeSlotRange second_range(10, 10);
        EXPECT_TRUE(second_range.IsEmpty());

        constexpr TimeSlotRange third_range(0, 1);
        EXPECT_FALSE(third_range.IsEmpty());
    }

    TEST(TimeSlotRangeTest, EqualityOperator)
    {
        constexpr TimeSlotRange first_range(5, 10);
        constexpr TimeSlotRange second_range(5, 10);
        EXPECT_TRUE(first_range == second_range);

        constexpr TimeSlotRange third_range(5, 11);
        EXPECT_FALSE(first_range == third_range);
    }

    TEST(TimeSlotRangeTest, InequalityOperator)
    {
        constexpr TimeSlotRange first_range(5, 10);
        constexpr TimeSlotRange second_range(5, 10);
        EXPECT_FALSE(first_range != second_range);

        constexpr TimeSlotRange third_range(5, 11);
        EXPECT_TRUE(first_range != third_range);
    }
}
