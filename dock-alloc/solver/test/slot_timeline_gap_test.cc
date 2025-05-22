// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/slot_timeline_gap.h"

namespace dockalloc::solver
{
    TEST(SlotTimelineGapTest, ConstructsCorrectly)
    {
        constexpr SlotTimelineGap first_gap(5, std::nullopt);
        EXPECT_EQ(first_gap.GetStart(), 5);
        EXPECT_FALSE(first_gap.IsEmpty());
        EXPECT_FALSE(first_gap.GetEnd().has_value());

        constexpr SlotTimelineGap second_gap(5, 10);
        EXPECT_EQ(second_gap.GetStart(), 5);
        EXPECT_FALSE(second_gap.IsEmpty());
        EXPECT_EQ(*second_gap.GetEnd(), 10);
    }

    TEST(SlotTimelineGapTest, ConstructorSwapsStartEnd)
    {
        constexpr SlotTimelineGap gap(5, 2);
        EXPECT_EQ(gap.GetStart(), 2);
        EXPECT_EQ(gap.GetEnd().value(), 5);
    }

    TEST(SlotTimelineGapTest, IsEmptyReturnsTrueEmptyRange)
    {
        constexpr SlotTimelineGap gap(5, 5);
        EXPECT_TRUE(gap.IsEmpty());
    }

    TEST(SlotTimelineGapTest, IsEmptyReturnsFalseNonEmptyRange)
    {
        constexpr SlotTimelineGap first_gap(5, 10);
        EXPECT_FALSE(first_gap.IsEmpty());

        constexpr SlotTimelineGap second_gap(5, std::nullopt);
        EXPECT_FALSE(second_gap.IsEmpty());
    }

    TEST(SlotTimelineGapTest, EqualityOperatorWorks)
    {
        constexpr SlotTimelineGap gap1(5, 10);
        constexpr SlotTimelineGap gap2(5, 10);
        constexpr SlotTimelineGap gap3(5, 11);
        constexpr SlotTimelineGap gap4(5, std::nullopt);

        EXPECT_TRUE(gap1 == gap2);
        EXPECT_FALSE(gap1 == gap3);
        EXPECT_FALSE(gap1 == gap4);
    }

    TEST(SlotTimelineGapTest, InequalityOperatorWorks)
    {
        constexpr SlotTimelineGap gap1(5, 10);
        constexpr SlotTimelineGap gap2(5, 10);
        constexpr SlotTimelineGap gap3(5, 11);
        constexpr SlotTimelineGap gap4(5, std::nullopt);

        EXPECT_FALSE(gap1 != gap2);
        EXPECT_TRUE(gap1 != gap3);
        EXPECT_TRUE(gap1 != gap4);
    }
}
