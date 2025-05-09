// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/disjoint_berth_time_schedule.h"

namespace dockalloc::solver
{
    TEST(DisjointBerthTimeScheduleTest, InitializesCorrectly)
    {
        const DisjointBerthTimeSchedule<uint32_t> schedule;
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(6, 10)));
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(10000, 20000)));
    }

    TEST(DisjointBerthTimeScheduleTest, OccupyCorrectly)
    {
        DisjointBerthTimeSchedule<uint32_t> schedule;
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));
        EXPECT_TRUE(schedule.Occupy(TimeInterval<uint32_t>(1, 5)));
        EXPECT_FALSE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));

        EXPECT_FALSE(schedule.Occupy(TimeInterval<uint32_t>(1, 5)));
        EXPECT_FALSE(schedule.Occupy(TimeInterval<uint32_t>(4, 10)));
        EXPECT_FALSE(schedule.Occupy(TimeInterval<uint32_t>(5, 10)));
        EXPECT_FALSE(schedule.Occupy(TimeInterval<uint32_t>(0, 3)));
        EXPECT_FALSE(schedule.Occupy(TimeInterval<uint32_t>(0, 1)));
    }

    TEST(DisjointBerthTimeScheduleTest, FreeCorrectly)
    {
        DisjointBerthTimeSchedule<uint32_t> schedule;
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));
        EXPECT_TRUE(schedule.Occupy(TimeInterval<uint32_t>(1, 5)));
        EXPECT_FALSE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));
        schedule.Free(TimeInterval<uint32_t>(1, 5));
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));
    }

    TEST(DisjointBerthTimeScheduleTest, FindGapCorrectly)
    {
        DisjointBerthTimeSchedule<uint32_t> schedule;
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));
        EXPECT_TRUE(schedule.Occupy(TimeInterval<uint32_t>(1, 5)));

        const auto gap1 = schedule.FindGap(2, 5);

        EXPECT_EQ(gap1.GetStart(), 6);
        EXPECT_EQ(gap1.GetEnd(), std::nullopt);

        EXPECT_TRUE(schedule.Occupy(TimeInterval<uint32_t>(15, 20)));

        const auto gap2 = schedule.FindGap(2, 5);

        EXPECT_EQ(gap2.GetStart(), 6);
        EXPECT_EQ(gap2.GetEnd(), 14);
    }
}
