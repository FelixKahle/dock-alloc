// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/disjoint_berth_schedule.h"

namespace dockalloc::solver
{
    TEST(DisjointBerthScheduleTest, InitializesCorrectly)
    {
        const DisjointBerthSchedule<uint32_t> schedule;
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(6, 10)));
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(10000, 20000)));
    }

    TEST(DisjointBerthScheduleTest, OccupyCorrectly)
    {
        DisjointBerthSchedule<uint32_t> schedule;
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));
        EXPECT_TRUE(schedule.Occupy(TimeInterval<uint32_t>(1, 5)));
        EXPECT_FALSE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));

        EXPECT_FALSE(schedule.Occupy(TimeInterval<uint32_t>(1, 5)));
        EXPECT_FALSE(schedule.Occupy(TimeInterval<uint32_t>(4, 10)));
        EXPECT_FALSE(schedule.Occupy(TimeInterval<uint32_t>(5, 10)));
        EXPECT_FALSE(schedule.Occupy(TimeInterval<uint32_t>(0, 3)));
        EXPECT_FALSE(schedule.Occupy(TimeInterval<uint32_t>(0, 1)));
    }

    TEST(DisjointBerthScheduleTest, FreeCorrectly)
    {
        DisjointBerthSchedule<uint32_t> schedule;
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));
        EXPECT_TRUE(schedule.Occupy(TimeInterval<uint32_t>(1, 5)));
        EXPECT_FALSE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));
        schedule.Free(TimeInterval<uint32_t>(1, 5));
        EXPECT_TRUE(schedule.IsFree(TimeInterval<uint32_t>(1, 5)));
    }
}
