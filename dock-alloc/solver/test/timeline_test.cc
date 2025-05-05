// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/timeline.h"

namespace dockalloc::solver
{
    TEST(BitPackedTimelineTest, TimeToSlotAndBack)
    {
        const BitPackedTimeline<uint32_t, uint64_t> timeline(1000, 10);
        EXPECT_EQ(timeline.TimeToSlot(0), 0);
        EXPECT_EQ(timeline.TimeToSlot(50), 5);
        EXPECT_EQ(timeline.SlotToTime(5), 50);
    }

    TEST(BitPackedTimelineTest, IsFree)
    {
        BitPackedTimeline<uint32_t, uint64_t> timeline(1000);
        EXPECT_TRUE(timeline.IsFree(0, 5));
        EXPECT_TRUE(timeline.IsFree(5, 5));

        timeline.Reserve(0, 5);
        EXPECT_FALSE(timeline.IsFree(0, 5));
        EXPECT_TRUE(timeline.IsFree(5, 5));
    }

    TEST(BitPackedTimelineTest, TotalSlots)
    {
        const BitPackedTimeline<uint32_t, uint64_t> timeline(1000);
        EXPECT_EQ(timeline.TotalSlots(), 1000);
    }
}
