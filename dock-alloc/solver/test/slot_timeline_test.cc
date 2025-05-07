// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/slot_timeline.h"

namespace dockalloc::solver
{
    TEST(SlotTimelineTest, ConstructorSetsCorrectDepth)
    {
        const SlotTimeline<4, uint16_t> timeline(100, true);
        EXPECT_EQ(timeline.kDepth, 4);
    }

    TEST(SlotTimelineTest, ConstructorSetsCorrectSlotCount)
    {
        const SlotTimeline<4, uint16_t> timeline(100, true);
        EXPECT_EQ(timeline.SlotCount(), 100);
    }

    TEST(SlotTimelineTest, ConstructorSetsOccupiedSlots)
    {
        const SlotTimeline<4, uint16_t> timeline(100, true);
        for (size_t i = 0; i < 100; ++i)
        {
            EXPECT_TRUE(timeline.IsOccupied(i));
        }
    }

    TEST(SlotTimelineTest, ConstructorSetsFreeSlots)
    {
        const SlotTimeline<4, uint16_t> timeline(100, false);
        for (size_t i = 0; i < 100; ++i)
        {
            EXPECT_TRUE(timeline.IsFree(i));
        }
    }
}
