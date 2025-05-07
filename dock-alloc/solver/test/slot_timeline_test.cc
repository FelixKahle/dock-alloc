// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/slot_timeline.h"

namespace dockalloc::solver
{
    TEST(SlotTimelineTest, ConstructorAllOccupied)
    {
        const SlotTimeline<uint32_t> timeline(100, true);
        EXPECT_TRUE(timeline.IsOccupied(0, 100));
    }

    TEST(SlotTimelineTest, SlotCountReturnsCorrectValue)
    {
        const SlotTimeline<uint32_t> timeline(100);
        EXPECT_EQ(timeline.SlotCount(), 100);
    }

    TEST(SlotTimelineTest, SetAllOccupied)
    {
        SlotTimeline<uint32_t> timeline(100, false);
        timeline.SetAllOccupied();
        EXPECT_TRUE(timeline.IsOccupied(0, 100));
    }

    TEST(SlotTimelineTest, SetAllFree)
    {
        SlotTimeline<uint32_t> timeline(100, true);
        timeline.SetAllFree();
        EXPECT_TRUE(timeline.IsFree(0, 100));
    }

    TEST(SlotTimelineTest, SingleSlotOccupied)
    {
        SlotTimeline<uint32_t> timeline(100, false);
        timeline.OccupySlot(50);
        EXPECT_TRUE(timeline.IsOccupied(50));
        EXPECT_FALSE(timeline.IsOccupied(0));
        EXPECT_FALSE(timeline.IsOccupied(99));
    }

    TEST(SlotTimelineTest, SingleSlotOccupiedOutside)
    {
        SlotTimeline<uint32_t> timeline_free(100, false);
        timeline_free.OccupySlot(120, false);
        EXPECT_TRUE(timeline_free.IsOccupied(120));
        EXPECT_FALSE(timeline_free.IsOccupied(0));
        EXPECT_FALSE(timeline_free.IsOccupied(119));

        SlotTimeline<uint32_t> timeline_occupied(100, false);
        timeline_occupied.OccupySlot(120, true);
        EXPECT_TRUE(timeline_occupied.IsOccupied(120));
        EXPECT_FALSE(timeline_occupied.IsOccupied(0));
        EXPECT_TRUE(timeline_occupied.IsOccupied(119));
    }

    TEST(SlotTimelineTest, SingleSlotFree)
    {
        SlotTimeline<uint32_t> timeline(100, true);
        timeline.FreeSlot(50);
        EXPECT_FALSE(timeline.IsOccupied(50));
        EXPECT_TRUE(timeline.IsOccupied(0));
        EXPECT_TRUE(timeline.IsOccupied(99));
    }

    TEST(SlotTimelineTest, SingleSlotOccupiedBasic)
    {
        const SlotTimeline<uint32_t> all_occ(100, true);
        EXPECT_TRUE(all_occ.IsOccupied(0));
        EXPECT_TRUE(all_occ.IsOccupied(99));
        EXPECT_FALSE(all_occ.IsOccupied(100));

        const SlotTimeline<uint32_t> all_free(100, false);
        EXPECT_FALSE(all_free.IsOccupied(0));
        EXPECT_FALSE(all_free.IsOccupied(99));
        EXPECT_FALSE(all_free.IsOccupied(100));
    }

    TEST(SlotTimelineTest, SingleSlotFreeBasic)
    {
        const SlotTimeline<uint32_t> all_free(100, false);
        EXPECT_TRUE(all_free.IsFree(0));
        EXPECT_TRUE(all_free.IsFree(99));
        EXPECT_TRUE(all_free.IsFree(100));

        const SlotTimeline<uint32_t> all_occ(100, true);
        EXPECT_FALSE(all_occ.IsFree(0));
        EXPECT_FALSE(all_occ.IsFree(99));
        EXPECT_TRUE(all_occ.IsFree(100));
    }

    TEST(SlotTimelineTest, RangeOccupiedNormal)
    {
        const SlotTimeline<uint32_t> occ(100, true);
        EXPECT_FALSE(occ.IsOccupied(0, 0));
        EXPECT_TRUE(occ.IsOccupied(0, 100));
        EXPECT_TRUE(occ.IsOccupied(10, 20));
    }

    TEST(SlotTimelineTest, RangeOccupiedEdge)
    {
        const SlotTimeline<uint32_t> occ(100, true);
        EXPECT_FALSE(occ.IsOccupied(0, 101));
        EXPECT_FALSE(occ.IsOccupied(99, 2));
        EXPECT_FALSE(occ.IsOccupied(100, 1));
        EXPECT_FALSE(occ.IsOccupied(50, 51));
    }

    TEST(SlotTimelineTest, RangeFreeNormal)
    {
        const SlotTimeline<uint32_t> free(100, false);
        EXPECT_TRUE(free.IsFree(0, 0));
        EXPECT_TRUE(free.IsFree(0, 100));
        EXPECT_TRUE(free.IsFree(10, 20));
    }

    TEST(SlotTimelineTest, RangeFreeEdge)
    {
        const SlotTimeline<uint32_t> free(100, false);
        EXPECT_TRUE(free.IsFree(90, 30));
        EXPECT_TRUE(free.IsFree(100, 1));
    }

    TEST(SlotTimelineTest, OverflowIsOccupied)
    {
        const SlotTimeline<uint32_t> tl(100, false);
        constexpr size_t huge = std::numeric_limits<size_t>::max();
        EXPECT_FALSE(tl.IsOccupied(0, huge));
        EXPECT_FALSE(tl.IsOccupied(huge, 1));
    }

    TEST(SlotTimelineTest, OverflowIsFree)
    {
        const SlotTimeline<uint32_t> tl(100, false);
        constexpr size_t huge = std::numeric_limits<size_t>::max();
        EXPECT_TRUE(tl.IsFree(0, huge));
        EXPECT_TRUE(tl.IsFree(huge, 1));
    }

    TEST(SlotTimelineTest, OccupyRange)
    {
        SlotTimeline<uint32_t> t(100, false);
        t.OccupySlotRange(2, 50);
        EXPECT_TRUE(t.IsOccupied(2, 50));
    }

    TEST(SlotTimelineTest, FreeRange)
    {
        SlotTimeline<uint32_t> t(100, true);
        t.FreeSlotRange(2, 50);
        EXPECT_TRUE(t.IsFree(2, 50));
    }
}
