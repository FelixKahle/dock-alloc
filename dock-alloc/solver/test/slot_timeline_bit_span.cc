// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/slot_timeline_bit_span.h"

namespace dockalloc::solver
{
    TEST(SlotTimelineBitSpanTest, ConstructorFromVector)
    {
        std::vector<uint32_t> bitmap(10, 0);
        const SlotTimelineBitSpan<uint32_t> bit_span(bitmap);

        EXPECT_EQ(bit_span.GetData(), bitmap.data());
        EXPECT_EQ(bit_span.GetWordCount(), bitmap.size());
    }

    TEST(SlotTimelineBitSpanTest, ConstructorFromPointer)
    {
        std::array<uint32_t, 4> data = {0, 1, 2, 3};
        SlotTimelineBitSpan<uint32_t> span(data.data(), data.size());
        EXPECT_EQ(span.GetData(), data.data());
        EXPECT_EQ(span.GetWordCount(), data.size());
    }

    TEST(SlotTimelineBitSpanTest, SetGetClearBitSingleBit)
    {
        std::vector<uint32_t> data(2, 0);
        SlotTimelineBitSpan<uint32_t> span(data);

        span.SetBit(0);
        EXPECT_TRUE(span.IsBitSet(0));
        EXPECT_FALSE(span.IsBitCleared(0));
        EXPECT_EQ(data[0], 1u);

        span.SetBit(31);
        EXPECT_TRUE(span.GetBit(31));

        span.ClearBit(31);
        EXPECT_TRUE(span.IsBitCleared(31));

        span.ToggleBit(15);
        EXPECT_TRUE(span.IsBitSet(15));
        span.ToggleBit(15);
        EXPECT_TRUE(span.IsBitCleared(15));
    }

    TEST(SlotTimelineBitSpanTest, SetAllClearAll)
    {
        std::vector<uint32_t> data(3, 0xAAAAAAAA);
        SlotTimelineBitSpan<uint32_t> span(data);
        span.SetAll();
        for (size_t i = 0; i < data.size() * 32; ++i)
        {
            EXPECT_TRUE(span[i]);
        }
        span.ClearAll();
        for (size_t i = 0; i < data.size() * 32; ++i)
        {
            EXPECT_FALSE(span.GetBit(i));
        }
    }

    TEST(SlotTimelineBitSpanTest, SetBitRangeSingleWord)
    {
        std::vector<uint32_t> data(1, 0);
        SlotTimelineBitSpan<uint32_t> span(data);

        span.SetBitRange(TimeSlotRange(5, 10));
        for (size_t i = 0; i < 32; ++i)
        {
            if (i >= 5 && i < 10)
                EXPECT_TRUE(span.IsBitSet(i));
            else
                EXPECT_FALSE(span.IsBitSet(i));
        }
    }

    TEST(SlotTimelineBitSpanTest, SetBitRangeMultiWord)
    {
        std::vector<uint32_t> data(2, 0);
        SlotTimelineBitSpan<uint32_t> span(data);

        span.SetBitRange(TimeSlotRange(28, 36));
        for (size_t i = 0; i < 64; ++i)
        {
            bool expected = (i >= 28 && i < 36);
            EXPECT_EQ(span.IsBitSet(i), expected) << "i=" << i;
        }
    }

    TEST(SlotTimelineBitSpanTest, ClearBitRangeCrossWord)
    {
        std::vector<uint32_t> data(3, 0xFFFFFFFF);
        SlotTimelineBitSpan<uint32_t> span(data);

        span.ClearBitRange(TimeSlotRange(20, 84));
        for (size_t i = 0; i < 96; ++i)
        {
            bool expected = !(i >= 20 && i < 84);
            EXPECT_EQ(span.GetBit(i), expected) << "bit " << i;
        }
    }

    TEST(SlotTimelineBitSpanTest, IsBitRangeSetClearMixed)
    {
        std::vector<uint32_t> data(2, 0);
        SlotTimelineBitSpan<uint32_t> span(data);

        span.SetAll();
        EXPECT_TRUE(span.IsBitRangeSet(TimeSlotRange(0, 64)));
        EXPECT_FALSE(span.IsBitRangeClear(TimeSlotRange(0, 64)));

        span.ClearBitRange(TimeSlotRange(10, 54));
        EXPECT_FALSE(span.IsBitRangeSet(TimeSlotRange(0, 64)));
        EXPECT_TRUE(span.IsBitRangeClear(TimeSlotRange(10, 54)));
        EXPECT_TRUE(span.IsBitRangeSet(TimeSlotRange(0, 10)));
        EXPECT_TRUE(span.IsBitRangeSet(TimeSlotRange(54, 64)));
    }

    TEST(SlotTimelineBitSpanTest, OperatorIndexReadOnly)
    {
        std::vector<uint32_t> data(1, 0);
        SlotTimelineBitSpan<uint32_t> span(data);
        span.SetBit(3);
        EXPECT_TRUE(span[3]);
        EXPECT_FALSE(span[2]);
    }
}
