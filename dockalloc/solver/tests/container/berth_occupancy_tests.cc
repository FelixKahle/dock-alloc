// Copyright (c) 2025 Felix Kahle.
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to
// the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
// LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
// WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#include "gtest/gtest.h"
#include "dockalloc/solver/container/berth_occupancy.h"

namespace dockalloc::solver
{
    template <typename T>
    class BerthOccupancyTest : public ::testing::Test
    {
    public:
        using TimeType = typename std::tuple_element<0, T>::type;
        using PositionType = typename std::tuple_element<1, T>::type;
        using WordType = typename std::tuple_element<2, T>::type;
    };

    using TestTypes = ::testing::Types<
        std::tuple<uint32_t, uint32_t, uint32_t>,
        std::tuple<uint64_t, size_t, uint64_t>,
        std::tuple<uint16_t, uint16_t, uint8_t>
    >;

    TYPED_TEST_SUITE(BerthOccupancyTest, TestTypes);

    TYPED_TEST(BerthOccupancyTest, ConstructionInitialStateIsFree)
    {
        using TimeType = typename TestFixture::TimeType;
        using PositionType = typename TestFixture::PositionType;
        using WordType = typename TestFixture::WordType;

        constexpr size_t num_segments = 100;
        BerthOccupancy<TimeType, PositionType, WordType> bo(num_segments);

        EXPECT_EQ(bo.GetQuaySegmentCount(), num_segments);
        EXPECT_EQ(bo.GetTimeEventCount(), 1);

        const core::TimeInterval<TimeType> full_time = {0, 1000};
        const core::SegmentRange<PositionType> full_range = {0, 100};
        EXPECT_TRUE(bo.IsFree(full_time, full_range));
        EXPECT_FALSE(bo.IsOccupied(full_time, full_range));
    }

    TYPED_TEST(BerthOccupancyTest, BasicOccupyAndFreeCycle)
    {
        using TimeType = typename TestFixture::TimeType;
        using PositionType = typename TestFixture::PositionType;
        using WordType = typename TestFixture::WordType;

        BerthOccupancy<TimeType, PositionType, WordType> bo(100);
        const core::TimeInterval<TimeType> ti = {10, 20};
        const core::SegmentRange<PositionType> sr = {5, 15};

        ASSERT_TRUE(bo.IsFree(ti, sr));

        bo.Occupy(ti, sr);
        EXPECT_EQ(bo.GetTimeEventCount(), 3) << "Timeline should have entries for 0, start, and end times.";
        EXPECT_FALSE(bo.IsFree(ti, sr));
        EXPECT_TRUE(bo.IsOccupied(ti, sr));

        bo.Free(ti, sr);
        EXPECT_EQ(bo.GetTimeEventCount(), 1) << "Timeline should coalesce back to the initial state.";
        EXPECT_TRUE(bo.IsFree(ti, sr));
        EXPECT_FALSE(bo.IsOccupied(ti, sr));
    }

    TYPED_TEST(BerthOccupancyTest, CoalesceAdjacentOccupiedIntervals)
    {
        using TimeType = typename TestFixture::TimeType;
        using PositionType = typename TestFixture::PositionType;
        using WordType = typename TestFixture::WordType;

        BerthOccupancy<TimeType, PositionType, WordType> bo(100);
        const core::SegmentRange<PositionType> sr = {10, 20};
        const core::TimeInterval<TimeType> time1 = {10, 20};
        const core::TimeInterval<TimeType> time2 = {20, 30};

        bo.Occupy(time1, sr);
        ASSERT_EQ(bo.GetTimeEventCount(), 3); // Events at 0, 10, 20

        // Occupy the adjacent time slot with the same segments
        bo.Occupy(time2, sr);

        // The event at time 20 should be coalesced away, as the state doesn't change.
        EXPECT_EQ(bo.GetTimeEventCount(), 3); // Events should now be at 0, 10, 30

        // The entire block [10, 30) should be occupied
        const core::TimeInterval<TimeType> combined_time = {10, 30};
        EXPECT_TRUE(bo.IsOccupied(combined_time, sr));
    }

    /// @brief Verifies that freeing a part of a larger occupied block works correctly.
    TYPED_TEST(BerthOccupancyTest, StateChangePunchingAHole)
    {
        using TimeType = typename TestFixture::TimeType;
        using PositionType = typename TestFixture::PositionType;
        using WordType = typename TestFixture::WordType;

        BerthOccupancy<TimeType, PositionType, WordType> bo(100);
        const core::TimeInterval<TimeType> large_ti = {10, 100};
        const core::SegmentRange<PositionType> large_sr = {10, 50};

        // Occupy a large block
        bo.Occupy(large_ti, large_sr);
        ASSERT_TRUE(bo.IsOccupied(large_ti, large_sr));

        // Free a smaller block inside the larger one ("punch a hole")
        const core::TimeInterval<TimeType> hole_ti = {40, 60};
        const core::SegmentRange<PositionType> hole_sr = {20, 30};
        bo.Free(hole_ti, hole_sr);

        // Check that the hole is now free
        EXPECT_TRUE(bo.IsFree(hole_ti, hole_sr));

        // Check that the areas around the hole are still occupied
        EXPECT_TRUE(bo.IsOccupied({30, 40}, {20, 30})); // Time before hole
        EXPECT_TRUE(bo.IsOccupied({60, 70}, {20, 30})); // Time after hole
        EXPECT_TRUE(bo.IsOccupied({40, 60}, {10, 20})); // Segments before hole
        EXPECT_TRUE(bo.IsOccupied({40, 60}, {30, 40})); // Segments after hole
    }

    /// @brief Tests querying at the exact boundaries of state changes.
    TYPED_TEST(BerthOccupancyTest, QueryExactBoundaries)
    {
        using TimeType = typename TestFixture::TimeType;
        using PositionType = typename TestFixture::PositionType;
        using WordType = typename TestFixture::WordType;

        BerthOccupancy<TimeType, PositionType, WordType> bo(50);
        const core::TimeInterval<TimeType> ti = {10, 20};
        const core::SegmentRange<PositionType> sr = {5, 15};
        bo.Occupy(ti, sr);

        // Time is exclusive at the end, so time 20 should be free
        EXPECT_TRUE(bo.IsFree({20, 21}, sr));
        // Time is inclusive at the start, so time 10 should be occupied
        EXPECT_FALSE(bo.IsFree({10, 11}, sr));

        // Check just before the start time
        EXPECT_TRUE(bo.IsFree({9, 10}, sr));
    }

    /// @brief Tests that operations with empty time or segment intervals are handled correctly.
    TYPED_TEST(BerthOccupancyTest, EdgeCaseEmptyIntervals)
    {
        using TimeType = typename TestFixture::TimeType;
        using PositionType = typename TestFixture::PositionType;
        using WordType = typename TestFixture::WordType;

        BerthOccupancy<TimeType, PositionType, WordType> bo(100);

        // Empty time interval
        const core::TimeInterval<TimeType> empty_ti = {10, 10};
        // Empty segment range
        const core::SegmentRange<PositionType> empty_sr = {5, 5};

        const core::TimeInterval<TimeType> valid_ti = {10, 20};
        const core::SegmentRange<PositionType> valid_sr = {5, 15};

        // Occupy/Free with empty intervals should be no-ops
        bo.Occupy(empty_ti, valid_sr);
        EXPECT_EQ(bo.GetTimeEventCount(), 1);
        bo.Occupy(valid_ti, empty_sr);
        EXPECT_EQ(bo.GetTimeEventCount(), 1);

        // IsFree with empty intervals should always be true
        EXPECT_TRUE(bo.IsFree(empty_ti, valid_sr));
        EXPECT_TRUE(bo.IsFree(valid_ti, empty_sr));
    }

    /// @brief Tests behavior with segment ranges that are partially or fully out of bounds.
    TYPED_TEST(BerthOccupancyTest, EdgeCaseOutOfBoundsSegments)
    {
        using TimeType = typename TestFixture::TimeType;
        using PositionType = typename TestFixture::PositionType;
        using WordType = typename TestFixture::WordType;

        BerthOccupancy<TimeType, PositionType, WordType> bo(50);
        const core::TimeInterval<TimeType> ti = {10, 20};

        // Range is partially out of bounds, should be clamped
        const core::SegmentRange<PositionType> partial_out = {40, 60};
        bo.Occupy(ti, partial_out);

        // The valid part [40, 50) should be occupied
        EXPECT_TRUE(bo.IsOccupied(ti, {40, 50}));
        // A query for the out-of-bounds part [50, 60) should be trivially free
        EXPECT_TRUE(bo.IsFree(ti, {50, 60}));

        // Reset state
        bo.Free(ti, partial_out);
        ASSERT_TRUE(bo.IsFree(ti, {0, 50}));

        // Range is fully out of bounds
        const core::SegmentRange<PositionType> full_out = {50, 100};
        bo.Occupy(ti, full_out);
        EXPECT_TRUE(bo.IsFree(ti, {0, 50})) << "Occupying a fully OOB range should do nothing.";
        EXPECT_EQ(bo.GetTimeEventCount(), 1);
    }

    /// @brief Tests behavior when the container is configured with zero segments.
    TYPED_TEST(BerthOccupancyTest, EdgeCaseZeroSegments)
    {
        using TimeType = typename TestFixture::TimeType;
        using PositionType = typename TestFixture::PositionType;
        using WordType = typename TestFixture::WordType;

        BerthOccupancy<TimeType, PositionType, WordType> bo(0);
        EXPECT_EQ(bo.GetQuaySegmentCount(), 0);
        EXPECT_EQ(bo.GetTimeEventCount(), 1);

        const core::TimeInterval<TimeType> ti = {10, 20};
        const core::SegmentRange<PositionType> sr = {0, 10};

        // Any operation should be a no-op on the state
        bo.Occupy(ti, sr);
        EXPECT_EQ(bo.GetTimeEventCount(), 1);
        EXPECT_TRUE(bo.IsFree(ti, sr));
    }
}
