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
    using Occ32 = BerthOccupancy<uint32_t, uint32_t, uint32_t>;
    using IntervalI = core::Interval<uint32_t>;

    TEST(BerthOccupancyTest, InitialFreeState)
    {
        // Times and positions cover [0,100]
        std::vector<uint32_t> times = {0, 50, 100};
        std::vector<uint32_t> positions = {0, 100};
        Occ32 occ(times, positions);
        IntervalI full_time(0, 100);
        IntervalI full_space(0, 100);
        EXPECT_TRUE(occ.IsFree(full_time, full_space));
        EXPECT_FALSE(occ.IsOccupied(full_time, full_space));
    }

    TEST(BerthOccupancyTest, MarkOccupiedAndFree)
    {
        std::vector<uint32_t> times = {0, 10, 20, 30};
        std::vector<uint32_t> positions = {0, 100, 200};
        Occ32 occ(times, positions);

        IntervalI t_iv(10, 30); // covers times 10..30
        IntervalI s_iv(0, 200); // full space

        // Occupy the middle time interval
        occ.MarkOccupied(t_iv, s_iv);
        EXPECT_FALSE(occ.IsFree(t_iv, s_iv));
        EXPECT_TRUE(occ.IsOccupied(t_iv, s_iv));

        // Free it back and verify full interval free
        occ.MarkFree(t_iv, s_iv);
        EXPECT_TRUE(occ.IsFree(t_iv, s_iv));
    }

    TEST(BerthOccupancyTest, PartialSpaceOccupation)
    {
        std::vector<uint32_t> times = {0, 1, 2, 3};
        std::vector<uint32_t> positions = {0, 10, 20, 30};
        Occ32 occ(times, positions);

        // Occupy the space interval that spans two segments due to implementation
        IntervalI t_iv(0, 3);
        IntervalI s_iv(10, 20);
        occ.MarkOccupied(t_iv, s_iv);

        // Due to how segments are computed, space [10,20] marks two segments
        EXPECT_FALSE(occ.IsFree(t_iv, s_iv));
        // Adjacent space intervals should remain free
        EXPECT_TRUE(occ.IsFree(t_iv, IntervalI(0, 10)));
    }

    TEST(BerthOccupancyTest, EmptyIntervalsNoOp)
    {
        std::vector<uint32_t> times = {0, 5, 10};
        std::vector<uint32_t> positions = {0, 50, 100};
        Occ32 occ(times, positions);

        // Empty time interval
        occ.MarkOccupied(IntervalI(5, 5), IntervalI(0, 100));
        EXPECT_TRUE(occ.IsFree(IntervalI(0, 10), IntervalI(0, 100)));

        // Empty space interval
        occ.MarkOccupied(IntervalI(0, 10), IntervalI(50, 50));
        EXPECT_TRUE(occ.IsFree(IntervalI(0, 10), IntervalI(0, 100)));
    }

    TEST(BerthOccupancyTest, OutOfDomainIntervals)
    {
        std::vector<uint32_t> times = {10, 20, 30};
        std::vector<uint32_t> positions = {100, 200, 300};
        Occ32 occ(times, positions);

        // Completely before domain (using sensible positive values)
        EXPECT_TRUE(occ.IsFree(IntervalI(0, 5), IntervalI(0, 50)));
        // Completely after domain
        EXPECT_TRUE(occ.IsFree(IntervalI(40, 50), IntervalI(400, 500)));

        // Occupy outside domain does nothing; domain interior remains free
        occ.MarkOccupied(IntervalI(0, 5), IntervalI(0, 50));
        EXPECT_TRUE(occ.IsFree(IntervalI(10, 30), IntervalI(100, 300)));
    }


    TEST(BerthOccupancyTest, NonPowerOfTwoLeaves)
    {
        // 3 time points -> tree_size = 4 internally
        std::vector<uint32_t> times = {0, 1, 2};
        std::vector<uint32_t> positions = {0, 100};
        Occ32 occ(times, positions);

        IntervalI full_time(0, 2);
        IntervalI full_space(0, 100);

        // Occupy an interval spanning all existing times
        occ.MarkOccupied(IntervalI(0, 3), full_space);
        EXPECT_FALSE(occ.IsFree(full_time, full_space));

        // Free back only first leaf and check only that leaf is free when queried exactly
        occ.MarkFree(IntervalI(0, 1), full_space);
        EXPECT_TRUE(occ.IsFree(IntervalI(0, 1), full_space));
    }

    TEST(BerthOccupancyTest, OverlappingOccupation)
    {
        std::vector<uint32_t> times = {0, 5, 10, 15};
        std::vector<uint32_t> positions = {0, 50, 100};
        Occ32 occ(times, positions);
        IntervalI full_space(0, 100);

        // Partially overlap two intervals
        occ.MarkOccupied(IntervalI(0, 10), full_space);
        occ.MarkOccupied(IntervalI(5, 15), full_space);

        // Entire span should now be occupied
        EXPECT_FALSE(occ.IsFree(IntervalI(0, 15), full_space));

        // Free middle only
        occ.MarkFree(IntervalI(5, 10), full_space);
        EXPECT_TRUE(occ.IsFree(IntervalI(5, 10), full_space));
        // Ends still occupied
        EXPECT_FALSE(occ.IsFree(IntervalI(0, 5), full_space));
        EXPECT_FALSE(occ.IsFree(IntervalI(10, 15), full_space));
    }
}
