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
#include "dockalloc/solver/container/quay_segment_tree.h"

namespace dockalloc::solver
{
    using TestTypes = ::testing::Types<uint32_t, uint64_t>;

    template <typename T>
    class SegmentTreeTest : public ::testing::Test
    {
    protected:
        using Position = T;
        const Position kSize = 16;
        SegmentTree<Position> tree{kSize};
    };

    TYPED_TEST_SUITE(SegmentTreeTest, TestTypes);

    TYPED_TEST(SegmentTreeTest, InitializesAllFree)
    {
        core::SegmentRange<typename TestFixture::Position> fullRange{0, this->kSize};
        EXPECT_TRUE(this->tree.IsRangeFree(fullRange));
        EXPECT_FALSE(this->tree.IsRangeOccupied(fullRange));
        // Find free of full length should return 0
        auto idx = this->tree.FindFree(this->kSize);
        ASSERT_TRUE(idx.has_value());
        EXPECT_EQ(idx.value(), 0);
    }

    // Test occupying a middle segment
    TYPED_TEST(SegmentTreeTest, OccupyMiddleSegment)
    {
        using Position = typename TestFixture::Position;
        Position start = 4, end = 10;
        core::SegmentRange<Position> mid{start, end};
        this->tree.Occupy(mid);

        // The occupied range should not be free
        EXPECT_FALSE(this->tree.IsRangeFree(mid));
        EXPECT_TRUE(this->tree.IsRangeOccupied(mid));

        // Segments before should remain free
        core::SegmentRange<Position> before{0, start};
        EXPECT_TRUE(this->tree.IsRangeFree(before));
        EXPECT_FALSE(this->tree.IsRangeOccupied(before));

        // Segments after should remain free
        core::SegmentRange<Position> after{end, this->kSize};
        EXPECT_TRUE(this->tree.IsRangeFree(after));
        EXPECT_FALSE(this->tree.IsRangeOccupied(after));

        // Find a block of size 3 should find at position 0
        auto idx3 = this->tree.FindFree(3);
        ASSERT_TRUE(idx3.has_value());
        EXPECT_EQ(idx3.value(), 0);

        // Find a block larger than any free continuous region should return none
        auto idxLarge = this->tree.FindFree((this->kSize - (end - start)) + 1);
        EXPECT_FALSE(idxLarge.has_value());
    }

    // Test freeing an occupied segment
    TYPED_TEST(SegmentTreeTest, FreeSegment)
    {
        using Position = typename TestFixture::Position;
        // Occupy all, then free a sub-range
        core::SegmentRange<Position> full{0, this->kSize};
        this->tree.Occupy(full);

        Position start = 5, end = 9;
        core::SegmentRange<Position> sub{start, end};
        this->tree.Free(sub);

        // Sub-range is free, rest occupied
        EXPECT_TRUE(this->tree.IsRangeFree(sub));
        EXPECT_FALSE(this->tree.IsRangeOccupied(sub));

        // Check before and after remain occupied
        core::SegmentRange<Position> before{0, start};
        EXPECT_TRUE(this->tree.IsRangeOccupied(before));
        core::SegmentRange<Position> after{end, this->kSize};
        EXPECT_TRUE(this->tree.IsRangeOccupied(after));

        // Find free of size (end-start)
        auto idx = this->tree.FindFree(end - start);
        ASSERT_TRUE(idx.has_value());
        EXPECT_EQ(idx.value(), start);
    }

    // Test edge cases: occupy at beginning and end
    TYPED_TEST(SegmentTreeTest, EdgeOccupy)
    {
        using Position = typename TestFixture::Position;
        // Occupy first k and last k positions
        Position k = 4;
        this->tree.Occupy({0, k});
        this->tree.Occupy({this->kSize - k, this->kSize});

        // Middle should remain free
        core::SegmentRange<Position> middle{k, this->kSize - k};
        EXPECT_TRUE(this->tree.IsRangeFree(middle));
        EXPECT_EQ(this->tree.FindFree(k), k);

        // Start and end should be occupied
        EXPECT_TRUE(this->tree.IsRangeOccupied({0, k}));
        EXPECT_TRUE(this->tree.IsRangeOccupied({this->kSize - k, this->kSize}));
    }

    // Test multiple updates and queries
    TYPED_TEST(SegmentTreeTest, MultipleUpdatesAndQueries)
    {
        // Occupy [2,5), [7,9)
        this->tree.Occupy({2, 5});
        this->tree.Occupy({7, 9});

        // Free [3,4)
        this->tree.Free({3, 4});

        // Check individual positions
        EXPECT_FALSE(this->tree.IsRangeFree({2,3}));
        EXPECT_TRUE(this->tree.IsRangeFree({3,4}));
        EXPECT_FALSE(this->tree.IsRangeFree({4,5}));

        // Max free block length should be 7 (positions [9,16))
        auto idx7 = this->tree.FindFree(7);
        ASSERT_TRUE(idx7.has_value());
        EXPECT_EQ(idx7.value(), 9);
    }
}
