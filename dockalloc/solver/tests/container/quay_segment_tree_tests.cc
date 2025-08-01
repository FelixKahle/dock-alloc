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
        QuaySegmentTree<Position> tree{kSize};
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
        EXPECT_EQ(this->tree.FindFree(k).value(), k);

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
        EXPECT_TRUE(this->tree.IsRangeOccupied({2,3}));
        EXPECT_TRUE(this->tree.IsRangeFree({3,4}));
        EXPECT_TRUE(this->tree.IsRangeOccupied({4,5}));

        // Max free block length should be 7 (positions [9,16))
        auto idx7 = this->tree.FindFree(7);
        ASSERT_TRUE(idx7.has_value());
        EXPECT_EQ(idx7.value(), 9);
    }

    // Test for equality and inequality operators
    TYPED_TEST(SegmentTreeTest, EqualityAndInequality)
    {
        using Position = typename TestFixture::Position;
        QuaySegmentTree<Position> tree_a{this->kSize};
        QuaySegmentTree<Position> tree_b{this->kSize};
        QuaySegmentTree<Position> tree_c{this->kSize + 1};
        QuaySegmentTree<Position> tree_zero_a{0};
        QuaySegmentTree<Position> tree_zero_b{0};

        // 1. Reflexivity: A tree is equal to itself.
        EXPECT_TRUE(this->tree == this->tree);

        // 2. Initial state: Two newly created trees of the same size are equal.
        EXPECT_TRUE(tree_a == tree_b);
        EXPECT_FALSE(tree_a != tree_b);
        // 2.1. Zero-sized trees are equal.
        EXPECT_TRUE(tree_zero_a == tree_zero_b);

        // 3. Different sizes: Trees of different sizes are not equal.
        EXPECT_FALSE(tree_a == tree_c);
        EXPECT_TRUE(tree_a != tree_c);
        EXPECT_FALSE(tree_a == tree_zero_a);

        // 4. Same operations: Applying the same operations should maintain equality.
        tree_a.Occupy({2, 5});
        tree_b.Occupy({2, 5});
        tree_a.Free({3, 4});
        tree_b.Free({3, 4});
        EXPECT_TRUE(tree_a == tree_b);
        EXPECT_TRUE(tree_b == tree_a); // Symmetry

        // 5. Different operations: Applying different operations should result in inequality.
        tree_b.Occupy({8, 10}); // tree_b is now different
        EXPECT_FALSE(tree_a == tree_b);
        EXPECT_TRUE(tree_a != tree_b);
    }

    // Test that logical equality holds even with different internal lazy states.
    TYPED_TEST(SegmentTreeTest, LogicalEqualityWithDifferentInternalStates)
    {
        using Position = typename TestFixture::Position;
        QuaySegmentTree<Position> tree_a{this->kSize};
        QuaySegmentTree<Position> tree_b{this->kSize};

        // --- Scenario 1: Fully occupied ---
        // tree_a is occupied via two adjacent calls, potentially creating different
        // internal lazy nodes than a single call.
        tree_a.Occupy({0, this->kSize / 2});
        tree_a.Occupy({this->kSize / 2, this->kSize});

        // tree_b is occupied via a single call for the whole range.
        tree_b.Occupy({0, this->kSize});

        // Logically, they are identical. The `operator==` should see past the
        // different lazy propagation history and confirm they are both fully occupied.
        EXPECT_TRUE(tree_a == tree_b);
        EXPECT_FALSE(tree_a != tree_b);

        // --- Scenario 2: Partially occupied with a hole ---
        QuaySegmentTree<Position> tree_c{this->kSize};
        QuaySegmentTree<Position> tree_d{this->kSize};

        // Occupy a large segment [2, 10) on both trees.
        tree_c.Occupy({2, 10});
        tree_d.Occupy({2, 10});

        // Now, free up a middle segment [5, 7) in two different ways.
        // tree_c is freed with one single call.
        tree_c.Free({5, 7});
        // tree_d is freed with two adjacent calls.
        tree_d.Free({5, 6});
        tree_d.Free({6, 7});

        // The final state of the quay is identical, so the trees should be equal.
        EXPECT_TRUE(tree_c == tree_d);
        EXPECT_FALSE(tree_c != tree_d);
    }

    // NEW TESTS START HERE

    // Test with a size that is not a power of two to check padding logic.
    TYPED_TEST(SegmentTreeTest, NonPowerOfTwoSize)
    {
        using Position = typename TestFixture::Position;
        const Position non_pow_size = 23;
        QuaySegmentTree<Position> np_tree{non_pow_size};

        // Initially all free
        EXPECT_TRUE(np_tree.IsRangeFree({0, non_pow_size}));
        EXPECT_EQ(np_tree.FindFree(non_pow_size).value(), 0);

        // Occupy a segment
        np_tree.Occupy({5, 15});
        EXPECT_TRUE(np_tree.IsRangeOccupied({5, 15}));
        EXPECT_TRUE(np_tree.IsRangeFree({0, 5}));
        EXPECT_TRUE(np_tree.IsRangeFree({15, non_pow_size}));

        // Largest free block is now at the end
        Position largest_free_len = non_pow_size - 15;
        EXPECT_EQ(np_tree.FindFree(largest_free_len).value(), 15);
        // Second largest is at the beginning
        EXPECT_EQ(np_tree.FindFree(5).value(), 0);
        // No block larger than the largest free segment
        EXPECT_FALSE(np_tree.FindFree(largest_free_len + 1).has_value());
    }

    // Test FindFree with a specified search range.
    TYPED_TEST(SegmentTreeTest, FindFreeWithSearchRange)
    {
        // State: Free: [0,4), Occupied: [4,10), Free: [10,16)
        this->tree.Occupy({4, 10});

        // Search in the whole range, should find the larger block at 10.
        EXPECT_EQ(this->tree.FindFree(5, {0, this->kSize}).value(), 10);

        // Search only in the first free block. Should find at 0.
        EXPECT_EQ(this->tree.FindFree(3, {0, 4}).value(), 0);
        // Cannot find a block of size 5 in the first part.
        EXPECT_FALSE(this->tree.FindFree(5, {0, 4}).has_value());

        // Search only in the second free block.
        EXPECT_EQ(this->tree.FindFree(5, {10, this->kSize}).value(), 10);

        // Search in a range that contains the occupied block but not a large enough free space.
        EXPECT_FALSE(this->tree.FindFree(5, {2, 12}).has_value());
        // Search in a range that spans across the occupied block.
        // The largest free space is 4 at the beginning of the range [2,12)
        EXPECT_EQ(this->tree.FindFree(2, {2, 12}).value(), 2);
        // The largest free space is 2 at the end of the range [2,12)
        EXPECT_EQ(this->tree.FindFree(2, {10, 12}).value(), 10);
    }

    // Test complex fragmentation and then coalescing of free segments.
    TYPED_TEST(SegmentTreeTest, FragmentationAndCoalescing)
    {
        // Occupy everything first
        this->tree.Occupy({0, this->kSize});
        EXPECT_TRUE(this->tree.IsRangeOccupied({0, this->kSize}));

        // Free segments, creating fragmentation
        this->tree.Free({4, 6}); // Free [4,6)
        this->tree.Free({8, 10}); // Free [8,10)
        this->tree.Free({12, 14}); // Free [12,14)

        // Find should return the first available block of size 2
        EXPECT_EQ(this->tree.FindFree(2).value(), 4);
        // A block of size 3 should not be found
        EXPECT_FALSE(this->tree.FindFree(3).has_value());

        // Now, free the segment between the first two holes to coalesce them.
        this->tree.Free({6, 8}); // Coalesces with [4,6) and [8,10) to form [4,10)
        // We should now be able to find a block of size 6.
        EXPECT_EQ(this->tree.FindFree(6).value(), 4);
        EXPECT_TRUE(this->tree.IsRangeFree({4, 10}));
        // A block of size 7 should not be found yet.
        EXPECT_FALSE(this->tree.FindFree(7).has_value());

        // Coalesce all three blocks
        this->tree.Free({10, 12});
        EXPECT_EQ(this->tree.FindFree(10).value(), 4);
        EXPECT_TRUE(this->tree.IsRangeFree({4, 14}));
    }

    // Test overlapping free/occupy calls.
    TYPED_TEST(SegmentTreeTest, OverlappingUpdates)
    {
        // Occupy a large central block
        this->tree.Occupy({2, 12});
        EXPECT_TRUE(this->tree.IsRangeOccupied({2, 12}));
        // Free a range that overlaps with the occupied block
        this->tree.Free({8, 14});
        // Final state should be:
        // [0, 2) -> Free
        // [2, 8) -> Occupied
        // [8, 14) -> Free
        // [14, 16) -> Free
        EXPECT_TRUE(this->tree.IsRangeFree({0, 2}));
        EXPECT_TRUE(this->tree.IsRangeOccupied({2, 8}));
        EXPECT_TRUE(this->tree.IsRangeFree({8, 14}));
        EXPECT_TRUE(this->tree.IsRangeFree({14, this->kSize}));

        // The largest free block is [8, 16), size 8
        EXPECT_EQ(this->tree.FindFree(8).value(), 8);
        EXPECT_FALSE(this->tree.FindFree(9).has_value());
    }

    // Test operations on empty ranges are no-ops.
    TYPED_TEST(SegmentTreeTest, EmptyRangeOperations)
    {
        using Position = typename TestFixture::Position;
        QuaySegmentTree<Position> tree_before{this->kSize};
        // Operations on an empty range should not change the state.
        this->tree.Occupy({5, 5});
        this->tree.Free({8, 8});
        EXPECT_TRUE(this->tree == tree_before);
        EXPECT_TRUE(this->tree.IsRangeFree({0, this->kSize}));
        EXPECT_FALSE(this->tree.FindFree(this->kSize + 1).has_value());
    }

    // Test a tree with a single element.
    TYPED_TEST(SegmentTreeTest, SingleElementTree)
    {
        using Position = typename TestFixture::Position;
        QuaySegmentTree<Position> single_tree{1};

        EXPECT_TRUE(single_tree.IsRangeFree({0, 1}));
        EXPECT_EQ(single_tree.FindFree(1).value(), 0);

        single_tree.Occupy({0, 1});
        EXPECT_TRUE(single_tree.IsRangeOccupied({0, 1}));
        EXPECT_FALSE(single_tree.FindFree(1).has_value());

        single_tree.Free({0, 1});
        EXPECT_TRUE(single_tree.IsRangeFree({0, 1}));
        EXPECT_EQ(single_tree.FindFree(1).value(), 0);
    }

    // Test a tree with zero size.
    TYPED_TEST(SegmentTreeTest, ZeroSizeTree)
    {
        using Position = typename TestFixture::Position;
        QuaySegmentTree<Position> zero_tree{0};

        EXPECT_FALSE(zero_tree.FindFree(1).has_value());
        // Finding a block of size 0 should succeed at position 0.
        EXPECT_EQ(zero_tree.FindFree(0).value(), 0);
        // Any operation should be a no-op and not crash.
        zero_tree.Occupy({0, 0});
        zero_tree.Free({0, 10}); // Range is outside, should be ignored.
        QuaySegmentTree<Position> other_zero_tree{0};
        EXPECT_TRUE(zero_tree == other_zero_tree);
    }

    // Test that logically identical states created by different operation sequences are equal.
    TYPED_TEST(SegmentTreeTest, LogicalEqualityWithDifferentOperations)
    {
        using Position = typename TestFixture::Position;
        QuaySegmentTree<Position> tree_a{this->kSize};
        QuaySegmentTree<Position> tree_b{this->kSize};

        // Scenario: Create a state with free ends and an occupied middle.
        // Tree A: Occupy the whole range, then free the ends.
        tree_a.Occupy({0, this->kSize});
        tree_a.Free({0, 4});
        tree_a.Free({12, this->kSize});

        // Tree B: Start with a free range and occupy the middle.
        tree_b.Occupy({4, 12});

        EXPECT_TRUE(tree_a == tree_b);
        // Verify state of tree_b to be sure
        EXPECT_TRUE(tree_b.IsRangeFree({0,4}));
        EXPECT_TRUE(tree_b.IsRangeOccupied({4,12}));
        EXPECT_TRUE(tree_b.IsRangeFree({12, this->kSize}));
    }

    // Test FindFree when the only available spot is at the very end of the quay.
    TYPED_TEST(SegmentTreeTest, FindFreeAtTheEnd)
    {
        this->tree.Occupy({0, this->kSize - 4});

        EXPECT_TRUE(this->tree.IsRangeOccupied({0, this->kSize - 4}));
        EXPECT_TRUE(this->tree.IsRangeFree({this->kSize - 4, this->kSize}));

        auto result = this->tree.FindFree(4);
        ASSERT_TRUE(result.has_value());
        EXPECT_EQ(result.value(), this->kSize - 4);

        EXPECT_FALSE(this->tree.FindFree(5).has_value());
    }

    // Test FindFree for a block that straddles the midpoint of the root's children.
    TYPED_TEST(SegmentTreeTest, FindFreeStraddlingMidpoint)
    {
        // kSize is 16, midpoint is 8.
        // Occupy [0, 6) and [10, 16). This leaves [6, 10) free, straddling 8.
        this->tree.Occupy({0, 6});
        this->tree.Occupy({10, this->kSize});

        EXPECT_TRUE(this->tree.IsRangeFree({6, 10}));

        auto result = this->tree.FindFree(4);
        ASSERT_TRUE(result.has_value());
        EXPECT_EQ(result.value(), 6);

        auto result2 = this->tree.FindFree(3, {7, 10});
        ASSERT_TRUE(result2.has_value());
        EXPECT_EQ(result2.value(), 7);

        EXPECT_FALSE(this->tree.FindFree(5).has_value());
    }
}
