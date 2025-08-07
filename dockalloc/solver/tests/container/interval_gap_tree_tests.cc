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
#include "dockalloc/solver/container/interval_gap_tree.h"

namespace dockalloc::solver
{
    TEST(IntervalGapTreeTest, ConstructorConstructsTree)
    {
        struct Case
        {
            size_t segments_;
            size_t expected_leaf_;
            size_t expected_height_;
            size_t expected_node_count_;
        };
        std::vector<Case> cases = {
            {0, 0, 0, 0}, // zero segments → empty tree
            {1, 1, 1, 2}, // leaf_count=1, height=1, nodes=2
            {2, 2, 2, 4}, // leaf_count=2, height=2, nodes=4
            {3, 4, 3, 8}, // leaf_count=4, height=3, nodes=8
            {16, 16, 5, 32}, // leaf_count=16, height=5, nodes=32
            {17, 32, 6, 64}, // leaf_count=32, height=6, nodes=64
            {21, 32, 6, 64} // leaf_count=32, height=6, nodes=64
        };

        for (auto& c : cases)
        {
            IntervalGapTree tree{c.segments_};
            EXPECT_EQ(tree.GetSegmentCount(), c.segments_);
            EXPECT_EQ(tree.GetLeafCount(), c.expected_leaf_);
            EXPECT_EQ(tree.GetHeight(), c.expected_height_);
            EXPECT_EQ(tree.GetNodeCount(), c.expected_node_count_);
        }
    }

    TEST(IntervalGapTreeTest, ConstructorInitialStateAsFree)
    {
        IntervalGapTree tree{10};
        EXPECT_TRUE(tree.IsRangeFree(0, 10));
        EXPECT_FALSE(tree.IsRangeOccupied(0, 10));
    }

    TEST(IntervalGapTreeTest, ConstructorInitialStateIsOccupied)
    {
        IntervalGapTree tree{10, false};
        EXPECT_TRUE(tree.IsRangeOccupied(0, 10));
        EXPECT_FALSE(tree.IsRangeFree(0, 10));
    }

    TEST(IntervalGapTreeTest, OccupyMarksOccupied)
    {
        IntervalGapTree tree{10};
        tree.Occupy(0, 10);
        EXPECT_FALSE(tree.IsRangeFree(0, 10));
        EXPECT_TRUE(tree.IsRangeOccupied(0, 10));
    }

    TEST(IntervalGapTreeTest, OccupyFullRange)
    {
        IntervalGapTree tree{8};
        tree.Occupy(0, 8);
        EXPECT_TRUE(tree.IsRangeOccupied(0, 8));
        EXPECT_FALSE(tree.IsRangeFree(0, 8));
    }

    TEST(IntervalGapTreeTest, FreeRestoresFree)
    {
        IntervalGapTree tree{10};
        tree.Occupy(3, 7);
        tree.Free(3, 7);
        EXPECT_TRUE(tree.IsRangeFree(3, 7));
        EXPECT_FALSE(tree.IsRangeOccupied(3, 7));
    }

    TEST(IntervalGapTreeTest, EmptyRangeOperationsNoOp)
    {
        IntervalGapTree tree{12};
        tree.Occupy(5, 5);
        tree.Free(5, 5);
        EXPECT_TRUE(tree.IsRangeFree(0, 12));
        EXPECT_FALSE(tree.IsRangeOccupied(0, 12));
    }

    TEST(IntervalGapTreeTest, FindFirstFreeRangeEmptyTree)
    {
        IntervalGapTree t{0};
        EXPECT_FALSE(t.FindFirstFreeRange(1).has_value());
        // For a zero-sized tree, even a zero-length request should find nothing.
        const auto z = t.FindFirstFreeRange(0);
        EXPECT_FALSE(z.has_value());
    }

    TEST(IntervalGapTreeTest, FindFirstFreeRangeWholeTree)
    {
        IntervalGapTree t{8};
        auto opt = t.FindFirstFreeRange(3);
        ASSERT_TRUE(opt.has_value());
        EXPECT_EQ(*opt, 0);
        EXPECT_FALSE(t.FindFirstFreeRange(9).has_value());
        auto z = t.FindFirstFreeRange(0);
        EXPECT_FALSE(z.has_value());
        EXPECT_EQ(*z, 0);
    }

    TEST(IntervalGapTreeTest, FindFirstFreeRangeAfterOccupy)
    {
        IntervalGapTree t{10};
        t.Occupy(2, 5);

        // want=2 fits at 0
        {
            auto o = t.FindFirstFreeRange(2);
            ASSERT_TRUE(o.has_value());
            EXPECT_EQ(*o, 0);
        }

        // want=3 doesn't fit at 0 (free length=2) but fits at 5
        {
            auto o = t.FindFirstFreeRange(3);
            ASSERT_TRUE(o.has_value());
            EXPECT_EQ(*o, 5);
        }

        // want=6 too big for both
        EXPECT_FALSE(t.FindFirstFreeRange(6).has_value());
    }

    TEST(IntervalGapTreeTest, FindFirstFreeRangeWithSearchRange)
    {
        IntervalGapTree t{12};
        t.Occupy(3, 6);
        t.Occupy(8, 10);
        // overall free segments: [0,3),[6,8),[10,12)

        // restrict search to [0,3):
        {
            const auto o = t.FindFirstFreeRange(2, 0, 3);
            ASSERT_TRUE(o.has_value());
            EXPECT_EQ(*o, 0);
            EXPECT_FALSE(t.FindFirstFreeRange(4, 0, 3).has_value());
        }

        // restrict to [6,8):
        {
            const auto o = t.FindFirstFreeRange(1, 6, 8);
            ASSERT_TRUE(o.has_value());
            EXPECT_EQ(*o, 6);
        }

        // restrict to a window containing no free gap of length 2:
        EXPECT_FALSE(t.FindFirstFreeRange(2, 3, 6).has_value());
    }

    TEST(IntervalGapTreeTest, DefaultTreesAreEqual)
    {
        const IntervalGapTree a{10};
        const IntervalGapTree b{10};
        EXPECT_TRUE(a == b);
        EXPECT_FALSE(a != b);
    }

    TEST(IntervalGapTreeTest, DifferentSizesNotEqual)
    {
        const IntervalGapTree small{8};
        const IntervalGapTree large{16};
        EXPECT_FALSE(small == large);
        EXPECT_TRUE(small != large);
    }

    TEST(IntervalGapTreeTest, SameOperationsYieldEqual)
    {
        IntervalGapTree a{20};
        IntervalGapTree b{20};

        // perform the same occupy/free sequence on both
        a.Occupy(3, 10);
        a.Free(15, 18);
        b.Occupy(3, 10);
        b.Free(15, 18);

        EXPECT_TRUE(a == b);
        EXPECT_FALSE(a != b);
    }

    TEST(IntervalGapTreeTest, DifferentOperationsNotEqual)
    {
        IntervalGapTree a{20};
        IntervalGapTree b{20};

        // a marks [5,12) occupied; b marks [5,12) free (default)
        a.Occupy(5, 12);

        EXPECT_FALSE(a == b);
        EXPECT_TRUE(a != b);
    }

    TEST(IntervalGapTreeTest, NestedUniformSubtreeShortcut)
    {
        IntervalGapTree a{32};
        IntervalGapTree b{32};
        a.Occupy(0, 16);
        b.Occupy(0, 16);

        a.Occupy(20, 25);

        EXPECT_FALSE(a == b);
        EXPECT_TRUE(a != b);
    }

    TEST(IntervalGapTreeTest, FreeRangeIteratorSimple)
    {
        IntervalGapTree tree{30};
        tree.Occupy(10, 20);

        // Free ranges are [0,10) and [20,30)

        std::vector<size_t> free_positions_len9;
        for (auto it = tree.BeginFreeRanges(10); it != tree.EndFreeRanges(); ++it)
        {
            free_positions_len9.push_back(*it);
        }
        ASSERT_EQ(free_positions_len9.size(), 2);
        EXPECT_EQ(free_positions_len9[0], 0);
        EXPECT_EQ(free_positions_len9[1], 20);
    }

    TEST(IntervalGapTreeTest, FreeRangeIteratorWithMultipleGaps)
    {
        IntervalGapTree tree{30};
        // Free gaps will be: [0,3), [5,10), [12,20), [25,30)
        tree.Occupy(3, 5);
        tree.Occupy(10, 12);
        tree.Occupy(20, 25);

        // Search for a length that fits in some but not all gaps.
        // Required length = 4.
        std::vector<size_t> found_positions;
        for (auto it = tree.BeginFreeRanges(4); it != tree.EndFreeRanges(); ++it)
        {
            found_positions.push_back(*it);
        }

        // Let's calculate the expected positions:
        // [0,3): length=3, can't fit length=4
        // [5,10): length=5, can fit 4 at positions: 5, 6 (since 6+4=10)
        // [12,20): length=8, can fit 4 at positions: 12, 13, 14, 15, 16 (since 16+4=20)
        // [25,30): length=5, can fit 4 at positions: 25, 26 (since 26+4=30)
        const std::vector<size_t> expected_positions = {5, 6, 12, 13, 14, 15, 16, 25, 26};
        EXPECT_EQ(found_positions, expected_positions);
    }

    TEST(IntervalGapTreeTest, FreeRangeIteratorWithSearchRange)
    {
        IntervalGapTree tree{30};
        // Free gaps will be: [0,3), [5,10), [12,20), [25,30)
        tree.Occupy(3, 5);
        tree.Occupy(10, 12);
        tree.Occupy(20, 25);

        // Search for a length of 2, but only within the window [4, 22).
        // This window excludes the free gaps [0,3) and [25,30).
        std::vector<size_t> found_positions;
        for (auto it = tree.BeginFreeRanges(2, 4, 22); it != tree.EndFreeRanges(); ++it)
        {
            found_positions.push_back(*it);
        }
        const std::vector<size_t> expected_positions = {5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 18};
        EXPECT_EQ(found_positions, expected_positions);
    }

    TEST(IntervalGapTreeTest, FreeRangeIteratorNoResults)
    {
        IntervalGapTree tree{30};
        // Free gaps will be: [0,3), [5,10), [12,20), [25,30)
        tree.Occupy(3, 5);
        tree.Occupy(10, 12);
        tree.Occupy(20, 25);

        // Case 1: Required length is too large for any gap.
        {
            auto it = tree.BeginFreeRanges(9);
            EXPECT_EQ(it, tree.EndFreeRanges()) << "Should not find any gap of length 9";
        }

        // Case 2: The search window is entirely within an occupied block.
        {
            auto it = tree.BeginFreeRanges(1, 21, 24);
            EXPECT_EQ(it, tree.EndFreeRanges()) << "Should not find any gap in an occupied range";
        }

        // Case 3: A fully occupied tree.
        {
            IntervalGapTree full_tree{20, false};
            auto it = full_tree.BeginFreeRanges(1);
            EXPECT_EQ(it, full_tree.EndFreeRanges()) << "Should not find any gaps in a fully occupied tree";
        }
    }

    template <size_t N>
    std::vector<size_t> CollectIteratorResults(const IntervalGapTree<N>& tree, size_t required_length)
    {
        std::vector<size_t> results;
        for (auto it = tree.BeginFreeRanges(required_length); it != tree.EndFreeRanges(); ++it)
        {
            results.push_back(*it);
        }
        return results;
    }

    template <size_t N>
    std::vector<size_t> CollectIteratorResults(const IntervalGapTree<N>& tree, size_t required_length, size_t start,
                                               size_t end)
    {
        std::vector<size_t> results;
        for (auto it = tree.BeginFreeRanges(required_length, start, end); it != tree.EndFreeRanges(); ++it)
        {
            results.push_back(*it);
        }
        return results;
    }

    class IntervalGapTreeIteratorTest : public ::testing::Test
    {
    protected:
        void SetUp() override
        {
            tree.Occupy(5, 10);
            tree.Occupy(11, 20);
            tree.Occupy(30, 31);
            tree.Occupy(40, 50);
            tree.Occupy(70, 90);
        }

        [[nodiscard]] IntervalGapTree<8>& GetTree()
        {
            return tree;
        }

    private:
        // Each test gets its own fresh copy of this tree.
        IntervalGapTree<8> tree{100, true};
    };

    TEST_F(IntervalGapTreeIteratorTest, IteratorFindsAllPossibleSingleSlots)
    {
        std::vector<size_t> expected;

        // Programmatically add expected ranges to avoid "magic numbers"
        // Gap [0, 5)
        expected.reserve(5);
        for (size_t i = 0; i < 5; ++i) expected.push_back(i);
        // Gap [10, 11)
        expected.push_back(10);
        // Gap [20, 30)
        for (size_t i = 20; i < 30; ++i) expected.push_back(i);
        // Gap [31, 40)
        for (size_t i = 31; i < 40; ++i) expected.push_back(i);
        // Gap [50, 70)
        for (size_t i = 50; i < 70; ++i) expected.push_back(i);
        // Gap [90, 100)
        for (size_t i = 90; i < 100; ++i) expected.push_back(i);

        EXPECT_EQ(CollectIteratorResults(GetTree(), 1), expected);
    }

    TEST_F(IntervalGapTreeIteratorTest, IteratorFindsFitsOfLength5)
    {
        std::vector<size_t> expected;

        auto add_range = [&](const size_t start, const size_t end)
        {
            for (size_t i = start; i <= end; ++i) expected.push_back(i);
        };

        // Gap [0, 5) -> size 5. Valid start: 0
        add_range(0, 0);
        // Gap [20, 30) -> size 10. Valid starts: 20, 21, 22, 23, 24, 25
        add_range(20, 25);
        // Gap [31, 40) -> size 9. Valid starts: 31, 32, 33, 34, 35
        add_range(31, 35);
        // Gap [50, 70) -> size 20. Valid starts: 50 through 65
        add_range(50, 65);
        // Gap [90, 100) -> size 10. Valid starts: 90 through 95
        add_range(90, 95);

        EXPECT_EQ(CollectIteratorResults(GetTree(), 5), expected);
    }

    TEST_F(IntervalGapTreeIteratorTest, IteratorRespectsBoundedSearchRange)
    {
        std::vector<size_t> expected;
        for (int i = 31; i <= 35; ++i) expected.push_back(i);
        for (int i = 50; i <= 59; ++i) expected.push_back(i);
        EXPECT_EQ(CollectIteratorResults(GetTree(), 5, 30, 60), expected);
    }

    TEST_F(IntervalGapTreeIteratorTest, IteratorFindsLargerGapsAfterMerging)
    {
        IntervalGapTree<8>& tree = GetTree();
        tree.Free(10, 20);
        const std::vector<size_t> expected = {10, 50};
        EXPECT_EQ(CollectIteratorResults(tree, 20), expected);
    }
}
