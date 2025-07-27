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
#include "dockalloc/solver/time_interval_tree_node.h"

namespace dockalloc::solver
{
    static_assert(std::is_same_v<SearchResult<core::TimeInterval<uint32_t>, false>::ValueReturnType,
                                 const core::TimeInterval<uint32_t>&>,
                  "Complex types must be returned as const references");

    static_assert(std::is_same_v<SearchResult<int, false>::ValueReturnType, int>,
                  "Fundamental types must be returned by value");

    static_assert(sizeof(TimeIntervalTreeNode<uint8_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint8_t, 256> must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint16_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint16_t, 256> must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint32_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint32_t, 256> must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint64_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint64_t, 256> must fit into 256 bytes");

    // Check the amount of slots in the node
    static_assert(TimeIntervalTreeNode<uint64_t, 256>::kSlotSize == 8,
                  "TimeIntervalTreeNode<uint64_t, 256> must have 8 slots");
    static_assert(TimeIntervalTreeNode<uint32_t, 256>::kSlotSize == 14,
                  "TimeIntervalTreeNode<uint64_t, 256> must have 8 slots");
    // Check the number of children pointers in the node
    static_assert(TimeIntervalTreeNode<uint64_t, 256>::kChildrenSize == 9,
                  "TimeIntervalTreeNode<uint64_t, 256> must have 9 children");
    static_assert(TimeIntervalTreeNode<uint32_t, 256>::kChildrenSize == 15,
                  "TimeIntervalTreeNode<uint64_t, 256> must have 9 children");

    TEST(TimeIntervalTreeNodeTest, GetParentReturnsNullptrWhenUninitialized)
    {
        const TimeIntervalTreeNode<uint32_t, 256> node;
        EXPECT_EQ(node.GetParent(), nullptr);
    }

    TEST(TimeIntervalTreeNodeTest, SetAndGetInterval)
    {
        TimeIntervalTreeNode<uint32_t, 256> node;
        node.SetInterval(0, core::TimeInterval<uint32_t>(10, 20));
        EXPECT_EQ(node.GetInterval(0), core::TimeInterval<uint32_t>(10, 20));
    }

    TEST(TimeIntervalTreeNodeTest, IsLeafIsFalseByDefault)
    {
        const TimeIntervalTreeNode<uint32_t, 256> node;
        EXPECT_FALSE(node.IsLeaf());
    }

    TEST(TimeIntervalTreeNodeTest, SetIsLeaf)
    {
        TimeIntervalTreeNode<uint32_t, 256> node;
        node.SetIsLeaf(true);
        EXPECT_TRUE(node.IsLeaf());
        node.SetIsLeaf(false);
        EXPECT_FALSE(node.IsLeaf());
    }
}
