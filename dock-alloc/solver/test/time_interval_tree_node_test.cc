// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/time_interval_tree_node.h"

namespace dockalloc::solver
{
    static_assert(sizeof(TimeIntervalTreeNode<uint8_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint8_t, 256> must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint16_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint16_t, 256> must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint32_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint32_t, 256> must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint64_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint64_t, 256> must fit into 256 bytes");

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
}
