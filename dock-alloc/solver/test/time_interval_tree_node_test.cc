// Copyright 2025 Felix Kahle. All rights reserved.

#include "dockalloc/solver/time_interval_tree_node.h"

namespace dockalloc::solver
{
    static_assert(sizeof(TimeIntervalTreeNode<uint8_t, 256>) <= 256, "Node exceeds 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint16_t, 256>) <= 256, "Node exceeds 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint32_t, 256>) <= 256, "Node exceeds 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint64_t, 256>) <= 256, "Node exceeds 256 bytes");

    static_assert(sizeof(TimeIntervalTreeNode<uint8_t, 512>) <= 512, "Node exceeds 512 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint16_t, 512>) <= 512, "Node exceeds 512 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint32_t, 512>) <= 512, "Node exceeds 512 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint64_t, 512>) <= 512, "Node exceeds 512 bytes");
}
