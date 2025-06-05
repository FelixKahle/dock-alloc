// Copyright 2025 Felix Kahle. All rights reserved.

#include "dockalloc/solver/time_interval_tree_node.h"

namespace dockalloc::solver
{
    static_assert(sizeof(TimeIntervalTreeNodeLayout<uint8_t, 256>::Type) <= 256,
                  "TimeIntervalTreeNodeLayout<uint8_t, 256>::Type must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNodeLayout<uint16_t, 256>::Type) <= 256,
                  "TimeIntervalTreeNodeLayout<uint16_t, 256>::Type must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNodeLayout<uint32_t, 256>::Type) <= 256,
                  "TimeIntervalTreeNodeLayout<uint32_t, 256>::Type must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNodeLayout<uint64_t, 256>::Type) <= 256,
                  "TimeIntervalTreeNodeLayout<uint64_t, 256>::Type must fit into 256 bytes");

    static_assert(sizeof(TimeIntervalTreeNode<uint8_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint8_t, 256> must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint16_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint16_t, 256> must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint32_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint32_t, 256> must fit into 256 bytes");
    static_assert(sizeof(TimeIntervalTreeNode<uint64_t, 256>) <= 256,
                  "TimeIntervalTreeNode<uint64_t, 256> must fit into 256 bytes");
}
