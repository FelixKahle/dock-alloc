// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_
#define DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_

#include "dockalloc/core/type_traits/bigger.h"
#include "dockalloc/core/type_traits/smallest_unsigned_for.h"
#include "dockalloc/core/time/time_interval.h"

namespace dockalloc::solver
{
    /// @brief Computes a node struct layout for a time-interval tree, matching a target byte size.
    ///
    /// @tparam TimeType The unsigned integral type used for timestamp fields.
    /// @tparam TargetNodeSize The desired size in bytes of the generated node struct.
    ///
    /// Internally, a compile-time binary search is performed to find the optimal slot count
    /// (each slot holds a \c TimeInterval<TimeType>) so that the resulting \c Type alias
    /// refers to a struct whose \c sizeof is as close to \p TargetNodeSize. Each node stores
    /// an array of \p SlotSize intervals, plus parent/child pointers, aggregate min/max/gap
    /// fields, and slot indices. Depending on whether \p TimeType is wider than the unsigned
    /// index type, some timestamp fields are laid out before or after the index fields to
    /// minimize padding.
    ///
    /// Example:
    /// @code
    ///   // For 32-bit time types, find a node layout that packs into 128 bytes:
    ///   using Node128 = TimeIntervalTreeNodeLayout<uint32_t, 128>::Type;
    ///   static_assert(sizeof(Node128) <= 128, "Layout must fit into 128 bytes");
    /// @endcode
    template <typename TimeType, size_t TargetNodeSize>
        requires std::unsigned_integral<TimeType>
    struct TimeIntervalTreeNodeLayout
    {
        /// @brief The layout of a time-interval tree node, with optimized padding.
        ///
        /// The layout is determined by the \p SLotSize and whether \p TimeType is wider
        /// then the smallest unsigned type that can hold the number of slots.
        ///
        /// @tparam SlotSize the number of slots in the node, must be at least 4.
        /// @tparam TimeTypeWider whether \p TimeType is wider than the smallest unsigned type
        template <size_t SlotSize, bool TimeTypeWider>
            requires (SlotSize >= 4)
        struct LayoutImpl;

        /// @brief The layout of a time-interval tree node, with optimized padding.
        ///
        /// The layout is determined by the \p SLotSize and whether \p TimeType is wider
        /// then the smallest unsigned type that can hold the number of slots.
        ///
        /// @tparam SlotSize the number of slots in the node, must be at least 4.
        template <size_t SlotSize>
            requires (SlotSize >= 4)
        struct LayoutImpl<SlotSize, true>
        {
            static constexpr size_t kSlotSize = SlotSize;
            static constexpr size_t kChildrenSize = SlotSize + 1;

            using PointerType = void*;
            using IndexType = core::SmallestUnsignedFor_t<SlotSize + 1>;

            PointerType parent_;
            PointerType children_[kChildrenSize];
            core::TimeInterval<TimeType> intervals_[kSlotSize];
            TimeType min_start_time_;
            TimeType max_end_time_;
            TimeType max_gap_;
            IndexType start_index_;
            IndexType finish_index_;
            IndexType parent_index_;
        };

        /// @brief The layout of a time-interval tree node, with optimized padding.
        ///
        /// The layout is determined by the \p SLotSize and whether \p TimeType is wider
        /// then the smallest unsigned type that can hold the number of slots.
        ///
        /// @tparam SlotSize the number of slots in the node, must be at least 4.
        template <size_t SlotSize>
            requires (SlotSize >= 4)
        struct LayoutImpl<SlotSize, false>
        {
            static constexpr size_t kSlotSize = SlotSize;
            static constexpr size_t kChildrenSize = SlotSize + 1;

            using PointerType = void*;
            using IndexType = core::SmallestUnsignedFor_t<SlotSize + 1>;

            PointerType parent_;
            PointerType children_[kChildrenSize];
            core::TimeInterval<TimeType> intervals_[kSlotSize];
            IndexType start_index_;
            IndexType finish_index_;
            IndexType parent_index_;
            TimeType min_start_time_;
            TimeType max_end_time_;
            TimeType max_gap_;
        };

        /// @brief The layout of a time-interval tree node, with optimized padding.
        ///
        /// The layout is determined by the \p SLotSize and whether \p TimeType is wider
        /// then the smallest unsigned type that can hold the number of slots.
        ///
        /// @tparam SlotSize the number of slots in the node, must be at least 4.
        template <size_t SlotSize>
            requires (SlotSize >= 4)
        using Layout = LayoutImpl<SlotSize, core::Bigger_v<TimeType, core::SmallestUnsignedFor_t<SlotSize + 1>>>;

    private:
        /// @brief Computes the number of slots that fit into the target node size.
        ///
        /// This is done using a compile-time binary search to find the maximum number of slots
        /// that can fit into the target node size, ensuring that the resulting layout
        /// is as close to \p TargetNodeSize as possible.
        ///
        /// @tparam Begin The lower bound of the search range, must be at least 4.
        /// @tparam End The upper bound of the search range, must be greater than \p Begin.
        ///
        /// @return The number of slots that fit into the target node size.
        template <size_t Begin, size_t End>
            requires (Begin >= 4)
        static constexpr size_t NodeTargetSlots() noexcept // NOLINT(*-no-recursion)
        {
            // @formatter:off
            return Begin == End ? Begin : sizeof(Layout<(Begin + End) / 2 + 1>) > TargetNodeSize
                ? NodeTargetSlots<Begin, (Begin + End) / 2>() : NodeTargetSlots<(Begin + End) / 2 + 1, End>();
            // @formatter:on
        }

    public:
        enum
        {
            /// @brief The number of slots in the time-interval tree node.
            ///
            /// This is determined by the compile-time binary search to find the maximum number of slots
            /// that can fit into the target node size.
            NodeSlotSize = NodeTargetSlots<4, TargetNodeSize>(),

            /// @brief The size of children each node can have.
            ///
            /// This is the number of child pointers in the node, which is one more than the number of slots.
            NodeChildSize = NodeSlotSize + 1,
        };

        /// @brief The type of the time-interval tree node layout, with optimized padding and slot count.
        ///
        /// This is the result of the compile-time binary search to find the optimal slot count
        /// and the compile time layout of the node.
        using Type = Layout<NodeSlotSize>;
    };

    template <typename TimeType, size_t TargetNodeSize>
        requires std::unsigned_integral<TimeType>
    class TimeIntervalTreeNode
    {
    private:
        typename TimeIntervalTreeNodeLayout<TimeType, TargetNodeSize>::Type layout_;
    };
}

#endif
