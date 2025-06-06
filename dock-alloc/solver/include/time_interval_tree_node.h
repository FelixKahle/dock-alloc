// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_
#define DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_

#include <type_traits>
#include "dockalloc/core/type_traits/smallest_unsigned_for.h"
#include "dockalloc/core/time/time_interval.h"
#include "dockalloc/solver/time_interval_tree_node_layout.h"

namespace dockalloc::solver
{
    /// @brief A node in a time-interval tree, which stores time intervals efficiently.
    ///
    /// This class represents a node in a time-interval tree, which is used to store
    /// time intervals efficiently. Each node contains an array of time intervals,
    /// pointers to child nodes, and aggregate fields for minimum start time,
    /// maximum end time, and maximum gap between intervals as well as some index fields.
    ///
    /// @tparam TimeType The unsigned integral type used for timestamp fields.
    /// @tparam TargetNodeSize The desired size in bytes of the generated node struct.
    template <typename TimeType, size_t TargetNodeSize>
        requires std::unsigned_integral<TimeType>
    class TimeIntervalTreeNode
    {
    public:
        using LayoutType = typename TimeIntervalTreeNodeLayout<TimeType, TimeIntervalTreeNode, TargetNodeSize>::Type;
        using IndexType = typename LayoutType::IndexType;

        TimeIntervalTreeNode()
            : layout_()
        {
        }

        /// @brief Returns a pointer to the parent node.
        ///
        /// This function returns a pointer to the parent node of this node.
        ///
        /// @return A pointer to the parent node, or \c nullptr if there is no parent.
        [[nodiscard]] const TimeIntervalTreeNode* GetParent() const noexcept
        {
            return layout_.GetParent();
        }

        /// @brief Gets a \c core::TimeInterval for the given index.
        ///
        /// This function returns a reference to the interval stored at the specified index.
        ///
        /// @param index The index of the interval to retrieve.
        ///
        /// @pre 0 <= index < kSlotSize
        ///
        /// @return A reference to the interval at the specified index.
        [[nodiscard]] const core::TimeInterval<TimeType>& GetInterval(const IndexType index) const noexcept
        {
            return layout_.GetInterval(index);
        }

        /// @brief Sets the interval at the specified index.
        ///
        /// This function sets the interval at the specified index to the given interval.
        ///
        /// @param index The index of the interval to set.
        /// @param interval The interval to set at the specified index.
        ///
        /// @pre 0 <= index < kSlotSize
        void SetInterval(const IndexType index, const core::TimeInterval<TimeType>& interval) noexcept
        {
            layout_.SetInterval(index, interval);
        }

        /// @brief Sets the interval at the specified index to a moved interval.
        ///
        /// This function sets the interval at the specified index to the given interval,
        /// which is moved into the storage.
        ///
        /// @param index The index of the interval to set.
        /// @param interval The interval to set at the specified index, which will be moved.
        ///
        /// @pre 0 <= index < kSlotSize
        void SetInterval(const IndexType index, core::TimeInterval<TimeType>&& interval) noexcept
        {
            layout_.SetInterval(index, std::move(interval));
        }

    private:
        LayoutType layout_{};
    };
}

#endif
