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

        TimeIntervalTreeNode(const TimeIntervalTreeNode& other) noexcept = delete;
        TimeIntervalTreeNode& operator=(const TimeIntervalTreeNode&) noexcept = delete;

        /// @brief Returns a pointer to the parent node.
        ///
        /// This function returns a pointer to the parent node of this node.
        ///
        /// @return A pointer to the parent node, or \c nullptr if there is no parent.
        [[nodiscard]] const TimeIntervalTreeNode* GetParent() const noexcept
        {
            return layout_.GetParent();
        }

        /// @brief Sets the parent node.
        ///
        /// This function sets the parent node of this node to the given pointer.
        ///
        /// @param parent A pointer to the parent node to set.
        void SetParent(TimeIntervalTreeNode* parent) noexcept
        {
            layout_.SetParent(parent);
        }

        /// @brief Returns the minimum start time of the intervals in this node.
        ///
        /// This function returns the minimum start time of all intervals stored in this node.
        ///
        /// @return The minimum start time of the intervals in this node.
        [[nodiscard]] TimeType GetMinStartTime() const noexcept
        {
            return layout_.GetMinStartTime();
        }

        /// @brief Sets the minimum start time of the intervals in this node.
        ///
        /// This function sets the minimum start time of all intervals stored in this node.
        ///
        /// @param min_start_time The minimum start time to set.
        void SetMinStartTime(TimeType min_start_time) noexcept
        {
            layout_.SetMinStartTime(min_start_time);
        }

        /// @brief Returns the maximum end time of the intervals in this node.
        ///
        /// This function returns the maximum end time of all intervals stored in this node.
        ///
        /// @return The maximum end time of the intervals in this node.
        [[nodiscard]] TimeType GetMaxEndTime() const noexcept
        {
            return layout_.GetMaxEndTime();
        }

        /// @brief Sets the maximum end time of the intervals in this node.
        ///
        /// This function sets the maximum end time of all intervals stored in this node.
        ///
        /// @param max_end_time The maximum end time to set.
        void SetMaxEndTime(TimeType max_end_time) noexcept
        {
            layout_.SetMaxEndTime(max_end_time);
        }

        /// @brief Returns the maximum gap between intervals in this node.
        ///
        /// This function returns the maximum gap between any two intervals stored in this node.
        ///
        /// @return The maximum gap between intervals in this node.
        [[nodiscard]] TimeType GetMaxGap() const noexcept
        {
            return layout_.GetMaxGap();
        }

        /// @brief Sets the maximum gap between intervals in this node.
        ///
        /// This function sets the maximum gap between any two intervals stored in this node.
        ///
        /// @param max_gap The maximum gap to set.
        void SetMaxGap(TimeType max_gap) noexcept
        {
            layout_.SetMaxGap(max_gap);
        }

        /// @brief Returns the start index of the intervals in this node.
        ///
        /// This function returns the index of the first interval in this node.
        ///
        /// @return The start index of the intervals in this node.
        [[nodiscard]] IndexType GetStartIndex() const noexcept
        {
            return layout_.GetStartIndex();
        }

        /// @brief Sets the start index of the intervals in this node.
        ///
        /// This function sets the index of the first interval in this node.
        ///
        /// @param index The start index to set.
        void SetStartIndex(IndexType index) noexcept
        {
            layout_.SetStartIndex(index);
        }

        /// @brief Returns the finish index of the intervals in this node.
        ///
        /// This function returns the index of the last interval in this node.
        ///
        /// @return The finish index of the intervals in this node.
        [[nodiscard]] IndexType GetFinishIndex() const noexcept
        {
            return layout_.GetFinishIndex();
        }

        /// @brief Sets the finish index of the intervals in this node.
        ///
        /// This function sets the index of the last interval in this node.
        ///
        /// @param index The finish index to set.
        void SetFinishIndex(IndexType index) noexcept
        {
            layout_.SetFinishIndex(index);
        }

        /// @brief Returns the index of the parent.
        ///
        /// This function returns the index of the parent.
        ///
        /// @return The index of the parent.
        [[nodiscard]] IndexType GetParentIndex() const noexcept
        {
            return layout_.GetParentIndex();
        }

        /// @brief Sets the index of the parent.
        ///
        /// This function sets the index of the parent.
        ///
        /// @param parent_index The index of the parent to set.
        void SetParentIndex(const IndexType& parent_index) noexcept
        {
            layout_.SetParentIndex(parent_index);
        }

        /// @brief Returns a pointer to the child node at the specified index.
        ///
        /// This function returns a pointer to the child node at the specified index.
        ///
        /// @param index The index of the child node to retrieve.
        ///
        /// @pre 0 <= index < kChildrenSize
        ///
        /// @return A pointer to the child node at the specified index, or \c nullptr if there is no child.
        [[nodiscard]] const TimeIntervalTreeNode* GetChild(const IndexType index) const noexcept
        {
            return layout_.GetChild(index);
        }

        /// @brief Sets the child node at the specified index.
        ///
        /// This function sets the child node at the specified index to the given pointer.
        ///
        /// @param index The index of the child node to set.
        /// @param child A pointer to the child node to set.
        ///
        /// @pre 0 <= index < kChildrenSize
        void SetChild(const IndexType index, const TimeIntervalTreeNode* child) noexcept
        {
            layout_.SetChild(index, child);
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

        /// @brief Checks if this node is a leaf node.
        ///
        /// This function checks if this node is a leaf node,
        /// which means it has no children.
        ///
        /// @return \c true if this node is a leaf, \c false otherwise.
        [[nodiscard]] bool IsLeaf() const noexcept
        {
            return layout_.GetChild(0) == nullptr;
        }

        /// @brief Checks if this node is an internal node.
        ///
        /// This function checks if this node is an internal node,
        /// which means it has at least one child.
        ///
        /// @return \c true if this node is internal, \c false if it is a leaf.
        [[nodiscard]] bool IsInternal() const noexcept
        {
            return !IsLeaf();
        }

        /// @brief Returns the number of intervals stored in this node.
        ///
        /// This function returns the number of intervals stored in this node,
        /// which is the difference between the finish and start indices.
        ///
        /// @return The number of intervals stored in this node.
        [[nodiscard]] IndexType GetNumIntervals() const noexcept
        {
            return GetFinishIndex() - GetStartIndex();
        }

    private:
        LayoutType layout_{};
    };
}

#endif
