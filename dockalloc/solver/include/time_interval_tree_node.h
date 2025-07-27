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

#ifndef DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_
#define DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_

#include <type_traits>
#include "dockalloc/core/type_traits/type_traits.h"
#include "dockalloc/core/miscellaneous/core_defines.h"
#include "dockalloc/solver/time_interval_tree_node_layout.h"

namespace dockalloc::solver
{
    /// @brief An enumeration representing the kind of match for time intervals.
    enum class MatchKind : uint8_t
    {
        /// @brief The intervals are not equal.
        ///
        /// Indicates that at least one of the start or end times differs
        /// between the two intervals.
        NotEqual,

        /// @brief The intervals are equal.
        ///
        /// Indicates that both the start time and end time match exactly.
        Equal,
    };

    /// @brief A class representing the result of a search operation in a time interval tree.
    ///
    /// This class encapsulates the result of a search operation in a time interval tree,
    /// allowing for both the value found and the kind of match that occurred.
    template <typename Value, bool IsCompareTo>
    class SearchResult;

    /// @brief A specialization of SearchResult for when comparison is needed.
    ///
    /// This specialization is used when the search result includes match information,
    /// allowing for the determination of whether the found value is equal to the searched value.
    template <typename Value>
    class SearchResult<Value, true>
    {
    public:
        /// @brief The type alias for the return type of the value stored in this search result.
        ///
        /// This type alias is used to determine the return type of the value stored in this search result.
        /// It uses \c std::conditional_t to choose between \c Value and \c const Value& based
        /// on whether \c Value is a fundamental type.
        using ValueReturnType = std::conditional_t<std::is_fundamental_v<Value>, Value, const Value&>;

        /// @brief Constructs a search result with the given value and match kind.
        ///
        /// This constructor initializes the search result with the specified value
        /// and match kind.
        ///
        /// @param value The value to store in this search result.
        /// @param match The match kind of this search result.
        explicit constexpr SearchResult(const Value value, const MatchKind match)
            : value_(value),
              match_(match)
        {
        }

        /// @brief Returns the match kind of this search result.
        ///
        /// This function provides access to the match kind of this search result,
        ///
        /// @return The match kind of this search result.
        [[nodiscard]] constexpr MatchKind GetMatchKind() const
        {
            return match_;
        }

        /// @brief Returns the value stored in this search result.
        ///
        /// This function provides access to the value stored in this search result.
        ///
        /// @return A reference to the value stored in this search result.
        [[nodiscard]] constexpr ValueReturnType GetValue() const
        {
            return value_;
        }

        /// @brief Checks if there is a match.
        ///
        /// This function always returns \c true, since match info exists.
        ///
        /// @return \c true always, since match info exists.
        [[nodiscard]] static constexpr bool HasMatch()
        {
            return true;
        }

        /// @brief Checks if the match is an exact match.
        ///
        /// This function checks if the match kind is \c MatchKind::Equal,
        ///
        /// @return \c true if the match is an exact match, \c false otherwise.
        [[nodiscard]] bool IsEqual() const
        {
            return match_ == MatchKind::Equal;
        }

    private:
        Value value_;
        MatchKind match_;
    };

    /// @brief A specialization of SearchResult for when no comparison is needed.
    ///
    /// This specialization is used when the search result does not include match information,
    /// allowing for a simpler representation of the found value without match details.
    template <typename Value>
    class SearchResult<Value, false>
    {
    public:
        /// @brief The type alias for the return type of the value stored in this search result.
        ///
        /// This type alias is used to determine the return type of the value stored in this search result.
        /// It uses \c std::conditional_t to choose between \c Value and \c const Value& based
        /// on whether \c Value is a fundamental type.
        using ValueReturnType = std::conditional_t<std::is_fundamental_v<Value>, Value, const Value&>;

        /// @brief Constructs a search result with the given value.
        ///
        /// This constructor initializes the search result with the specified value.
        ///
        /// @param value The value to store in this search result.
        explicit constexpr SearchResult(const Value value)
            : value_(value)
        {
        }

        /// Returns the value stored in this search result.
        ///
        /// This function provides access to the value stored in this search result.
        ///
        /// @return A reference to the value stored in this search result.
        [[nodiscard]] constexpr ValueReturnType GetValue() const noexcept
        {
            return value_;
        }

        /// @brief Checks if there is a match (not supported here).
        ///
        /// This function always returns \c false, since no match info exists.
        ///
        /// @return \c false always, since no match info exists.
        [[nodiscard]] static constexpr bool HasMatch() noexcept
        {
            return false;
        }

        /// @brief Checks for exact match (not supported here).
        ///
        /// This function always returns \c false, since no match info exists.
        ///
        /// @return \c false always, since no match info exists.
        [[nodiscard]] static constexpr bool IsEqual() noexcept
        {
            return false;
        }

    private:
        Value value_;
    };

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

        /// @brief The number of child pointers in the node, which is one more than the number of slots.
        ///
        /// This is the number of child pointers in the node, which is one more than the number of slots.
        static constexpr size_t kChildrenSize = LayoutType::kChildrenSize;

        /// @brief The number of slots in the node, determined by the compile-time binary search.
        ///
        /// This is the number of \c TimeInterval<TimeType> slots in the node, which is determined
        /// by the compile-time binary search to find the optimal slot count.
        static constexpr size_t kSlotSize = LayoutType::kSlotSize;

        TimeIntervalTreeNode()
            : layout_()
        {
        }

        TimeIntervalTreeNode(const TimeIntervalTreeNode& other) noexcept = delete;
        TimeIntervalTreeNode& operator=(const TimeIntervalTreeNode&) noexcept = delete;

        /// @brief Returns whether this node is a leaf node.
        ///
        /// This function checks if this node is a leaf node,
        /// which means it has no children.
        ///
        /// @return \c true if this node is a leaf, \c false otherwise.
        [[nodiscard]] bool IsLeaf() const noexcept
        {
            return layout_.IsLeaf();
        }

        /// @brief Returns whether this node is an internal node.
        ///
        /// This function checks if this node is an internal node,
        /// which means it has at least one child.
        ///
        /// @return \c true if this node is internal, \c false if it is a leaf.
        [[nodiscard]] bool IsInternal() const noexcept
        {
            return layout_.IsInternal();
        }

        /// @brief Sets whether this node is a leaf node.
        ///
        /// This function sets the leaf status of this node to the given value.
        ///
        /// @param value The value to set for the leaf status of this node.
        void SetIsLeaf(bool value) noexcept
        {
            layout_.SetIsLeaf(value);
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

        /// @brief Returns the maximum end time of the intervals in this node.
        ///
        /// This function returns the maximum end time of all intervals stored in this node.
        ///
        /// @return The maximum end time of the intervals in this node.
        [[nodiscard]] TimeType GetMaxEndTime() const noexcept
        {
            return layout_.GetMaxEndTime();
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
        /// @brief Sets the minimum start time of the intervals in this node.
        ///
        /// This function sets the minimum start time of all intervals stored in this node.
        ///
        /// @param min_start_time The minimum start time to set.
        void SetMinStartTime(TimeType min_start_time) noexcept
        {
            layout_.SetMinStartTime(min_start_time);
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

        /// @brief Sets the maximum gap between intervals in this node.
        ///
        /// This function sets the maximum gap between any two intervals stored in this node.
        ///
        /// @param max_gap The maximum gap to set.
        void SetMaxGap(TimeType max_gap) noexcept
        {
            layout_.SetMaxGap(max_gap);
        }

        LayoutType layout_{};
    };
}

#endif
