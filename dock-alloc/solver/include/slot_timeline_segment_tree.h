// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_SLOT_TIMELINE_SEGMENT_TREE_H_
#define DOCK_ALLOC_SOLVER_SLOT_TIMELINE_SEGMENT_TREE_H_

#include <cstdint>
#include "absl/log/check.h"

namespace dockalloc::solver
{
    /// @brief A segment tree with lazy propagation to track occupancy over a discrete timeline.
    ///
    /// This data structure allows efficient range updates and queries.
    class SlotTimelineSegmentTree
    {
    public:
        /// @brief Assignment type used in lazy propagation.
        enum class Assignment : uint8_t
        {
            /// @brief No pending update.
            kNone,
            /// @brief Mark the range as unoccupied.
            kSetFree,
            /// @brief Mark the range as occupied.
            kSetOccupied
        };

        /// @brief Constructor for the TimelineSegmentTree.
        ///
        /// @param size Initial size of the discrete timeline.
        explicit SlotTimelineSegmentTree(const size_t size)
            : root_(size > 0 ? std::make_unique<SlotTimeSegmentNode>(0, size - 1) : nullptr)
        {
        }

        /// @brief Check if the segment tree is empty.
        ///
        /// @return true if the segment tree is empty, false otherwise.
        [[nodiscard]] bool IsEmpty() const noexcept
        {
            return root_ == nullptr;
        }

    private:
        /// @brief Internal tree node representing a segment [start_...end_].
        class SlotTimeSegmentNode
        {
        public:
            /// @brief Constructor for a segment node.
            ///
            /// @param start The start index of the segment.
            /// @param end The end index of the segment.
            explicit SlotTimeSegmentNode(const size_t start, const size_t end) noexcept
                : start_(start), end_(end), left_(nullptr), right_(nullptr), occupied_(false),
                  lazy_(Assignment::kNone)
            {
            }

            /// @brief Check if this node is a leaf (covers a single index).
            ///
            /// @return true if this node is a leaf, false otherwise.
            [[nodiscard]] bool IsLeaf() const noexcept
            {
                return start_ == end_;
            }


            /// @brief Getter for the start of the segment.
            ///
            /// @return The start of the segment.
            [[nodiscard]] size_t GetStart() const noexcept
            {
                return start_;
            }

            /// @brief Getter for the end of the segment.
            ///
            /// @return The end of the segment.
            [[nodiscard]] size_t GetEnd() const noexcept
            {
                return end_;
            }

            /// @brief Getter for the occupied status of the segment.
            ///
            /// @return The occupied status of the segment.
            [[nodiscard]] bool IsOccupied() const noexcept
            {
                return occupied_;
            }

            /// @brief Getter for the lazy tag of the segment.
            ///
            /// @return The lazy tag of the segment.
            [[nodiscard]] Assignment GetLazy() const noexcept
            {
                return lazy_;
            }

            /// @brief Getter for the left child of the segment.
            ///
            /// @return A Pointer to the left child node.
            ///
            /// @note If IsLeaf() is true, this function returns nullptr.
            [[nodiscard]] SlotTimeSegmentNode* GetLeft() const noexcept
            {
                if (IsLeaf())
                {
                    return nullptr;
                }

                if (left_)
                {
                    return left_.get();
                }

                const auto self = const_cast<SlotTimeSegmentNode*>(this);
                const size_t mid = start_ + (end_ - start_) / 2;
                self->left_ = std::make_unique<SlotTimeSegmentNode>(start_, mid);
                return self->left_.get();
            }

            /// @brief Getter for the right child of the segment.
            ///
            /// @return A Pointer to the right child node.
            ///
            /// @note If IsLeaf() is true, this function returns nullptr.
            [[nodiscard]] SlotTimeSegmentNode* GetRight() const noexcept
            {
                if (IsLeaf())
                {
                    return nullptr;
                }

                if (right_)
                {
                    return right_.get();
                }

                const auto self = const_cast<SlotTimeSegmentNode*>(this);
                const size_t mid = start_ + (end_ - start_) / 2;
                self->right_ = std::make_unique<SlotTimeSegmentNode>(mid + 1, end_);
                return self->right_.get();
            }

            /// @brief Apply an assignment to this node and mark it as lazy.
            ///
            /// This does not propagate the assignment to children immediately.
            ///
            /// @param assignment The assignment to apply (occupied or free).
            void ApplyAssignmentToNode(const Assignment assignment) noexcept
            {
                lazy_ = assignment;
                switch (assignment)
                {
                case Assignment::kSetOccupied: occupied_ = true;
                    break;
                case Assignment::kSetFree: occupied_ = false;
                    break;
                case Assignment::kNone: break;
                }
            }

            /// @brief Propagate any pending assignment to child nodes.
            ///
            /// Used during updates and queries to ensure correctness.
            void PropagateToChildren() noexcept
            {
                // Nothing to do if no pending assignment or if leaf
                if (lazy_ == Assignment::kNone || IsLeaf())
                {
                    return;
                }

                // Ensure children exist (lazily create them if needed)
                SlotTimeSegmentNode* left_child = GetLeft();
                SlotTimeSegmentNode* right_child = GetRight();

                // Push the assignment down
                left_child->ApplyAssignmentToNode(lazy_);
                right_child->ApplyAssignmentToNode(lazy_);

                // Clear this node’s lazy tag
                lazy_ = Assignment::kNone;

                // Recompute occupied status: occupied if either child is occupied
                occupied_ = left_child->IsOccupied() || right_child->IsOccupied();
            }

            /// @brief Check if a range is occupied.
            ///
            /// This function checks if the range [start...end] is occupied.
            ///
            /// @param start The start index of the range.
            /// @param end The end index of the range.
            ///
            /// @return true if the range is occupied, false otherwise.
            [[nodiscard]] bool IsRangeOccupied(const size_t start, const size_t end) const noexcept // NOLINT(*-no-recursion)
            {
                // Check if the range is completely outside this segment.
                // If so, the segment is not occupied by definition.
                if (end < start_ || end_ < start)
                {
                    return false;
                }

                // Check if the range is completely inside this segment.
                // If so, return the occupied status of this segment.
                if (start <= start_ && end_ <= end)
                {
                    return occupied_;
                }

                // Partial overlap → must push down then ask children
                const auto self = const_cast<SlotTimeSegmentNode*>(this);
                self->PropagateToChildren();
                return GetLeft()->IsRangeOccupied(start, end) || GetRight()->IsRangeOccupied(start, end);
            }

            /// @brief Check if a range is free.
            ///
            /// This function checks if the range [start...end] is free.
            ///
            /// @param start The start index of the range.
            /// @param end The end index of the range.
            ///
            /// @return true if the range is free, false otherwise.
            [[nodiscard]] bool IsRangeFree(const size_t start, const size_t end) const noexcept
            {
                return !IsRangeOccupied(start, end);
            }

            /// @brief Sets a range to free.
            ///
            /// This function updates the range [start...end] to be free.
            ///
            /// @param start The start index of the range.
            /// @param end The end index of the range.
            void SetRangeFree(const size_t start, const size_t end) noexcept
            {
                UpdateRange(start, end, Assignment::kSetFree);
            }

            /// @brief Sets a range to occupied.
            ///
            /// This function updates the range [start...end] to be occupied.
            ///
            /// @param start The start index of the range.
            /// @param end The end index of the range.
            void SetRangeOccupied(const size_t start, const size_t end) noexcept
            {
                UpdateRange(start, end, Assignment::kSetOccupied);
            }

            /// @brief Update a range with a given assignment.
            ///
            /// This function updates the range [start...end] with the specified assignment.
            ///
            /// @param start The start index of the range.
            /// @param end The end index of the range.
            void UpdateRange(const size_t start, const size_t end, const Assignment assignment) noexcept // NOLINT(*-no-recursion)
            {
                // Check if the range is completely outside this segment.
                if (end < start_ || end_ < start)
                {
                    return;
                }

                // Check if the range is completely inside this segment.
                if (start <= start_ && end_ <= end)
                {
                    ApplyAssignmentToNode(assignment);
                    return;
                }

                // Partial overlap: push any pending to children
                PropagateToChildren();

                // Recurse
                GetLeft()->UpdateRange(start, end, assignment);
                GetRight()->UpdateRange(start, end, assignment);

                // Recompute occupied status
                occupied_ = GetLeft()->IsOccupied() || GetRight()->IsOccupied();
            }

        private:
            size_t start_;
            size_t end_;
            std::unique_ptr<SlotTimeSegmentNode> left_;
            std::unique_ptr<SlotTimeSegmentNode> right_;
            bool occupied_;
            Assignment lazy_;
        };

        std::unique_ptr<SlotTimeSegmentNode> root_;
    };
}

#endif
