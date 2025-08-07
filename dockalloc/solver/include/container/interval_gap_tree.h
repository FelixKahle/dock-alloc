// Copyright (c) 2025 Felix Kahle.
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do, subject to
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

#ifndef DOCK_ALLOC_SOLVER_CONTAINER_INTERVAL_GAP_TREE_H_
#define DOCK_ALLOC_SOLVER_CONTAINER_INTERVAL_GAP_TREE_H_

#include <optional>
#include <vector>
#include <algorithm>
#include <bit>
#include "absl/log/check.h"
#include "absl/container/inlined_vector.h"
#include "dockalloc/core/miscellaneous/core_types.h"
#include "dockalloc/core/container/stack.h"

namespace dockalloc::solver
{
    /// @brief Segment tree for managing and querying contiguous free intervals.
    ///
    /// This class uses a segment tree data structure to maintain the occupancy state of one dimension.
    /// Each node in the tree stores the longest free prefix,
    /// longest free suffix, and the maximum free contiguous gap within its range. This allows
    /// for highly efficient range updates, range queries, and, most importantly, finding a
    /// free segment of a required length in logarithmic time.
    ///
    /// @tparam ExpectedMaxTreeHeight The expected maximum height of the tree, used for stack allocation. Must be
    /// greater than 0. Default is 32.
    template <size_t ExpectedMaxTreeHeight = 32>
        requires (ExpectedMaxTreeHeight > 0)
    class IntervalGapTree
    {
        /// @brief Represents the state for lazy propagation updates.
        enum class LazyState : uint8_t
        {
            /// @brief No pending update for this node.
            None = 255,
            /// @brief The range is marked as free.
            Free = 0,
            /// @brief The range is marked as occupied.
            Occupied = 1
        };

        /// @brief A node in the segment tree.
        struct Node
        {
            /// @brief The longest free prefix of this segment.
            size_t length_of_longest_free_prefix{0};
            /// @brief The longest free suffix of this segment.
            size_t length_of_longest_free_suffix{0};
            /// @brief The maximum free gap in this segment.
            size_t length_of_maximum_free_gap{0};
            /// @brief The total length of this segment.
            size_t segment_length{0};
            /// @brief The lazy state for this node.
            LazyState lazy_propagation_state{LazyState::None};
        };

        /// @brief Frame for the iterative equality comparison.
        struct EqualFrame
        {
            /// @brief The index of the node to compare in both trees.
            size_t node_index_to_compare;
        };

    public:
        /// @brief Iterator that yields the starting positions of free ranges of a specified length in a given range.
        ///
        /// This iterator allows efficient traversal of the segment tree to find all starting positions
        /// of free segments that are at least as long as the specified required length.
        class FreeRangeIterator
        {
            struct FindFrame
            {
                /// @brief The index of the current node in the segment tree.
                size_t node_index;
                /// @brief The starting index of the segment represented by the node.
                size_t segment_start_index;
                /// @brief The ending index of the segment represented by the node.
                size_t segment_end_index;
                /// @brief Flag to indicate if the left child has already been processed.
                bool has_processed_left_child;
            };

        public:
            using value_type = size_t;
            using difference_type = std::ptrdiff_t;
            using reference = const size_t&;
            using pointer = const size_t*;
            using iterator_category = std::forward_iterator_tag;

            /// @brief Dereferences the iterator to get the current free range starting position.
            ///
            /// This method returns the current position of the iterator, which is the starting index
            /// of the free range that matches the required length.
            ///
            /// @pre The iterator must not be an "end" iterator.
            ///
            /// @return A reference to the current position, or an error if the iterator is at the end.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE reference operator*() const noexcept
            {
                DCHECK(current_position_.has_value()) << "Cannot dereference an end iterator.";

                return *current_position_;
            }

            /// @brief Accesses the current free range's starting position via a pointer.
            ///
            /// This method returns a pointer to the current position of the iterator,
            /// which is the starting index of the free range that matches the required length.
            ///
            /// @pre The iterator must not be an "end" iterator.
            ///
            /// @return A pointer to the current position, or an error if the iterator is at the end.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE pointer operator->() const noexcept
            {
                DCHECK(current_position_.has_value()) << "Cannot dereference an end iterator.";

                return &(*current_position_);
            }

            /// @brief Advances the iterator to the next possible starting position (prefix increment).
            ///
            /// This method increments the iterator to the next valid starting position
            /// of a free range that is at least as long as the required length.
            ///
            /// @pre The iterator must not be an "end" iterator.
            ///
            /// @return A reference to the updated iterator.
            DOCK_ALLOC_FORCE_INLINE FreeRangeIterator& operator++() noexcept
            {
                DCHECK(current_position_.has_value()) << "Cannot increment an end iterator.";

                // First, try the most efficient move: just slide one position to the right.
                (*current_position_)++;

                // Check if this new position is still a valid start for the required length
                // within the currently identified large free gap.
                if (*current_position_ + required_length_ <= active_gap_end_)
                {
                    return *this;
                }

                // We have exhausted all possible start positions in the current gap.
                // We must find the next distinct free gap in the tree.
                // The search for the next gap should start from our current (now invalid) position.
                next_search_position_ = *current_position_;
                Advance();
                return *this;
            }

            /// @brief Advances the iterator to the next possible starting position (postfix increment).
            ///
            /// This method increments the iterator to the next valid starting position
            /// of a free range that is at least as long as the required length.
            ///
            /// @pre The iterator must not be an "end" iterator.
            ///
            /// @return A copy of the iterator before incrementing.
            DOCK_ALLOC_FORCE_INLINE FreeRangeIterator operator++(int) noexcept
            {
                FreeRangeIterator tmp = *this;
                ++*this;
                return tmp;
            }

            /// @brief Compares two iterators for equality.
            ///
            /// This method checks if two iterators point to the same position in the segment tree.
            /// If both iterators are "end" iterators, they are also considered equal.
            ///
            /// @param other The other iterator to compare against.
            ///
            /// @return \c true if both iterators point to the same position, \c false otherwise.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool operator==(const FreeRangeIterator& other) const noexcept
            {
                return current_position_ == other.current_position_;
            }

            /// @brief Compares two iterators for inequality.
            ///
            /// This method checks if two iterators do not point to the same position in the segment tree.
            /// If one iterator is an "end" iterator and the other is not, they are considered unequal.
            ///
            /// @param other The other iterator to compare against.
            ///
            /// @return \c true if the iterators point to different positions, \c false if they are equal.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool operator!=(const FreeRangeIterator& other) const noexcept
            {
                return !(*this == other);
            }

        private:
            friend class IntervalGapTree;

            /// @brief Default constructor creates an "end" iterator.
            FreeRangeIterator() = default;

            /// @brief Constructs a FreeRangeIterator for the specified tree and search parameters.
            ///
            /// This constructor initializes the iterator to search for free ranges of a specified length
            /// within a given search range.
            ///
            /// @param tree The segment tree to search within.
            /// @param required_length The minimum length of the free segment to find.
            /// @param search_start The starting index of the search range (inclusive).
            /// @param search_end The ending index of the search range (exclusive).
            ///
            /// @pre search_start <= search_end
            /// @pre search_end <= tree->GetSegmentCount()
            /// @pre search_range <= tree->GetSegmentCount() if tree is not null.
            FreeRangeIterator(const IntervalGapTree* tree, const size_t required_length, const size_t search_start,
                              const size_t search_end) noexcept
                : tree_(tree),
                  required_length_(required_length),
                  search_start_bound_(search_start),
                  search_end_bound_(search_end),
                  next_search_position_(search_start)
            {
                DCHECK_LE(search_start, search_end);

                // Check for conditions where no search is possible. If so, create an "end" iterator.
                if (tree_ == nullptr || required_length_ == 0 || search_start_bound_ >= search_end_bound_ ||
                    required_length_ > tree->GetSegmentCount())
                {
                    current_position_ = std::nullopt;
                }
                else
                {
                    DCHECK_LE(search_end, tree->GetSegmentCount());

                    // Pre-allocate memory for the traversal stack to avoid reallocations.
                    stack_.reserve(tree->GetHeight());
                    // Start the traversal at the root of the tree (index 1).
                    // The root covers the entire conceptual range [0, number_of_leaf_nodes_).
                    stack_.push({1, 0, tree_->GetLeafCount(), false});
                    // Immediately call Advance() to find the *first* valid position.
                    // This "primes" the iterator, so a valid begin iterator already points to the first result.
                    Advance();
                }
            }

            /// @brief Finds the *next* valid gap and sets the iterator to its first position.
            ///
            /// This method performs a depth-first traversal of the segment tree to find the next valid
            /// starting position of a free range that is at least as long as the required length.
            /// The first call has a complexity of O(log N), where N is the number of segments.
            /// Every subsequent call to `Advance()` will also have O(log N) complexity,
            /// but most of the time it will be O(1) due to the iterator's state being maintained.
            void Advance() noexcept
            {
                // Loop as long as there are nodes to explore in our traversal stack.
                while (!stack_.empty())
                {
                    // Get the next node to process from the stack.
                    FindFrame frame = stack_.top();
                    stack_.pop();

                    // If the node's range is entirely outside our search window, skip it.
                    if (frame.segment_end_index <= next_search_position_ || // Node is before our search start
                        frame.segment_start_index >= search_end_bound_) // Node is after our search end
                    {
                        continue; // Skip this node and its entire subtree.
                    }

                    // If the largest possible gap in this node's entire range is smaller than what we need,
                    // there's no point in searching further down this branch.
                    if (const auto& node = tree_->segment_tree_nodes_[frame.node_index]; node.length_of_maximum_free_gap
                        < required_length_)
                    {
                        continue; // Skip this node and its entire subtree.
                    }

                    // This flag simulates recursion. If we haven't processed the left child yet...
                    if (!frame.has_processed_left_child)
                    {
                        // This is the "pre-order" part of the traversal.
                        // Mark that we are now processing the left side.
                        frame.has_processed_left_child = true;
                        // Push the current frame back onto the stack. We'll return to it in the "post-order" step.
                        stack_.push(frame);
                        // Ensure any lazy updates on the current node are pushed to its children before we visit them.
                        tree_->Push(frame.node_index);

                        // Push the left child onto the stack to be processed next.
                        const size_t mid = (frame.segment_start_index + frame.segment_end_index) >> 1;
                        stack_.push({
                            frame.node_index << 1, // Left child index
                            frame.segment_start_index,
                            mid,
                            false // New frame, so left child is not yet processed.
                        });
                    }
                    else
                    {
                        // This is the "post-order" part. We have finished with the left child.
                        // Now, push the right child to be processed.
                        const size_t mid = (frame.segment_start_index + frame.segment_end_index) >> 1;
                        stack_.push({frame.node_index << 1 | 1, mid, frame.segment_end_index, false});

                        // Check for a gap that might span across the boundary of the left and right children.
                        const auto& left_node = tree_->segment_tree_nodes_[frame.node_index << 1];
                        const auto& right_node = tree_->segment_tree_nodes_[(frame.node_index << 1) | 1];

                        // Calculate the effective suffix/prefix, clipped to the search bounds.
                        const size_t eff_suf = CalculateEffectiveSuffix(left_node, mid);
                        if (const size_t eff_pre = CalculateEffectivePrefix(right_node, mid); eff_suf + eff_pre >=
                            required_length_)
                        {
                            // Define the full extent of this boundary gap.
                            const size_t boundary_start = mid - eff_suf;
                            const size_t boundary_end = mid + eff_pre;

                            // Check if a block of required_length can fit starting at this position.
                            if (const size_t first_possible_pos = std::max(boundary_start, next_search_position_);
                                first_possible_pos + required_length_ <= boundary_end)
                            {
                                // Success! We found a valid starting position.
                                // Set the iterator's state to point to this new find.
                                current_position_ = first_possible_pos;
                                // Record the end of this large gap to allow for efficient `++` operations.
                                active_gap_end_ = boundary_end;
                                // Update the search bookmark to prevent finding this same spot again on the next `Advance`.
                                next_search_position_ = *current_position_ + 1;
                                return; // We are done. Exit the Advance() method.
                            }
                        }
                    }
                }

                // If the while loop finishes, the stack is empty, meaning no more gaps were found.
                // The iterator becomes an "end" iterator.
                current_position_ = std::nullopt;
            }

            /// @brief Calculates the length of a left child's suffix, clipped by the search boundaries.
            ///
            /// This method computes the effective length of the longest free suffix
            /// of the left child node, ensuring it does not exceed the user-defined search bounds.
            ///
            /// @param left_node The left child node to analyze.
            /// @param mid The midpoint index of the parent node, used to determine the suffix start.
            ///
            /// @return The effective length of the suffix, clipped to the search bounds.
            DOCK_ALLOC_FORCE_INLINE size_t CalculateEffectiveSuffix(const Node& left_node, size_t mid) const noexcept
            {
                if (left_node.length_of_longest_free_suffix == 0)
                {
                    return 0;
                }
                // Calculate the true start of the suffix.
                const size_t suffix_start = mid - left_node.length_of_longest_free_suffix;
                // Clip the start and end of the suffix to the user-specified search window.
                const size_t clipped_start = std::max(suffix_start, search_start_bound_);
                const size_t clipped_end = std::min(mid, search_end_bound_);
                // Return the length of the clipped suffix.
                return (clipped_end > clipped_start) ? clipped_end - clipped_start : 0;
            }

            /// @brief Calculates the length of a right child's prefix, clipped by the search boundaries.
            ///
            /// This method computes the effective length of the longest free prefix
            /// of the right child node, ensuring it does not exceed the user-defined search bounds.
            ///
            /// @param right_node The right child node to analyze.
            /// @param mid The midpoint index of the parent node, used to determine the prefix end.
            ///
            /// @return The effective length of the prefix, clipped to the search bounds.
            DOCK_ALLOC_FORCE_INLINE size_t CalculateEffectivePrefix(const Node& right_node, size_t mid) const noexcept
            {
                if (right_node.length_of_longest_free_prefix == 0)
                {
                    return 0;
                }
                // Calculate the true end of the prefix.
                const size_t prefix_end = mid + right_node.length_of_longest_free_prefix;
                // Clip the start and end of the prefix to the user-specified search window.
                const size_t clipped_start = std::max(mid, search_start_bound_);
                const size_t clipped_end = std::min(prefix_end, search_end_bound_);
                // Return the length of the clipped prefix.
                return (clipped_end > clipped_start) ? clipped_end - clipped_start : 0;
            }


            const IntervalGapTree* tree_ = nullptr;
            size_t required_length_{};
            size_t search_start_bound_{};
            size_t search_end_bound_{};
            size_t next_search_position_{};
            std::optional<size_t> current_position_{std::nullopt};
            size_t active_gap_end_{0};
            core::reservable_stack<FindFrame, absl::InlinedVector<FindFrame, ExpectedMaxTreeHeight>> stack_;
        };

        /// @brief Creates an iterator pointing to the start of free ranges of a specified length within the entire tree.
        ///
        /// This method initializes an iterator that will traverse the segment tree,
        /// yielding the starting positions of all free segments that are at least as long as the specified required length.
        ///
        /// @param required_length The minimum length of the free segment to find.
        ///
        /// @return A \c FreeRangeIterator that starts at the first valid position of a free segment of the required length.
        [[nodiscard]] FreeRangeIterator BeginFreeRanges(const size_t required_length) const noexcept
        {
            return FreeRangeIterator(this, required_length, 0, number_of_segments_);
        }

        /// @brief Creates an iterator pointing to the start of free ranges of a specified length within a specific search range.
        ///
        /// This method initializes an iterator that will traverse the segment tree,
        /// yielding the starting positions of all free segments that are at least as long as the specified required length,
        /// within the specified search range.
        ///
        /// @param required_length The minimum length of the free segment to find.
        /// @param search_start The starting index of the search range (inclusive).
        /// @param search_end The ending index of the search range (exclusive).
        ///
        /// @pre search_start <= search_end
        ///
        /// @return A \c FreeRangeIterator that starts at the first valid position of a free segment of the required length
        [[nodiscard]] FreeRangeIterator BeginFreeRanges(const size_t required_length, const size_t search_start,
                                                        const size_t search_end) const noexcept
        {
            const size_t effective_search_end = std::min(search_end, number_of_segments_);
            if (search_start >= effective_search_end)
            {
                return EndFreeRanges();
            }
            return FreeRangeIterator(this, required_length, search_start, effective_search_end);
        }

        /// @brief Creates an "end" iterator that signifies the end of the free ranges.
        ///
        /// This method returns an iterator that represents the end of the free ranges,
        /// indicating that there are no more valid starting positions to iterate over.
        ///
        /// @return A \c FreeRangeIterator that acts as an "end" iterator.
        [[nodiscard]] FreeRangeIterator EndFreeRanges() const noexcept
        {
            return FreeRangeIterator();
        }

        /// @brief A proxy object that represents a range of free segments.
        ///
        /// This view class makes it possible to use a range-based for loop
        /// to iterate over all valid starting positions for a free run of segments.
        class FreeRangeView
        {
        public:
            /// @brief Constructs a view for iterating over free ranges.
            ///
            /// This constructor initializes the view with the specified segment tree and search parameters.
            ///
            /// @param tree The segment tree to search within.
            /// @param required_length The minimum length of the free segment to find.
            /// @param search_start The starting index of the search range (inclusive).
            /// @param search_end The ending index of the search range (exclusive).
            FreeRangeView(const IntervalGapTree* tree, const size_t required_length, const size_t search_start,
                          const size_t search_end)
                : tree_(tree),
                  required_length_(required_length),
                  search_start_(search_start),
                  search_end_(search_end)
            {
            }

            /// @brief Returns the begin iterator for the range.
            ///
            /// This method returns an iterator that points to the first valid starting position
            /// for a contiguous run of clear bits of the specified length within the range defined by
            /// \p search_start and \p search_end.
            ///
            /// @return A \c FreeRangeIterator that starts at the first valid position of a free
            /// segment of the required length.
            [[nodiscard]] auto begin() const
            {
                return tree_->BeginFreeRanges(required_length_, search_start_, search_end_);
            }

            /// @brief Returns the end iterator for the range.
            ///
            /// This method returns an iterator that signifies the end of the valid free range positions,
            /// indicating that there are no more valid starting positions to iterate over.
            ///
            /// @return A \c FreeRangeIterator that acts as an "end" iterator.
            [[nodiscard]] auto end() const
            {
                return tree_->EndFreeRanges();
            }

        private:
            const IntervalGapTree* tree_;
            size_t required_length_;
            size_t search_start_;
            size_t search_end_;
        };

        /// @brief Returns a range-based for-loop compatible view of all free ranges.
        ///
        /// @param required_length The minimum required length of the free segment.
        ///
        /// @return A view object that can be used in a for-each loop.
        [[nodiscard]] FreeRangeView FindFreeRanges(size_t required_length) const noexcept
        {
            return FreeRangeView(this, required_length, 0, number_of_segments_);
        }

        /// @brief Returns a range-based for-loop compatible view of all free ranges within a sub-range.
        ///
        /// @param required_length The minimum required length of the free segment.
        /// @param search_start The starting index of the search range (inclusive).
        /// @param search_end The ending index of the search range (exclusive).
        ///
        /// @return A view object that can be used in a for-each loop.
        [[nodiscard]] FreeRangeView FindFreeRanges(size_t required_length, size_t search_start,
                                                   size_t search_end) const noexcept
        {
            return FreeRangeView(this, required_length, search_start, search_end);
        }

        /// @brief Constructs a segment tree for managing
        ///
        /// The internal storage is padded to the next power of two to simplify
        /// tree traversal arithmetic. The tree is then built from the bottom up,
        /// aggregating the state of the leaf nodes.
        /// This runs in O(N) time, where N is the number of segments.
        ///
        /// @param initial_number_of_segments The number of segments to manage.
        /// @param initially_free If \c true, all segments are initialized as free; otherwise, they
        /// are initialized as occupied.
        explicit IntervalGapTree(const size_t initial_number_of_segments,
                                 const bool initially_free = true) noexcept
        {
            if (initial_number_of_segments == 0) [[unlikely]]
            {
                return;
            }

            // Record how many segments the user asked for.
            number_of_segments_ = initial_number_of_segments;

            // Compute the number of leaves in our segment tree array.
            // We need number_of_leaf_nodes_ to be a power of two ≥ initial_number_of_segments,
            // so that the binary tree is complete and simplifies indexing.
            // Mathematically: number_of_leaf_nodes_ = 2^⌈log₂(initial_number_of_segments)⌉
            number_of_leaf_nodes_ = std::bit_ceil(initial_number_of_segments);

            // Compute the tree’s height (number of levels).
            // C++20’s bit_width(x) returns ⌊log₂(x)⌋ + 1 for x>0.
            // For number_of_leaf_nodes = 2^h, bit_width(number_of_leaf_nodes) = h+1,
            // which corresponds to h+1 levels (root at level 1, leaves at level h+1).
            tree_height_ = static_cast<size_t>(std::bit_width(number_of_leaf_nodes_));

            // Allocate storage for all nodes.
            // A full binary tree with L leaves has exactly 2*L nodes
            // (indices [1..2*L-1], ignoring index 0).
            segment_tree_nodes_.resize(2 * number_of_leaf_nodes_);

            const size_t leaf_nodes_start_index = number_of_leaf_nodes_;
            const size_t user_segments_end_index = leaf_nodes_start_index + number_of_segments_;
            const size_t padded_leaf_nodes_end_index = 2 * number_of_leaf_nodes_;

            for (size_t leaf_index = leaf_nodes_start_index; leaf_index < user_segments_end_index; ++leaf_index)
            {
                auto& current_node = segment_tree_nodes_[leaf_index];
                current_node.segment_length = 1;
                if (initially_free)
                {
                    current_node.length_of_longest_free_prefix = 1;
                    current_node.length_of_longest_free_suffix = 1;
                    current_node.length_of_maximum_free_gap = 1;
                }
                else
                {
                    current_node.length_of_longest_free_prefix = 0;
                    current_node.length_of_longest_free_suffix = 0;
                    current_node.length_of_maximum_free_gap = 0;
                }
                current_node.lazy_propagation_state = LazyState::None;
            }

            for (size_t leaf_index = user_segments_end_index; leaf_index < padded_leaf_nodes_end_index; ++leaf_index)
            {
                auto& current_node = segment_tree_nodes_[leaf_index];
                current_node.segment_length = 1;
                current_node.length_of_longest_free_prefix = 0;
                current_node.length_of_longest_free_suffix = 0;
                current_node.length_of_maximum_free_gap = 0;
                current_node.lazy_propagation_state = LazyState::None;
            }

            size_t parent_node_index = number_of_leaf_nodes_ - 1;
            while (parent_node_index > 0)
            {
                auto& current_node = segment_tree_nodes_[parent_node_index];
                auto& left_child_node = segment_tree_nodes_[parent_node_index << 1];
                auto& right_child_node = segment_tree_nodes_[(parent_node_index << 1) | 1];

                current_node.segment_length = left_child_node.segment_length + right_child_node.segment_length;

                current_node.length_of_longest_free_prefix = (left_child_node.length_of_longest_free_prefix ==
                                                                 left_child_node.segment_length)
                                                                 ? left_child_node.segment_length + right_child_node.
                                                                 length_of_longest_free_prefix
                                                                 : left_child_node.length_of_longest_free_prefix;

                current_node.length_of_longest_free_suffix = (right_child_node.length_of_longest_free_suffix ==
                                                                 right_child_node.segment_length)
                                                                 ? right_child_node.segment_length + left_child_node.
                                                                 length_of_longest_free_suffix
                                                                 : right_child_node.length_of_longest_free_suffix;

                current_node.length_of_maximum_free_gap = std::max({
                    left_child_node.length_of_maximum_free_gap, right_child_node.length_of_maximum_free_gap,
                    left_child_node.length_of_longest_free_suffix + right_child_node.length_of_longest_free_prefix
                });

                current_node.lazy_propagation_state = LazyState::None;

                --parent_node_index;
            }
        }

        /// @brief Gets the total number of segments managed by the tree.
        ///
        /// @return The number of segments specified at construction.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t GetSegmentCount() const noexcept
        {
            return number_of_segments_;
        }

        /// @brief Gets the height of the internal segment tree.
        ///
        /// @return The height of the tree, where a tree with a single node has height 1.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t GetHeight() const noexcept
        {
            return tree_height_;
        }

        /// @brief Gets the number of leaf nodes in the segment tree.
        ///
        /// @note This can be larger than the actual number of segments due to padding to the next power of two.
        ///
        /// @return The number of leaf nodes.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t GetLeafCount() const noexcept
        {
            return number_of_leaf_nodes_;
        }

        /// @brief Gets the total number of nodes in the segment tree's storage.
        ///
        /// @return The size of the underlying node vector.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t GetNodeCount() const noexcept
        {
            return segment_tree_nodes_.size();
        }

        /// @brief Marks a specified range of segments as occupied.
        ///
        /// This is an efficient O(log N) operation due to lazy propagation.
        ///
        /// @param start_index_inclusive The starting index of the range to occupy (inclusive).
        /// @param end_index_exclusive The ending index of the range to occupy (exclusive).
        ///
        /// @pre end_index_exclusive <= GetSegmentCount()
        /// @pre start_index_inclusive <= end_index_exclusive
        DOCK_ALLOC_FORCE_INLINE void Occupy(const size_t start_index_inclusive,
                                            const size_t end_index_exclusive) noexcept
        {
            DCHECK_LE(end_index_exclusive, number_of_segments_) << "End must not exceed number of segments";
            DCHECK_LE(start_index_inclusive, end_index_exclusive) << "Start must be less than end";

            if (number_of_segments_ == 0 || start_index_inclusive == end_index_exclusive) [[unlikely]]
            {
                return;
            }

            RangeUpdate(start_index_inclusive, end_index_exclusive, LazyState::Occupied);
        }

        /// @brief Marks a specified range of segments as free.
        ///
        /// This is an efficient O(log N) operation due to lazy propagation.
        ///
        /// @param start_index_inclusive The starting index of the range to free (inclusive).
        /// @param end_index_exclusive The ending index of the range to free (exclusive).
        ///
        /// @pre end_index_exclusive <= GetSegmentCount()
        /// @pre start_index_inclusive <= end_index_exclusive
        DOCK_ALLOC_FORCE_INLINE void Free(const size_t start_index_inclusive, const size_t end_index_exclusive) noexcept
        {
            DCHECK_LE(end_index_exclusive, number_of_segments_) << "End must not exceed number of segments";
            DCHECK_LE(start_index_inclusive, end_index_exclusive) << "Start must be less than end";

            if (number_of_segments_ == 0 || start_index_inclusive == end_index_exclusive) [[unlikely]]
            {
                return;
            }

            RangeUpdate(start_index_inclusive, end_index_exclusive, LazyState::Free);
        }

        /// @brief Checks if a specified range of segments is entirely occupied.
        ///
        /// This is an efficient O(log N) operation due to lazy propagation.
        ///
        /// @param start_index_inclusive The starting index of the range to check (inclusive).
        /// @param end_index_exclusive The ending index of the range to check (exclusive).
        ///
        /// @pre end_index_exclusive <= GetSegmentCount()
        ///
        /// @return \c true if every segment in the range is occupied, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool IsRangeOccupied(const size_t start_index_inclusive,
                                                                   const size_t end_index_exclusive) const noexcept
        {
            DCHECK_LE(end_index_exclusive, number_of_segments_) << "End must not exceed number of segments";
            DCHECK_LE(start_index_inclusive, end_index_exclusive) << "Start must be less than end";

            if (number_of_segments_ == 0) [[unlikely]]
            {
                return false;
            }

            if (start_index_inclusive == end_index_exclusive) [[unlikely]]
            {
                return false;
            }

            auto queried_range_node = RangeQuery(start_index_inclusive, end_index_exclusive);
            return queried_range_node.length_of_maximum_free_gap == 0;
        }

        /// @brief Checks if a specified range of segments is entirely free.
        ///
        /// This is an efficient O(log N) operation due to lazy propagation.
        ///
        /// @param start_index_inclusive The starting index of the range to check (inclusive).
        /// @param end_index_exclusive The ending index of the range to check (exclusive).
        ///
        /// @pre end_index_exclusive <= GetSegmentCount()
        /// @pre start_index_inclusive <= end_index_exclusive
        ///
        /// @return \c true if every segment in the range is free, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool IsRangeFree(
            const size_t start_index_inclusive, const size_t end_index_exclusive) const noexcept
        {
            DCHECK_LE(end_index_exclusive, number_of_segments_) << "End must not exceed number of segments";
            DCHECK_LE(start_index_inclusive, end_index_exclusive) << "Start must be less than end";

            if (number_of_segments_ == 0) [[unlikely]]
            {
                return true;
            }

            if (start_index_inclusive == end_index_exclusive) [[unlikely]]
            {
                return true;
            }

            auto queried_range_node = RangeQuery(start_index_inclusive, end_index_exclusive);
            return queried_range_node.length_of_maximum_free_gap == end_index_exclusive - start_index_inclusive;
        }

        /// @brief Finds the first available contiguous block of at least a given length within a specified search range.
        ///
        /// This is an overload that allows specifying the search range explicitly.
        /// This is an efficient O(log N) operation due to lazy propagation.
        ///
        /// @param required_length The minimum required length of the free segment.
        /// @param search_range_start_inclusive The starting index of the search range (inclusive).
        /// @param search_range_end_exclusive The ending index of the search range (exclusive).
        ///
        /// @pre search_range_end_exclusive <= GetSegmentCount()
        /// @pre search_range_start_inclusive <= search_range_end_exclusive
        ///
        /// @return A \c std::optional containing the starting position of the first found free segment of sufficient length.
        /// Returns \c std::nullopt if no such segment is found.
        [[nodiscard]] std::optional<size_t> FindFirstFreeRange(const size_t required_length,
                                                               const size_t search_range_start_inclusive,
                                                               const size_t search_range_end_exclusive)
        const noexcept
        {
            auto first_found_it = BeginFreeRanges(required_length, search_range_start_inclusive,
                                                  search_range_end_exclusive);
            if (first_found_it != EndFreeRanges())
            {
                return *first_found_it;
            }
            return std::nullopt;
        }

        /// @brief Finds the first available contiguous block of at least a given length anywhere on the interval tree.
        /// This is an overload that searches the entire tree without a specified range.
        ///
        /// This is an efficient O(log N) operation due to lazy propagation.
        ///
        /// @param required_length The minimum required length of the free segment.
        ///
        /// @return A \c std::optional containing the starting position of the first found free segment.
        /// Returns \c std::nullopt if no such segment is found.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE std::optional<size_t> FindFirstFreeRange(
            const size_t required_length) const noexcept
        {
            return FindFirstFreeRange(required_length, 0, number_of_segments_);
        }

        /// @brief Compares this segment tree with another for equality.
        ///
        /// Two trees are considered equal if they manage the same number of segments and their
        /// occupancy states are identical. The comparison is optimized: it traverses both trees,
        /// pruning branches where states are provably identical (e.g., both subtrees are
        /// fully occupied or fully free), which is significantly faster than a naive
        /// element-by-element comparison of the underlying state.
        /// This runs in O(N) time, where N is the number of segments, however, due to pruning,
        /// this is often much faster in practice. Still the worst case is O(N).
        ///
        /// @param other_tree The other \c IntervalGapTree to compare against.
        ///
        /// @return \c true if the trees represent the same state, \c false otherwise.
        bool operator==(const IntervalGapTree& other_tree) const noexcept
        {
            if (this == &other_tree)
            {
                return true;
            }
            if (number_of_segments_ != other_tree.number_of_segments_)
            {
                return false;
            }
            if (number_of_leaf_nodes_ != other_tree.number_of_leaf_nodes_)
            {
                return false;
            }

            equality_check_stack_.clear();
            equality_check_stack_.reserve(tree_height_);
            equality_check_stack_.push({1});

            while (!equality_check_stack_.empty())
            {
                auto current_equal_frame = equality_check_stack_.top();
                equality_check_stack_.pop();
                auto const& this_node = segment_tree_nodes_[current_equal_frame.node_index_to_compare];
                auto const& other_node = other_tree.segment_tree_nodes_[current_equal_frame.node_index_to_compare];

                // If both have the same non-None lazy flag, we know
                // the entire subtree is uniformly Free or Occupied
                // in both trees, so we can prune here:
                if (this_node.lazy_propagation_state != LazyState::None && this_node.lazy_propagation_state ==
                    other_node.lazy_propagation_state)
                {
                    continue;
                }

                // If both subtrees happen to be completely Free or
                // completely Occupied (even with no lazy flag),
                // we can also prune:
                const bool is_this_node_subtree_all_free = (this_node.length_of_maximum_free_gap == this_node.
                    segment_length);
                if (const bool is_other_node_subtree_all_free = (other_node.length_of_maximum_free_gap == other_node.
                    segment_length); is_this_node_subtree_all_free && is_other_node_subtree_all_free)
                {
                    continue;
                }

                const bool is_this_node_subtree_all_occupied = (this_node.length_of_maximum_free_gap == 0);
                if (const bool is_other_node_subtree_all_occupied = (other_node.length_of_maximum_free_gap == 0);
                    is_this_node_subtree_all_occupied && is_other_node_subtree_all_occupied)
                {
                    continue;
                }

                // Otherwise require exact match on the *aggregates* only:
                if (this_node.length_of_longest_free_prefix != other_node.length_of_longest_free_prefix ||
                    this_node.length_of_longest_free_suffix != other_node.length_of_longest_free_suffix ||
                    this_node.length_of_maximum_free_gap != other_node.length_of_maximum_free_gap ||
                    this_node.segment_length != other_node.segment_length)
                {
                    return false;
                }

                // If not a leaf, descend into children:
                if (current_equal_frame.node_index_to_compare < number_of_leaf_nodes_)
                {
                    equality_check_stack_.push({current_equal_frame.node_index_to_compare * 2 + 1});
                    equality_check_stack_.push({current_equal_frame.node_index_to_compare * 2});
                }
            }

            return true;
        }

        /// @brief Compares this segment tree with another for inequality.
        ///
        /// This runs in O(N) time, where N is the number of segments, however, due to pruning,
        /// this is often much faster in practice. Still the worst case is O(N).
        ///
        /// @param other_tree The other \c IntervalGapTree to compare against.
        ///
        /// @return \c true if the trees represent different states, \c false otherwise.
        DOCK_ALLOC_FORCE_INLINE bool operator!=(const IntervalGapTree& other_tree) const noexcept
        {
            return !(*this == other_tree);
        }

    private:
        /// @brief Merges two adjacent node states into a new parent node state.
        ///
        /// This is the core combination logic of the segment tree. It calculates the parent's prefix,
        /// suffix, and max gap based on the children's properties.
        ///
        /// @param left_child_node The left child node.
        /// @param right_child_node The right child node.
        ///
        /// @return A new node representing the merged state.
        static Node Merge(const Node& left_child_node, const Node& right_child_node) noexcept
        {
            Node merged_parent_node;
            merged_parent_node.segment_length = left_child_node.segment_length + right_child_node.segment_length;
            merged_parent_node.length_of_longest_free_prefix = (left_child_node.length_of_longest_free_prefix ==
                                                                   left_child_node.segment_length)
                                                                   ? left_child_node.segment_length + right_child_node.
                                                                   length_of_longest_free_prefix
                                                                   : left_child_node.length_of_longest_free_prefix;
            merged_parent_node.length_of_longest_free_suffix = (right_child_node.length_of_longest_free_suffix ==
                                                                   right_child_node.segment_length)
                                                                   ? right_child_node.segment_length + left_child_node.
                                                                   length_of_longest_free_suffix
                                                                   : right_child_node.length_of_longest_free_suffix;
            merged_parent_node.length_of_maximum_free_gap = std::max({
                left_child_node.length_of_maximum_free_gap, right_child_node.length_of_maximum_free_gap,
                left_child_node.length_of_longest_free_suffix + right_child_node.length_of_longest_free_prefix
            });
            merged_parent_node.lazy_propagation_state = LazyState::None;
            return merged_parent_node;
        }

        /// @brief Performs a query to get the aggregate node data for a given range.
        ///
        /// This is an iterative implementation that traverses the tree from the leaves up to
        /// efficiently aggregate the information for the specified range.
        ///
        /// @param range_start_inclusive The starting index of the query range (inclusive).
        /// @param range_end_exclusive The ending index of the query range (exclusive).
        ///
        /// @return A \c Node object summarizing the state of the queried range.
        Node RangeQuery(size_t range_start_inclusive, size_t range_end_exclusive) const noexcept
        {
            // Handle empty or trivial
            if (range_start_inclusive >= range_end_exclusive || number_of_segments_ == 0) [[unlikely]]
            {
                // For an empty or invalid range, the length and all gap metrics are 0.
                return Node{0, 0, 0, 0, LazyState::None};
            }

            // Shift to leaves
            range_start_inclusive += number_of_leaf_nodes_;
            range_end_exclusive += number_of_leaf_nodes_;

            // Push pending lazies down to these boundaries
            for (size_t tree_level = tree_height_; tree_level > 0; --tree_level)
            {
                const size_t left_boundary_ancestor_index = range_start_inclusive >> tree_level;
                const size_t right_boundary_ancestor_index = (range_end_exclusive - 1) >> tree_level;

                if (left_boundary_ancestor_index > 0)
                {
                    Push(left_boundary_ancestor_index);
                }

                if (right_boundary_ancestor_index > 0 && right_boundary_ancestor_index != left_boundary_ancestor_index)
                {
                    Push(right_boundary_ancestor_index);
                }
            }

            // Sweep from both ends
            Node aggregate_node_left{0, 0, 0, 0, LazyState::None};
            Node aggregate_node_right{0, 0, 0, 0, LazyState::None};
            while (range_start_inclusive < range_end_exclusive)
            {
                if (range_start_inclusive & static_cast<size_t>(1))
                {
                    aggregate_node_left = Merge(aggregate_node_left, segment_tree_nodes_[range_start_inclusive++]);
                }
                if (range_end_exclusive & static_cast<size_t>(1))
                {
                    aggregate_node_right = Merge(segment_tree_nodes_[--range_end_exclusive], aggregate_node_right);
                }
                range_start_inclusive >>= 1;
                range_end_exclusive >>= 1;
            }

            // Final merge
            return Merge(aggregate_node_left, aggregate_node_right);
        }

        /// @brief Applies a lazy state to a specific node.
        ///
        /// This updates the node's aggregate values (\c length_of_maximum_free_gap, etc.) according to the new
        /// state (\c Free or \c Occupied) and sets its \c lazy_propagation_state flag.
        ///
        /// @param node_index The index of the node in the tree array.
        /// @param lazy_state_to_apply The lazy state to apply.
        void Apply(const size_t node_index, const LazyState lazy_state_to_apply) const noexcept
        {
            auto& target_node = segment_tree_nodes_[node_index];
            target_node.lazy_propagation_state = lazy_state_to_apply;
            if (lazy_state_to_apply == LazyState::Free)
            {
                auto node_segment_length = target_node.segment_length;
                target_node.length_of_longest_free_prefix = node_segment_length;
                target_node.length_of_longest_free_suffix = node_segment_length;
                target_node.length_of_maximum_free_gap = node_segment_length;
            }
            else
            {
                target_node.length_of_longest_free_prefix = 0;
                target_node.length_of_longest_free_suffix = 0;
                target_node.length_of_maximum_free_gap = 0;
            }
        }

        /// @brief Pushes a pending lazy update from a parent node down to its children.
        ///
        /// Before operating on a node's children, this function must be called to ensure their
        /// state is up-to-date. It applies the parent's lazy flag to the children and then
        /// clears the parent's flag.
        ///
        /// @param parent_node_index The index of the parent node whose lazy state needs to be pushed down.
        void Push(const size_t parent_node_index) const noexcept
        {
            auto parent_lazy_state = segment_tree_nodes_[parent_node_index].lazy_propagation_state;
            if (parent_lazy_state == LazyState::None)
            {
                return;
            }
            Apply(parent_node_index << 1, parent_lazy_state);
            Apply(parent_node_index << 1 | 1, parent_lazy_state);
            segment_tree_nodes_[parent_node_index].lazy_propagation_state = LazyState::None;
        }

        /// @brief Updates a parent node's state by merging its children's states.
        ///
        /// This is used after an update operation to propagate changes back up the tree. It
        /// re-calculates the parent's aggregate values based on its now up-to-date children.
        /// This is the inverse of \c Push.
        ///
        /// @param parent_node_index The index of the parent node to update.
        void Pull(const size_t parent_node_index) const noexcept
        {
            // Parent node that we’re rebuilding
            auto& parent_node_to_update = segment_tree_nodes_[parent_node_index];

            if (parent_node_to_update.lazy_propagation_state != LazyState::None)
            {
                return;
            }

            // Its two children
            auto& left_child_node = segment_tree_nodes_[parent_node_index << 1];
            auto& right_child_node = segment_tree_nodes_[(parent_node_index << 1) | 1];

            // Total length = sum of children
            parent_node_to_update.segment_length = left_child_node.segment_length + right_child_node.segment_length;

            // Longest free prefix:
            // if the entire left_child_node is free, extend with right_child_node’s prefix
            parent_node_to_update.length_of_longest_free_prefix = (left_child_node.length_of_longest_free_prefix ==
                                                                      left_child_node.segment_length)
                                                                      ? (left_child_node.segment_length +
                                                                          right_child_node.
                                                                          length_of_longest_free_prefix)
                                                                      : left_child_node.length_of_longest_free_prefix;

            // Longest free suffix:
            // if the entire right_child_node is free, extend with left_child_node’s suffix
            parent_node_to_update.length_of_longest_free_suffix = (right_child_node.length_of_longest_free_suffix ==
                                                                      right_child_node.segment_length)
                                                                      ? (right_child_node.segment_length +
                                                                          left_child_node.length_of_longest_free_suffix)
                                                                      : right_child_node.length_of_longest_free_suffix;

            // Max gap is the best of:
            // – left_child_node.length_of_maximum_free_gap
            // – right_child_node.length_of_maximum_free_gap
            // – a gap straddling the two children
            parent_node_to_update.length_of_maximum_free_gap = std::max({
                left_child_node.length_of_maximum_free_gap, right_child_node.length_of_maximum_free_gap,
                left_child_node.length_of_longest_free_suffix + right_child_node.length_of_longest_free_prefix
            });
        }

        /// @brief The internal implementation for marking a range as free or occupied.
        ///
        /// It uses lazy propagation. It first pushes down any pending updates along the path to
        /// the update range, then applies the new state to the relevant nodes, and finally pulls
        /// the changes back up the tree to ensure consistency.
        ///
        /// @param range_start_inclusive The starting index of the update range (inclusive).
        /// @param range_end_exclusive The ending index of the update range (exclusive).
        /// @param new_lazy_state The new state (\c LazyState::Free or \c LazyState::Occupied) to apply.
        void RangeUpdate(size_t range_start_inclusive, size_t range_end_exclusive,
                         const LazyState new_lazy_state) noexcept
        {
            if (range_start_inclusive >= range_end_exclusive || number_of_segments_ == 0) [[unlikely]]
            {
                return; // empty range, nothing to do
            }

            // shift to leaves
            range_start_inclusive += number_of_leaf_nodes_;
            range_end_exclusive += number_of_leaf_nodes_;
            const size_t initial_left_leaf_index = range_start_inclusive;
            const size_t initial_right_leaf_index = range_end_exclusive;

            // push all ancestors
            for (size_t tree_level = tree_height_; tree_level > 0; --tree_level)
            {
                const size_t left_boundary_ancestor_index = range_start_inclusive >> tree_level;
                const size_t right_boundary_ancestor_index = (range_end_exclusive - 1) >> tree_level;

                if (left_boundary_ancestor_index > 0)
                {
                    Push(left_boundary_ancestor_index);
                }

                if (right_boundary_ancestor_index > 0 && right_boundary_ancestor_index != left_boundary_ancestor_index)
                {
                    Push(right_boundary_ancestor_index);
                }
            }

            // cover segments
            while (range_start_inclusive < range_end_exclusive)
            {
                if (range_start_inclusive & static_cast<size_t>(1))
                {
                    Apply(range_start_inclusive++, new_lazy_state);
                }
                if (range_end_exclusive & static_cast<size_t>(1))
                {
                    Apply(--range_end_exclusive, new_lazy_state);
                }
                range_start_inclusive >>= 1;
                range_end_exclusive >>= 1;
            }

            // pull back up
            for (size_t tree_level = 1; tree_level <= tree_height_; ++tree_level)
            {
                const size_t left_boundary_ancestor_index = initial_left_leaf_index >> tree_level;
                const size_t right_boundary_ancestor_index = (initial_right_leaf_index - 1) >> tree_level;

                if (left_boundary_ancestor_index > 0)
                {
                    Pull(left_boundary_ancestor_index);
                }
                if (right_boundary_ancestor_index > 0 && right_boundary_ancestor_index != left_boundary_ancestor_index)
                {
                    Pull(right_boundary_ancestor_index);
                }
            }
        }

        size_t number_of_segments_{0};
        size_t number_of_leaf_nodes_{0};
        size_t tree_height_{0};
        mutable std::vector<Node> segment_tree_nodes_{};

        // We rely on explicit descent for the search and equality comparison,
        // so we need to keep these stacks around.
        // They are allocated only once and reused for each call,
        // so they should not be a performance concern.
        // We avoid recursion to prevent stack overflow and increase performance,
        // by having complete control over the stack frames.
        mutable core::reservable_stack<EqualFrame, absl::InlinedVector<EqualFrame, ExpectedMaxTreeHeight>>
        equality_check_stack_{};
    };
}

#endif
