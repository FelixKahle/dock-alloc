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

#ifndef DOCK_ALLOC_SOLVER_CONTAINER_QUAY_SEGMENT_TREE_H_
#define DOCK_ALLOC_SOLVER_CONTAINER_QUAY_SEGMENT_TREE_H_

#include <concepts>
#include <optional>
#include <vector>
#include <algorithm>
#include <bit>
#include "dockalloc/core/miscellaneous/core_types.h"

namespace dockalloc::solver
{
    /// @brief A node in the segment tree that represents a segment of the quay.
    ///
    /// This class stores information about the longest free prefix, longest free suffix,
    /// maximum gap of free space, and the length of the segment it represents.
    ///
    /// @tparam PositionType The unsigned integral type for segment positions and lengths.
    template <typename PositionType>
        requires std::unsigned_integral<PositionType>
    class QuaySegmentTreeNode
    {
    public:
        /// @brief Default constructor for the segment tree node.
        ///
        /// Initializes all member variables to zero.
        constexpr DOCK_ALLOC_FORCE_INLINE QuaySegmentTreeNode() noexcept = default;

        /// @brief Constructs a segment tree node with specified properties.
        ///
        /// @param longest_free_prefix The length of the longest free prefix in this segment.
        /// @param longest_free_suffix The length of the longest free suffix in this segment.
        /// @param max_gap The maximum contiguous free space within this segment.
        /// @param length The total length of this segment.
        constexpr DOCK_ALLOC_FORCE_INLINE QuaySegmentTreeNode(const PositionType longest_free_prefix,
                                                              const PositionType longest_free_suffix,
                                                              const PositionType max_gap,
                                                              const PositionType length) noexcept
            : longest_free_prefix_{longest_free_prefix},
              longest_free_suffix_{longest_free_suffix},
              max_gap_{max_gap},
              length_{length}
        {
        }

        /// @brief Returns the longest free prefix of this segment.
        ///
        /// @return The length of the longest free prefix.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE PositionType GetLongestFreePrefix() const noexcept
        {
            return longest_free_prefix_;
        }

        /// @brief Sets the longest free prefix of this segment.
        ///
        /// @param prefix The new length of the longest free prefix.
        constexpr DOCK_ALLOC_FORCE_INLINE void SetLongestFreePrefix(const PositionType prefix) noexcept
        {
            longest_free_prefix_ = prefix;
        }

        /// @brief Returns the longest free suffix of this segment.
        ///
        /// @return The length of the longest free suffix.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE PositionType GetLongestFreeSuffix() const noexcept
        {
            return longest_free_suffix_;
        }

        /// @brief Sets the longest free suffix of this segment.
        ///
        /// @param suffix The new length of the longest free suffix.
        constexpr DOCK_ALLOC_FORCE_INLINE void SetLongestFreeSuffix(const PositionType suffix) noexcept
        {
            longest_free_suffix_ = suffix;
        }

        /// @brief Returns the maximum contiguous free space within this segment.
        ///
        /// @return The maximum gap of free space.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE PositionType GetMaxGap() const noexcept
        {
            return max_gap_;
        }

        /// @brief Sets the maximum contiguous free space within this segment.
        ///
        /// @param gap The new maximum gap of free space.
        constexpr DOCK_ALLOC_FORCE_INLINE void SetMaxGap(const PositionType gap) noexcept
        {
            max_gap_ = gap;
        }

        /// @brief Returns the total length of this segment.
        ///
        /// @return The length of the segment.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE PositionType GetLength() const noexcept
        {
            return length_;
        }

        /// @brief Sets the total length of this segment.
        ///
        /// @param length The new length of the segment.
        constexpr DOCK_ALLOC_FORCE_INLINE void SetLength(const PositionType length) noexcept
        {
            length_ = length;
        }

    private:
        PositionType longest_free_prefix_{};
        PositionType longest_free_suffix_{};
        PositionType max_gap_{};
        PositionType length_{};
    };

    /// @brief Segment tree for managing and querying free space on a quay.
    ///
    /// This class uses a segment tree data structure to maintain the occupancy state of a
    /// one-dimensional space (the quay). Each node in the tree stores the longest free prefix,
    /// longest free suffix, and the maximum free contiguous gap within its range. This allows
    /// for highly efficient range updates, range queries, and, most importantly, finding a
    /// free segment of a required length in logarithmic time.
    ///
    /// @tparam PositionType The unsigned integral type for segment positions and lengths.
    template <typename PositionType>
        requires std::unsigned_integral<PositionType>
    class SegmentTree
    {
    public:
        static constexpr size_t kTreeSizeFactor = 4;

        /// @brief Represents the state for lazy propagation updates.
        enum class LazyState : uint8_t
        {
            None = 255,
            Free = 0,
            Occupied = 1
        };

        /// @brief Constructs a new SegmentTree instance.
        ///
        /// @note The tree is initialized with all segments marked as free.
        ///
        /// @param size The total number of discrete segments the quay is divided into.
        explicit SegmentTree(const PositionType size) noexcept
            : size_{size}
        {
            if (size_ == 0)
            {
                return;
            }
            const size_t leaf_count = std::bit_ceil(static_cast<size_t>(size_));
            const size_t tree_size = 2 * leaf_count;

            tree_.resize(tree_size);
            lazy_.assign(tree_size, LazyState::None);

            Build(1, core::SegmentRange<PositionType>{0, size_});
        }

        /// @brief Marks a given range of segments as occupied.
        ///
        /// @param target_range The range of segments [start, end) to mark as occupied.
        void Occupy(const core::SegmentRange<PositionType>& target_range) noexcept
        {
            Update(1, core::SegmentRange<PositionType>{0, size_}, target_range, LazyState::Occupied);
        }

        /// @brief Marks a given range of segments as free.
        ///
        /// @param target_range The range of segments [start, end) to mark as free.
        void Free(const core::SegmentRange<PositionType>& target_range) noexcept
        {
            Update(1, core::SegmentRange<PositionType>{0, size_}, target_range, LazyState::Free);
        }

        /// @brief Checks if a given range of segments is entirely free.
        ///
        /// @param target_range The range of segments [start, end) to check.
        ///
        /// @return \c true if all specified segments are free, \c false otherwise.
        [[nodiscard]] bool IsRangeFree(const core::SegmentRange<PositionType>& target_range) const noexcept
        {
            const auto node = Query(1, core::SegmentRange<PositionType>{0, size_}, target_range);
            return node.GetMaxGap() == target_range.Length();
        }

        /// @brief Checks if a given range of segments is entirely occupied.
        ///
        /// @param target_range The range of segments [start, end) to check.
        ///
        /// @return \c true if all specified segments are occupied, \c false otherwise.
        [[nodiscard]] bool IsRangeOccupied(const core::SegmentRange<PositionType>& target_range) const noexcept
        {
            const auto node = Query(1, core::SegmentRange<PositionType>{0, size_}, target_range);
            return node.GetMaxGap() == 0;
        }

        /// @brief Finds the starting position of the first free contiguous block of at least size k.
        ///
        /// @param k The minimum required length of the free segment.
        ///
        /// @return A \c std::optional containing the starting position if a suitable segment is found;
        /// \c std::nullopt otherwise.
        [[nodiscard]] std::optional<PositionType> FindFree(const PositionType k) const noexcept
        {
            return FindFree(k, core::SegmentRange<PositionType>{0, size_});
        }

        /// @brief Finds the starting position of the first free contiguous block of at least size k within a
        /// specified search range.
        ///
        /// @param k The minimum required length of the free segment.
        /// @param search_range The range of segments [start, end) to search within.
        ///
        /// @return A std::optional containing the starting position if a suitable segment is found;
        /// \c std::nullopt otherwise.
        [[nodiscard]] std::optional<PositionType> FindFree(const PositionType k,
                                                           const core::SegmentRange<PositionType>& search_range) const
            noexcept
        {
            return FindFreeRangeRec(1, core::SegmentRange<PositionType>{0, size_}, search_range, k);
        }

    private:
        using Node = QuaySegmentTreeNode<PositionType>;

        /// @brief Recursively constructs the segment tree during initialization.
        ///
        /// @param node_index The index of the current node in the segment tree.
        /// @param node_range The range of segments that this node covers.
        void Build(const size_t node_index, const core::SegmentRange<PositionType>& node_range) noexcept
        {
            auto& current = tree_[node_index];
            const auto len = node_range.Length();
            current.SetLength(len);
            if (len == 1)
            {
                current.SetLongestFreePrefix(1);
                current.SetLongestFreeSuffix(1);
                current.SetMaxGap(1);
            }
            else
            {
                const auto mid = node_range.template Midpoint<PositionType>();
                const auto left = core::SegmentRange<PositionType>{node_range.GetStart(), mid};
                const auto right = core::SegmentRange<PositionType>{mid, node_range.GetEnd()};
                Build(node_index << 1, left);
                Build(node_index << 1 | 1, right);
                current = Merge(tree_[node_index << 1], tree_[node_index << 1 | 1]);
            }
        }

        /// @brief Applies a lazy update to a single node and marks it with the lazy state.
        ///
        /// @param node_index The index of the node to update.
        /// @param node_range The range of segments that this node covers.
        /// @param state The lazy state to apply.
        void Apply(const size_t node_index, const core::SegmentRange<PositionType>& node_range,
                   const LazyState state) const noexcept
        {
            auto& current = tree_[node_index];
            const auto len = node_range.Length();
            current.SetLength(len);
            if (state == LazyState::Free)
            {
                current.SetLongestFreePrefix(len);
                current.SetLongestFreeSuffix(len);
                current.SetMaxGap(len);
            }
            else // Occupied
            {
                current.SetLongestFreePrefix(0);
                current.SetLongestFreeSuffix(0);
                current.SetMaxGap(0);
            }
            lazy_[node_index] = state;
        }

        /// @brief Pushes pending lazy updates from a parent node down to its children.
        ///
        /// @param node_index The index of the node to push updates from.
        /// @param node_range The range of segments that this node covers.
        void Push(const size_t node_index, const core::SegmentRange<PositionType>& node_range) const noexcept
        {
            if (lazy_[node_index] == LazyState::None || node_range.Length() == 1)
            {
                return;
            }
            const auto mid = node_range.template Midpoint<PositionType>();
            const auto left = core::SegmentRange<PositionType>{node_range.GetStart(), mid};
            const auto right = core::SegmentRange<PositionType>{mid, node_range.GetEnd()};
            Apply(node_index << 1, left, lazy_[node_index]);
            Apply(node_index << 1 | 1, right, lazy_[node_index]);
            lazy_[node_index] = LazyState::None;
        }

        /// @brief Recursively updates the state of a target range in the tree.
        ///
        /// @param node_index The index of the current node in the segment tree.
        /// @param node_range The range of segments that this node covers.
        /// @param target_range The range of segments to update.
        /// @param state The lazy state to apply to the target range.
        void Update(const size_t node_index, const core::SegmentRange<PositionType>& node_range,
                    const core::SegmentRange<PositionType>& target_range, const LazyState state) noexcept
        {
            if (target_range.IsEmpty())
            {
                return;
            }
            if (node_range == target_range)
            {
                Apply(node_index, node_range, state);
                return;
            }
            Push(node_index, node_range);
            const auto mid = node_range.template Midpoint<PositionType>();
            const auto left = core::SegmentRange<PositionType>{node_range.GetStart(), mid};
            const auto right = core::SegmentRange<PositionType>{mid, node_range.GetEnd()};
            if (auto q = target_range.Intersection(left); q)
            {
                Update(node_index << 1, left, *q, state);
            }
            if (auto q = target_range.Intersection(right); q)
            {
                Update(node_index << 1 | 1, right, *q, state);
            }
            tree_[node_index] = Merge(tree_[node_index << 1], tree_[node_index << 1 | 1]);
        }

        /// @brief Recursively queries the aggregated state of a range in the tree.
        ///
        /// @param node_index The index of the current node in the segment tree.
        /// @param node_range The range of segments that this node covers.
        /// @param query_range The range of segments to query.
        ///
        /// @return The aggregated state of the queried range as a Node.
        Node Query(const size_t node_index, const core::SegmentRange<PositionType>& node_range,
                   const core::SegmentRange<PositionType>& query_range) const noexcept
        {
            if (query_range.IsEmpty())
            {
                return Node(0, 0, 0, 0);
            }
            if (node_range == query_range)
            {
                return tree_[node_index];
            }
            Push(node_index, node_range);
            const auto mid = node_range.template Midpoint<PositionType>();
            const auto left = core::SegmentRange<PositionType>{node_range.GetStart(), mid};
            const auto right = core::SegmentRange<PositionType>{mid, node_range.GetEnd()};
            if (query_range.GetEnd() <= mid)
            {
                return Query(node_index << 1, left, query_range);
            }
            if (query_range.GetStart() >= mid)
            {
                return Query(node_index << 1 | 1, right, query_range);
            }
            const auto ln = Query(node_index << 1, left, {query_range.GetStart(), mid});
            const auto rn = Query(node_index << 1 | 1, right, {mid, query_range.GetEnd()});
            return Merge(ln, rn);
        }

        /// @brief Recursively searches for a free segment of at least length k.
        ///
        /// @param node_index The index of the current node in the segment tree.
        /// @param node_range The range of segments that this node covers.
        /// @param search_range The range of segments to search within.
        /// @param k The minimum required length of the free segment.
        ///
        /// @return A \ cstd::optional containing the starting position of the first free segment of at
        /// least length \c k, or \c std::nullopt if no such segment exists.
        std::optional<PositionType> FindFreeRangeRec(const size_t node_index,
                                                     const core::SegmentRange<PositionType>& node_range,
                                                     const core::SegmentRange<PositionType>& search_range,
                                                     const PositionType k
        ) const noexcept
        {
            // Pruning: if the node's range doesn't intersect the search area or its max free space is too small, stop.
            if (!node_range.Intersects(search_range) || tree_[node_index].GetMaxGap() < k)
            {
                return std::nullopt;
            }

            // Base case: if we are at a leaf node, and it passed the checks, we found a spot.
            if (node_range.Length() == 1)
            {
                return node_range.GetStart();
            }

            // Push down any pending updates before inspecting children.
            Push(node_index, node_range);

            const PositionType mid = node_range.template Midpoint<PositionType>();
            const core::SegmentRange<PositionType> left{node_range.GetStart(), mid};
            const core::SegmentRange<PositionType> right{mid, node_range.GetEnd()};

            // 1. Search in the left child first.
            auto lr = search_range.Intersection(left);
            if (lr)
            {
                if (auto res = FindFreeRangeRec(node_index << 1, left, *lr, k))
                {
                    return res;
                }
            }

            // 2. Check the gap across the midpoint, safely clipped to the search range.
            auto rr = search_range.Intersection(right);

            const PositionType suffix = tree_[node_index << 1].GetLongestFreeSuffix();
            const PositionType effective_suffix = (lr && suffix > 0 && mid > lr->GetStart())
                                                      ? std::min(suffix, mid - lr->GetStart())
                                                      : 0;

            const PositionType prefix = tree_[node_index << 1 | 1].GetLongestFreePrefix();
            const PositionType effective_prefix = (rr && prefix > 0)
                                                      ? std::min(prefix, rr->GetEnd() - mid)
                                                      : 0;

            if (effective_suffix + effective_prefix >= k)
            {
                return mid - effective_suffix;
            }

            // 3. If no other solution is found, search in the right child.
            if (rr)
            {
                return FindFreeRangeRec(node_index << 1 | 1, right, *rr, k);
            }

            return std::nullopt;
        }

        /// @brief Merges the information from two child nodes into a parent node.
        ///
        /// @param left The left child node.
        /// @param right The right child node.
        ///
        /// @return A new Node that represents the merged state of the two child nodes.
        static Node Merge(const Node& left, const Node& right) noexcept
        {
            Node result;
            const PositionType total_len = left.GetLength() + right.GetLength();
            result.SetLength(total_len);

            // A full-free left node extends the prefix of the right node.
            const PositionType prefix = (left.GetLongestFreePrefix() == left.GetLength())
                                            ? left.GetLength() + right.GetLongestFreePrefix()
                                            : left.GetLongestFreePrefix();

            // A full-free right node extends the suffix of the left node.
            const PositionType suffix = (right.GetLongestFreeSuffix() == right.GetLength())
                                            ? right.GetLength() + left.GetLongestFreeSuffix()
                                            : right.GetLongestFreeSuffix();

            // The max gap is the largest of the children's gaps or the new gap formed at the merge point.
            const PositionType gap = std::max({
                left.GetMaxGap(), right.GetMaxGap(), left.GetLongestFreeSuffix() + right.GetLongestFreePrefix()
            });

            result.SetLongestFreePrefix(prefix);
            result.SetLongestFreeSuffix(suffix);
            result.SetMaxGap(gap);
            return result;
        }

        PositionType size_;
        mutable std::vector<Node> tree_;
        mutable std::vector<LazyState> lazy_;
    };
}

#endif
