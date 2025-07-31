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

#ifndef DOCK_ALLOC_SOLVER_CONTAINER_BERTH_OCCUPANCY_H_
#define DOCK_ALLOC_SOLVER_CONTAINER_BERTH_OCCUPANCY_H_

#include <vector>
#include <optional>
#include <algorithm>
#include <bit> // For std::bit_ceil, std::bit_width (C++20)

#include "absl/log/check.h"
#include "dockalloc/core/miscellaneous/core_defines.h"
#include "dockalloc/core/container/interval.h"
#include "dockalloc/solver/container/bit_vector.h"

namespace dockalloc::solver
{
    /// @brief A node in the berth occupancy tree, representing the state of all space segments over a specific time interval.
    ///
    /// This class serves as the fundamental building block for the `BerthOccupancy` segment tree. Each node
    /// tracks berth availability using two \c BitVector masks: a \c free_mask that represents the actual
    /// combined availability of its children, and a \c pending_mask used for lazy propagation of updates.
    /// A \c dirty flag indicates that the node has a pending update that has not yet been pushed to its children.
    ///
    /// @tparam WordType The unsigned integral type used by the underlying `BitVector` for its storage words.
    template <typename WordType>
        requires std::unsigned_integral<WordType>
    class BerthOccupancyNode
    {
    public:
        /// @brief Constructs a BerthOccupancyNode for a given number of space segments.
        ///
        /// This constructor initializes the node with bit vectors of the specified size,
        /// where each bit corresponds to a space segment. The bit vectors are initialized
        /// with all bits set to \c true`, indicating that all segments are initially free.
        ///
        /// @param slots The number of space segments to track, which determines the size of the bit vectors.
        explicit DOCK_ALLOC_FORCE_INLINE BerthOccupancyNode(const size_t slots)
            : free_mask_(slots, true),
              pending_mask_(slots, true),
              dirty_(false)
        {
        }

        /// @brief Checks if the node has a pending update that has not been propagated to its children.
        ///
        /// A "dirty" node holds a lazy update in its `pending_mask`. This state must be pushed down
        /// to its children before their states can be accurately queried or updated.
        ///
        /// @return `true` if the node is dirty, `false` otherwise.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE bool IsDirty() const noexcept
        {
            return dirty_;
        }

        /// @brief Sets the dirty state of the node.
        ///
        /// This is typically called when a lazy update is applied directly to this node.
        ///
        /// @param dirty The new dirty state to set.
        constexpr DOCK_ALLOC_FORCE_INLINE void SetDirty(const bool dirty) noexcept
        {
            dirty_ = dirty;
        }

        /// @brief Provides mutable access to the free mask.
        ///
        /// The \c free_mask` represents the true, combined availability of all time intervals covered by this node
        /// and its descendants. A bit is \c 1 (true) if the corresponding space segment is free.
        ///
        /// @return A mutable reference to the \c free_mask bit vector.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE BitVector<WordType>& GetFreeMask() noexcept
        {
            return free_mask_;
        }

        /// @brief Provides const access to the free mask.
        ///
        /// The \c free_mask` represents the true, combined availability of all time intervals covered by this node
        /// and its descendants. A bit is \c 1 (true) if the corresponding space segment is free.
        ///
        /// @return A const reference to the `free_mask` bit vector.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE const BitVector<WordType>& GetFreeMask() const noexcept
        {
            return free_mask_;
        }

        /// @brief Provides mutable access to the pending mask.
        ///
        /// The \c pending_mask stores a lazy update that applies to this node and all of its descendants.
        ///
        /// @return A mutable reference to the \c pending_mask bit vector.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE BitVector<WordType>& GetPendingMask() noexcept
        {
            return pending_mask_;
        }

        /// @brief Provides const access to the pending mask.
        ///
        /// The \c pending_mask stores a lazy update that applies to this node and all of its descendants.
        ///
        /// @return A const reference to the `pending_mask` bit vector.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE const BitVector<WordType>& GetPendingMask() const noexcept
        {
            return pending_mask_;
        }

    private:
        BitVector<WordType> free_mask_;
        BitVector<WordType> pending_mask_;
        bool dirty_;
    };

    /// @brief Manages 2D berth occupancy using a segment tree over a compressed time dimension.
    ///
    /// This class provides a highly efficient way to query and update berth availability across continuous
    /// time and space. It works by first compressing the time dimension into a discrete set of non-overlapping
    /// intervals defined by the start and end points of all operations. A segment tree with lazy propagation
    /// is built on top of these time intervals, allowing for range-based queries and updates in O(log T) time,
    /// where T is the number of unique time points.
    ///
    /// For the space dimension, each node in the segment tree contains a \c BitVector, where each bit corresponds
    /// to a compressed space segment. This allows for hardware-accelerated (SIMD) operations on all space
    /// segments simultaneously, making queries exceptionally fast.
    ///
    /// @tparam TimeType Unsigned integral type for time.
    /// @tparam PositionType Unsigned integral type for position.
    /// @tparam WordType Unsigned integral type for the `BitVector` words.
    template <typename TimeType, typename PositionType, typename WordType>
        requires std::unsigned_integral<TimeType> &&
        std::unsigned_integral<PositionType> &&
        std::unsigned_integral<WordType>
    class BerthOccupancy
    {
    public:
        using TimeInterval = core::Interval<TimeType>;
        using SpaceInterval = core::Interval<PositionType>;

        /// @brief Constructs the \c BerthOccupancy data structure from a set of time and position points.
        ///
        /// The constructor takes vectors of all unique time and position points that define the boundaries
        /// of all possible occupancy intervals. It sorts and uniques these points to create a compressed
        /// grid, then builds a segment tree structure to manage it.
        ///
        /// @param times A vector of time points (e.g., start and end times of bookings).
        /// @param positions A vector of position points (e.g., start and end locations of berths).
        explicit BerthOccupancy(std::vector<TimeType> times, std::vector<PositionType> positions) noexcept
            : times_(std::move(times)),
              positions_(std::move(positions))
        {
            // Sort and remove duplicates to define the compressed time/space axes.
            std::sort(times_.begin(), times_.end());
            times_.erase(std::unique(times_.begin(), times_.end()), times_.end());
            std::sort(positions_.begin(), positions_.end());
            positions_.erase(std::unique(positions_.begin(), positions_.end()), positions_.end());

            // The number of intervals is one less than the number of points.
            num_leaves_ = times_.empty() ? 0 : times_.size() - 1;
            num_segments_ = positions_.empty() ? 0 : positions_.size() - 1;

            // Calculate the segment tree size, rounding up to the next power of two.
            if (num_leaves_ > 0)
            {
                tree_size_ = std::bit_ceil(num_leaves_);
            }
            tree_height_ = (tree_size_ > 1) ? (std::bit_width(tree_size_ - 1)) : 0;
            nodes_.resize(2 * tree_size_, BerthOccupancyNode<WordType>(num_segments_));
            if (times_.size() >= 2)
            {
                domain_time_ = TimeInterval(times_.front(), times_.back());
            }
            if (positions_.size() >= 2)
            {
                domain_space_ = SpaceInterval(positions_.front(), positions_.back());
            }
        }

        /// @brief Checks if a given time-space rectangle is completely free.
        ///
        /// This is the primary query operation. It performs a highly optimized check by traversing the
        /// segment tree to cover the time range and, at each relevant node, using a SIMD-accelerated
        /// bitmask check to validate the space range. The function returns \c false as soon as the
        /// first occupied slot is found (early exit).
        ///
        /// @param time_iv The continuous time interval to check.
        /// @param space_iv The continuous space interval to check.
        ///
        /// @return \c true if every part of the specified rectangle is available, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool IsFree(const TimeInterval time_iv,
                                                          const SpaceInterval space_iv) noexcept
        {
            if (time_iv.IsEmpty() || space_iv.IsEmpty() || times_.size() < 2 || positions_.size() < 2)
            {
                return true;
            }

            auto valid_time = time_iv.Intersection(domain_time_);
            auto valid_space = space_iv.Intersection(domain_space_);
            if (!valid_time || !valid_space)
            {
                return true;
            }

            auto leaf_iv = CalcLeafRange(*valid_time);
            if (!leaf_iv)
            {
                return true;
            }
            auto seg_iv = CalcSegmentRange(*valid_space);
            if (!seg_iv)
            {
                return true;
            }

            const size_t leaf_l = leaf_iv->GetStart();
            const size_t leaf_r = leaf_iv->GetEnd() - 1;
            const size_t seg_l = seg_iv->GetStart();
            const size_t seg_r = seg_iv->GetEnd();

            size_t l = leaf_l + tree_size_;
            size_t r = leaf_r + tree_size_ + 1;

            for (size_t h = tree_height_; h > 0; --h)
            {
                PushDown(l >> h);
                PushDown((r - 1) >> h);
            }

            for (; l < r; l >>= 1, r >>= 1)
            {
                if (l & 1)
                {
                    if (!nodes_[l++].GetFreeMask().AreBitsSet(seg_l, seg_r))
                    {
                        return false;
                    }
                }
                if (r & 1)
                {
                    if (!nodes_[--r].GetFreeMask().AreBitsSet(seg_l, seg_r))
                    {
                        return false;
                    }
                }
            }

            return true;
        }

        /// @brief Checks if any part of a given time-space rectangle is occupied.
        ///
        /// @param time_iv The continuous time interval to check.
        /// @param space_iv The continuous space interval to check.
        ///
        /// @return \c true if any part of the specified rectangle is occupied, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool IsOccupied(const TimeInterval time_iv,
                                                              const SpaceInterval space_iv) noexcept
        {
            return !IsFree(time_iv, space_iv);
        }

        /// @brief Marks a time-space rectangle as occupied.
        ///
        /// @param time_iv The continuous time interval to mark.
        /// @param space_iv The continuous space interval to mark.
        void MarkOccupied(const TimeInterval time_iv, const SpaceInterval space_iv) noexcept
        {
            if (time_iv.IsEmpty() || space_iv.IsEmpty() || times_.size() < 2 || positions_.size() < 2)
            {
                return;
            }

            auto valid_time = time_iv.Intersection(domain_time_);
            auto valid_space = space_iv.Intersection(domain_space_);
            if (!valid_time || !valid_space)
            {
                return;
            }

            auto leaf_iv = CalcLeafRange(*valid_time);
            if (!leaf_iv)
            {
                return;
            }
            auto seg_iv = CalcSegmentRange(*valid_space);
            if (!seg_iv)
            {
                return;
            }

            UpdateRange(leaf_iv->GetStart(), leaf_iv->GetEnd() - 1, seg_iv->GetStart(), seg_iv->GetEnd(),
                        &BerthOccupancy::ApplyOccupied);
        }

        /// @brief Marks a time-space rectangle as free.
        ///
        /// @param time_iv The continuous time interval to mark.
        /// @param space_iv The continuous space interval to mark.
        void MarkFree(const TimeInterval time_iv, const SpaceInterval space_iv) noexcept
        {
            if (time_iv.IsEmpty() || space_iv.IsEmpty() || times_.size() < 2 || positions_.size() < 2)
            {
                return;
            }

            auto valid_time = time_iv.Intersection(domain_time_);
            auto valid_space = space_iv.Intersection(domain_space_);
            if (!valid_time || !valid_space)
            {
                return;
            }

            auto leaf_iv = CalcLeafRange(*valid_time);
            if (!leaf_iv)
            {
                return;
            }
            auto seg_iv = CalcSegmentRange(*valid_space);
            if (!seg_iv)
            {
                return;
            }

            UpdateRange(leaf_iv->GetStart(), leaf_iv->GetEnd() - 1, seg_iv->GetStart(), seg_iv->GetEnd(),
                        &BerthOccupancy::ApplyFree);
        }

        /// @brief Provides const access to the unique, sorted time points.
        [[nodiscard]] const auto& times() const noexcept { return times_; }

        /// @brief Provides const access to the unique, sorted position points.
        [[nodiscard]] const auto& positions() const noexcept { return positions_; }

    private:
        /// @brief Propagates a lazy update from a parent node to its direct children.
        ///
        /// This is the core of the lazy propagation mechanism. If a node is "dirty", its pending mask
        /// is applied to its children, marking them as dirty in turn. The parent's pending mask is then
        /// reset, and it is marked as clean.
        ///
        /// @param k The index of the parent node in the `nodes_` array.
        void PushDown(size_t k) noexcept
        {
            [[unlikely]] if (auto& nd = nodes_[k]; nd.IsDirty())
            {
                const auto& pm = nd.GetPendingMask();
                for (size_t c : {2 * k, 2 * k + 1})
                {
                    if (c >= nodes_.size()) continue;
                    nodes_[c].GetFreeMask() &= pm;
                    nodes_[c].GetPendingMask() &= pm;
                    nodes_[c].SetDirty(true);
                }
                nd.GetPendingMask().SetAll(true);
                nd.SetDirty(false);
            }
        }

        /// @brief Updates a parent node's state by combining the states of its children.
        ///
        /// After updates are applied to lower levels of the tree, this function is called to "pull up"
        /// the changes, ensuring that parent nodes accurately summarize the state of their descendants.
        /// A parent's free/pending state is the bitwise AND of its children's states.
        ///
        /// @note This operation is skipped if the parent node is dirty, as its state is defined by its
        ///       pending mask, not its children.
        /// @param k The index of the parent node to update.
        void PullUp(size_t k) noexcept
        {
            if (k == 0 || k >= tree_size_)
            {
                return;
            }
            if (nodes_[k].IsDirty()) [[unlikely]]
            {
                return;
            }

            const auto& child1 = nodes_[2 * k];
            const auto& child2 = nodes_[2 * k + 1];

            auto& nd = nodes_[k];
            nd.GetFreeMask() &= child1.GetFreeMask();
            nd.GetFreeMask() &= child2.GetFreeMask();
            nd.GetPendingMask() &= child1.GetPendingMask();
            nd.GetPendingMask() &= child2.GetPendingMask();
        }


        /// @brief A generic, templated function to update a range of leaf and segment indices.
        ///
        /// This function implements the iterative, bottom-up segment tree update algorithm, factoring
        /// out the common traversal logic from `OccupyRange` and `FreeRange`. The iterative approach
        /// implicitly finds the highest-level nodes that cover the requested range, ensuring full-coverage
        /// updates are efficient.
        ///
        /// @tparam ApplyFunc The type of the function to apply to each node in the range.
        /// @param leaf_l The starting leaf index (inclusive).
        /// @param leaf_r The ending leaf index (inclusive).
        /// @param seg_l The starting segment index (inclusive).
        /// @param seg_r The ending segment index (exclusive).
        /// @param apply_func A member function pointer (`&BerthOccupancy::Apply...`) to be called on each node.
        template <typename ApplyFunc>
        void UpdateRange(const size_t leaf_l, const size_t leaf_r, const size_t seg_l, const size_t seg_r,
                         ApplyFunc apply_func) noexcept
        {
            const size_t l0 = leaf_l + tree_size_;
            const size_t r0 = leaf_r + tree_size_;

            for (size_t h = tree_height_; h > 0; --h)
            {
                PushDown(l0 >> h);
                PushDown(r0 >> h);
            }

            for (size_t l = l0, r = r0 + 1; l < r; l >>= 1, r >>= 1)
            {
                if (l & 1)
                {
                    (this->*apply_func)(l++, seg_l, seg_r);
                }
                if (r & 1)
                {
                    (this->*apply_func)(--r, seg_l, seg_r);
                }
            }

            for (size_t h = 1; h <= tree_height_; ++h)
            {
                PullUp(l0 >> h);
                PullUp(r0 >> h);
            }
        }

        /// @brief Converts a continuous time interval into a discrete, half-open range of leaf indices.
        ///
        /// @param iv The continuous time interval.
        ///
        /// @return An optional \c Interval of leaf indices, or \c std::nullopt if the range is invalid.
        std::optional<core::Interval<size_t>> CalcLeafRange(const TimeInterval& iv) const noexcept
        {
            auto it_l = std::lower_bound(times_.begin(), times_.end(), iv.GetStart());
            auto it_r = std::lower_bound(times_.begin(), times_.end(), iv.GetEnd());
            if (it_l >= it_r)
            {
                return std::nullopt;
            }
            const size_t l = std::distance(times_.begin(), it_l);
            const size_t r = std::distance(times_.begin(), it_r);
            return core::Interval(l, r);
        }

        /// @brief Converts a continuous space interval into a discrete, half-open range of segment indices.
        ///
        /// @param iv The continuous space interval.
        ///
        /// @return An optional \c Interval` of segment indices, or \c std::nullopt if the range is invalid.
        std::optional<core::Interval<size_t>> CalcSegmentRange(const SpaceInterval& iv) const noexcept
        {
            auto jt_l = std::lower_bound(positions_.begin(), positions_.end(), iv.GetStart());
            auto jt_r = std::lower_bound(positions_.begin(), positions_.end(), iv.GetEnd());
            if (jt_l >= jt_r)
            {
                return std::nullopt;
            }
            const size_t l = std::distance(positions_.begin(), jt_l);
            const size_t r = std::distance(positions_.begin(), jt_r);
            return core::Interval(l, r);
        }

        /// @brief Applies a "free" operation to a single node's bitmasks.
        ///
        /// @param node_index The index of the node to modify.
        /// @param s0 The starting segment index (inclusive).
        /// @param s1_excl The ending segment index (exclusive).
        void ApplyFree(const size_t node_index, const size_t s0, const size_t s1_excl) noexcept
        {
            nodes_[node_index].GetFreeMask().SetBits(s0, s1_excl);
            nodes_[node_index].GetPendingMask().SetBits(s0, s1_excl);
            nodes_[node_index].SetDirty(true);
        }

        /// @brief Applies an "occupied" operation to a single node's bitmasks.
        ///
        /// @param k The index of the node to modify.
        /// @param s0 The starting segment index (inclusive).
        /// @param s1_excl The ending segment index (exclusive).
        void ApplyOccupied(const size_t k, const size_t s0, const size_t s1_excl) noexcept
        {
            nodes_[k].GetFreeMask().ClearBits(s0, s1_excl);
            nodes_[k].GetPendingMask().ClearBits(s0, s1_excl);
            nodes_[k].SetDirty(true);
        }

        std::vector<TimeType> times_;
        std::vector<PositionType> positions_;
        size_t num_leaves_;
        size_t num_segments_;
        size_t tree_size_ = 1;
        size_t tree_height_ = 0;
        std::vector<BerthOccupancyNode<WordType>> nodes_;
        TimeInterval domain_time_ = TimeInterval(0, 0);
        SpaceInterval domain_space_ = SpaceInterval(0, 0);
    };
}

#endif
