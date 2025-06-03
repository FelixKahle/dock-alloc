// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_
#define DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_

#include <concepts>
#include "dockalloc/core/type_traits/smallest_unsigned_for.h"
#include "dockalloc/core/time/time_interval.h"

namespace dockalloc::solver
{
    template <typename TimeType, size_t NodeBytes = 256, size_t AlignBytes = alignof(std::max_align_t)>
        requires std::unsigned_integral<TimeType>
    class alignas(AlignBytes) TimeIntervalTreeNode
    {
        /// @brief Layout of the time interval tree node.
        ///
        /// This struct defines the layout of a time interval tree node, including:
        ///   - The maximum number of entries and child pointers that can fit in the node
        ///   - The size of internal metadata
        ///   - The space taken by intervals and children
        ///
        /// The layout ensures that the entire node fits within the configured `NodeBytes` size
        /// (e.g., 256 bytes), and uses alignment-aware packing to maintain pointer alignment.
        /// It computes an optimal trade-off between metadata overhead and data capacity.
        struct Layout
        {
        private:
            /// @brief Size of a single interval stored in the node.
            ///
            /// Each interval is an instance of \c core::TimeInterval<TimeType>.
            /// The size depends on the template parameter `TimeType`.
            static constexpr size_t kIntervalBytes = sizeof(core::TimeInterval<TimeType>);

            /// @brief Size of a pointer on this platform.
            ///
            /// Used for both parent pointer and child array entries.
            static constexpr size_t kPtrBytes = sizeof(void*);

            /// @brief Size of fixed metadata fields before considering indexing.
            ///
            /// Includes:
            ///   - \c min_start_time_
            ///   - \c max_end_time_
            ///   - \c max_gap_
            ///   - \c parent_ pointer
            static constexpr size_t kBasicMetaBytes = 3 * sizeof(TimeType) + sizeof(void*);

            /// @brief Aligned overhead for provisional max entry calculation.
            ///
            /// Rounds \c kBasicMetaBytes up to nearest multiple of pointer size.
            /// Used to compute a provisional maximum number of entries to determine \c IndexType.
            static constexpr size_t kProvisionalOverhead =
                ((kBasicMetaBytes + kPtrBytes - 1) / kPtrBytes) * kPtrBytes;

            /// @brief Space left for interval and child arrays (provisional).
            ///
            /// This excludes overhead and one spare pointer.
            static constexpr size_t kProvisionalSpace = NodeBytes - kProvisionalOverhead - kPtrBytes;

            /// @brief Combined size of one interval and one child pointer.
            ///
            /// Each entry consists of an interval and a pointer to the corresponding subtree.
            static constexpr size_t kEntryPlusChildBytes = kIntervalBytes + kPtrBytes;

            /// @brief Provisional max number of intervals (used to define \c IndexType).
            ///
            /// Used early on to determine how many entries we might be able to fit.
            static constexpr size_t kProvisionalMaxEntries = kProvisionalSpace / kEntryPlusChildBytes;

            static_assert(kProvisionalMaxEntries >= 2, "Too little space for even 2 intervals in the node.");

        public:
            /// @brief Minimal unsigned integral type that can index all entries.
            ///
            /// Used for \c start_ and \c finish_ indices. Typically, \c uint8_t , \c uint16_t, etc.
            using IndexType = core::SmallestUnsignedFor_t<kProvisionalMaxEntries>;

        private:
            /// @brief Total metadata size with index fields included.
            ///
            /// Adds two index fields (\c start_ and \c finish_) to the basic metadata.
            static constexpr size_t kMetaBytes = kBasicMetaBytes + 2 * sizeof(IndexType);

            /// @brief Aligned metadata size (rounded up to pointer alignment).
            ///
            /// Ensures that the interval and child arrays begin on a pointer-aligned boundary.
            static constexpr size_t kAlignedOverhead = ((kMetaBytes + kPtrBytes - 1) / kPtrBytes) * kPtrBytes;

            /// @brief Final space available for the arrays after all overhead is reserved.
            ///
            /// Subtracts the aligned metadata and one spare pointer from the node budget.
            static constexpr size_t kSpaceForArrays = NodeBytes - kAlignedOverhead - kPtrBytes;

        public:
            /// @brief Final maximum number of intervals that can fit in this node.
            ///
            /// This value governs the static array size for `intervals_`.
            static constexpr size_t kMaxEntries = kSpaceForArrays / kEntryPlusChildBytes;

            /// @brief Final number of children pointers (always one more than entries).
            ///
            /// This value governs the static array size for `children_`.
            static constexpr size_t kMaxChildren = kMaxEntries + 1;
        };

    public:
        TimeIntervalTreeNode() = default;

    private:
        using IndexType = typename Layout::IndexType;
        TimeType min_start_time_;
        TimeType max_end_time_;
        TimeType max_gap_;
        TimeIntervalTreeNode* parent_;
        core::TimeInterval<TimeType> intervals_[Layout::kMaxEntries];
        TimeIntervalTreeNode* children_[Layout::kMaxChildren];
    };
}

#endif
