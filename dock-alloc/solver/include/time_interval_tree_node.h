// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_
#define DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_

#include <concepts>
#include "absl/log/check.h"
#include "dockalloc/core/type_traits/smallest_unsigned_for.h"
#include "dockalloc/core/time/time_interval.h"

namespace dockalloc::solver
{
    /// @brief A single node in a time interval tree structure.
    ///
    /// This class represents one node of a static‐size, packed time interval tree.
    ///
    /// @tparam TimeType An unsigned integral type representing time (e.g., \c uint8_t, \c uint16_t, \c uint32_t, ...).
    /// @tparam NodeBytes The total size of the node in bytes (default is 256).
    /// @tparam AlignBytes The alignment of the node in bytes (default is \c NodeBytes).
    template <typename TimeType, size_t NodeBytes = 256, size_t AlignBytes = NodeBytes>
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

            // We ensure that we have enough space for at least 2 intervals.
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
            /// This value governs the static array size for \c children_.
            static constexpr size_t kMaxChildren = kMaxEntries + 1;
        };

        /// @brief The index type used for entries in this node.
        ///
        /// This type ensures that we can index all entries in the node.
        using IndexType = typename Layout::IndexType;

    public:
        /// @brief Final maximum number of intervals that can fit in this node.
        ///
        /// This value governs the static array size for \c intervals_.
        static constexpr size_t kMaxEntries = Layout::kMaxEntries;

        /// @brief Final number of children pointers (always one more than entries).
        ///
        /// This value governs the static array size for \c children_.
        static constexpr size_t kMaxChildren = Layout::kMaxChildren;

        /// @brief Checks if this node is a leaf node.
        ///
        /// A leaf node has no children, meaning it does not have any subtrees.
        ///
        /// @return \c true if this node is a leaf (no children), \c false otherwise.
        [[nodiscard]] bool IsLeaf() const noexcept
        {
            return children_[start_] == nullptr;
        }

        /// @brief Returns the amount of entries in this node.
        ///
        /// This function returns the number of time intervals stored in this node.
        ///
        /// @return The number of intervals in this node.
        IndexType Size() const noexcept
        {
            return finish_ - start_;
        }

        /// @brief Returns the \c TimeInterval<TimeType> at the given index \p i.
        ///
        /// This function retrieves the time interval at the specified index within this node.
        ///
        /// @param i The index of the interval to retrieve.
        ///
        /// @pre i < Size()
        ///
        /// @return The time interval at index \p i.
        const core::TimeInterval<TimeType>& Interval(IndexType i) const noexcept
        {
            DCHECK_LT(i, Size());

            return intervals_[start_ + i];
        }

        /// @brief Returns the child node at the given index \p i.
        ///
        /// This function retrieves the child node at the specified index within this node.
        ///
        /// @param i The index of the child node to retrieve.
        ///
        /// @pre i <= Size()
        ///
        /// @return The child node at index \p i.
        TimeIntervalTreeNode* Child(IndexType i) const noexcept
        {
            DCHECK_LE(i, Size());

            return children_[i];
        }

    private:
        /// @brief Compares two time intervals for ordering.
        ///
        /// This function compares two time intervals based on their start times,
        /// and if those are equal, by their end times.
        ///
        /// @param left The first time interval to compare.
        /// @param right The second time interval to compare.
        ///
        /// @return \c true if \p left is less than \p right, \c false otherwise.
        static constexpr bool Less(const core::TimeInterval<TimeType>& left,
                                   const core::TimeInterval<TimeType>& right) noexcept
        {
            if (left.start() < right.start())
            {
                return true;
            }
            if (left.start() > right.start())
            {
                return false;
            }
            return left.end() < right.end();
        }

        TimeType min_start_time_{0};
        TimeType max_end_time_{0};
        TimeType max_gap_{0};
        IndexType start_{0};
        IndexType finish_{0};
        TimeIntervalTreeNode* parent_{nullptr};
        core::TimeInterval<TimeType> intervals_[kMaxEntries];
        TimeIntervalTreeNode* children_[kMaxChildren]{nullptr};
    };
}

#endif
