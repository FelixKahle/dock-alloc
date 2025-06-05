// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_
#define DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_H_

#include <type_traits>
#include "dockalloc/core/type_traits/bigger_alignment.h"
#include "dockalloc/core/type_traits/smallest_unsigned_for.h"
#include "dockalloc/core/time/time_interval.h"

namespace dockalloc::solver
{
    /// Forward declaration of the TimeIntervalTreeNode class.
    ///
    /// This class represents a node in a time-interval tree, which is used to store
    /// time intervals efficiently.
    ///
    /// @tparam TimeType The unsigned integral type used for timestamp fields.
    /// @tparam TargetNodeSize The desired size in bytes of the generated node struct.
    template <typename TimeType, size_t TargetNodeSize>
        requires std::unsigned_integral<TimeType>
    class TimeIntervalTreeNode;

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
    /// @note The \c TimeIntervalTreeNodeLayout does not own any pointers, it only provides
    /// a layout for the node structure. The actual memory management is handled by the caller,
    /// so the caller must ensure that the pointers to parent and children are valid and deallocated.
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
        class LayoutImpl;

        /// @brief The layout of a time-interval tree node, with optimized padding.
        ///
        /// The layout is determined by the \p SLotSize and whether \p TimeType is wider
        /// then the smallest unsigned type that can hold the number of slots.
        ///
        /// @tparam SlotSize the number of slots in the node, must be at least 4.
        template <size_t SlotSize>
            requires (SlotSize >= 4)
        class LayoutImpl<SlotSize, true>
        {
        public:
            /// @brief The slot size in the node.
            ///
            /// This is the number of \c TimeInterval<TimeType> slots in the node.
            static constexpr size_t kSlotSize = SlotSize;

            /// @brief The size of children each node can have.
            ///
            /// This is the number of child pointers in the node, which is one more than the number of slots.
            static constexpr size_t kChildrenSize = SlotSize + 1;

            /// @brief The type of the index used to access children and intervals.
            ///
            /// This is the smallest unsigned type that can hold the number of children in the node.
            using IndexType = core::SmallestUnsignedFor_t<kChildrenSize>;

            using IntervalStorage = std::aligned_storage_t<
                sizeof(core::TimeInterval<TimeType>),
                alignof(core::TimeInterval<TimeType>)
            >;

            /// @brief Default constructor.
            ///
            /// Initializes the layout with default values.
            LayoutImpl() noexcept = default;

            /// @brief Destructor.
            ///
            /// Cleans up the layout, but does not delete any pointers.
            ~LayoutImpl() noexcept = default;


            // Delete copy and assignment operators to prevent copying.

            LayoutImpl(const LayoutImpl&) noexcept = delete;
            LayoutImpl& operator=(const LayoutImpl&) noexcept = delete;

            /// @brief Returns a pointer to the parent node.
            ///
            /// This function returns a pointer to the parent node of this node.
            ///
            /// @return A pointer to the parent node, or \c nullptr if there is no parent.
            [[nodiscard]] TimeIntervalTreeNode<TimeType, TargetNodeSize>* GetParent() const noexcept
            {
                return parent_;
            }

            /// @brief Returns the minimum start time of the intervals in this node.
            ///
            /// This function returns the minimum start time of all intervals stored in this node.
            ///
            /// @return The minimum start time of the intervals in this node.
            [[nodiscard]] TimeType GetMinStartTime() const noexcept
            {
                return min_start_time_;
            }

            /// @brief Returns the maximum end time of the intervals in this node.
            ///
            /// This function returns the maximum end time of all intervals stored in this node.
            ///
            /// @return The maximum end time of the intervals in this node.
            [[nodiscard]] TimeType GetMaxEndTime() const noexcept
            {
                return max_end_time_;
            }

            /// @brief Returns the maximum gap between intervals in this node.
            ///
            /// This function returns the maximum gap between any two intervals stored in this node.
            ///
            /// @return The maximum gap between intervals in this node.
            [[nodiscard]] TimeType GetMaxGap() const noexcept
            {
                return max_gap_;
            }

            /// @brief Returns the start index of the intervals in this node.
            ///
            /// This function returns the index of the first interval in this node.
            ///
            /// @return The start index of the intervals in this node.
            [[nodiscard]] IndexType GetStartIndex() const noexcept
            {
                return start_index_;
            }

            /// @brief Returns the finish index of the intervals in this node.
            ///
            /// This function returns the index of the last interval in this node.
            ///
            /// @return The finish index of the intervals in this node.
            [[nodiscard]] IndexType GetFinishIndex() const noexcept
            {
                return finish_index_;
            }

            /// @brief Returns the index of the parent.
            ///
            /// This function returns the index of the parent.
            ///
            /// @return The index of the parent.
            [[nodiscard]] IndexType GetParentIndex() const noexcept
            {
                return parent_index_;
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
            [[nodiscard]] const TimeIntervalTreeNode<TimeType, TargetNodeSize>* GetChild(
                const IndexType index) const noexcept
            {
                return children_[index];
            }

            /// @brief Sets the child node at the specified index.
            ///
            /// This function sets the child node at the specified index to the given pointer.
            ///
            /// @param index The index of the child node to set.
            /// @param child A pointer to the child node to set.
            ///
            /// @pre 0 <= index < kChildrenSize
            void SetChild(const IndexType index, TimeIntervalTreeNode<TimeType, TargetNodeSize>* child) noexcept
            {
                children_[index] = child;
            }

            /// @brief Returns a reference to the interval at the specified index.
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
                return *reinterpret_cast<const core::TimeInterval<TimeType>*>(&intervals_[index]);
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
                *reinterpret_cast<core::TimeInterval<TimeType>*>(&intervals_[index]) = interval;
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
                *reinterpret_cast<core::TimeInterval<TimeType>*>(&intervals_[index]) = std::move(interval);
            }

            /// @brief Sets the parent node of this node.
            ///
            /// This function sets the parent node of this node to the specified pointer.
            ///
            /// @param parent A pointer to the parent node to set.
            void SetParent(const TimeIntervalTreeNode<TimeType, TargetNodeSize>* parent) noexcept
            {
                parent_ = parent;
            }

            /// @brief Sets the minimum start time of the intervals in this node.
            ///
            /// This function sets the minimum start time of all intervals stored in this node
            ///
            /// @param min_start_time The minimum start time to set.
            void SetMinStartTime(const TimeType min_start_time) noexcept
            {
                min_start_time_ = min_start_time;
            }

            /// @brief Sets the maximum end time of the intervals in this node.
            ///
            /// This function sets the maximum end time of all intervals stored in this node.
            ///
            /// @param max_end_time The maximum end time to set.
            void SetMaxEndTime(const TimeType max_end_time) noexcept
            {
                max_end_time_ = max_end_time;
            }

            /// @brief Sets the maximum gap between intervals in this node.
            ///
            /// This function sets the maximum gap between any two intervals stored in this node.
            ///
            /// @param max_gap The maximum gap to set.
            void SetMaxGap(const TimeType max_gap) noexcept
            {
                max_gap_ = max_gap;
            }

            /// @brief Sets the start index of the intervals in this node.
            ///
            /// This function sets the index of the first interval in this node.
            ///
            /// @param start_index The start index to set.
            void SetStartIndex(const IndexType start_index) noexcept
            {
                start_index_ = start_index;
            }

            /// @brief Sets the finish index of the intervals in this node.
            ///
            /// This function sets the index of the last interval in this node.
            ///
            /// @param finish_index The finish index to set.
            void SetFinishIndex(const IndexType finish_index) noexcept
            {
                finish_index_ = finish_index;
            }

            /// @brief Sets the index of the parent.
            ///
            /// This function sets the index of the parent.
            ///
            /// @param parent_index The index of the parent to set.
            void SetParentIndex(const IndexType& parent_index) noexcept
            {
                parent_index_ = parent_index;
            }

        private:
            TimeIntervalTreeNode<TimeType, TargetNodeSize>* parent_{nullptr};
            TimeIntervalTreeNode<TimeType, TargetNodeSize>* children_[kChildrenSize] = {nullptr};
            IntervalStorage intervals_[kSlotSize];
            TimeType min_start_time_{0};
            TimeType max_end_time_{0};
            TimeType max_gap_{0};
            IndexType start_index_{0};
            IndexType finish_index_{0};
            IndexType parent_index_{0};
        };

        /// @brief The layout of a time-interval tree node, with optimized padding.
        ///
        /// The layout is determined by the \p SLotSize and whether \p TimeType is wider
        /// then the smallest unsigned type that can hold the number of slots.
        ///
        /// @tparam SlotSize the number of slots in the node, must be at least 4.
        template <size_t SlotSize>
            requires (SlotSize >= 4)
        class LayoutImpl<SlotSize, false>
        {
        public:
            /// @brief The slot size in the node.
            ///
            /// This is the number of \c TimeInterval<TimeType> slots in the node.
            static constexpr size_t kSlotSize = SlotSize;

            /// @brief The size of children each node can have.
            ///
            /// This is the number of child pointers in the node, which is one more than the number of slots.
            static constexpr size_t kChildrenSize = SlotSize + 1;

            /// @brief The type of the index used to access children and intervals.
            ///
            /// This is the smallest unsigned type that can hold the number of children in the node.
            using IndexType = core::SmallestUnsignedFor_t<kChildrenSize>;

            using IntervalStorage = std::aligned_storage_t<
                sizeof(core::TimeInterval<TimeType>),
                alignof(core::TimeInterval<TimeType>)
            >;

            /// @brief Default constructor.
            ///
            /// Initializes the layout with default values.
            LayoutImpl() noexcept = default;

            /// @brief Destructor.
            ///
            /// Cleans up the layout, but does not delete any pointers.
            ~LayoutImpl() noexcept = default;


            // Delete copy and assignment operators to prevent copying.

            LayoutImpl(const LayoutImpl&) noexcept = delete;
            LayoutImpl& operator=(const LayoutImpl&) noexcept = delete;

            /// @brief Returns a pointer to the parent node.
            ///
            /// This function returns a pointer to the parent node of this node.
            ///
            /// @return A pointer to the parent node, or \c nullptr if there is no parent.
            [[nodiscard]] TimeIntervalTreeNode<TimeType, TargetNodeSize>* GetParent() const noexcept
            {
                return parent_;
            }

            /// @brief Returns the minimum start time of the intervals in this node.
            ///
            /// This function returns the minimum start time of all intervals stored in this node.
            ///
            /// @return The minimum start time of the intervals in this node.
            [[nodiscard]] TimeType GetMinStartTime() const noexcept
            {
                return min_start_time_;
            }

            /// @brief Returns the maximum end time of the intervals in this node.
            ///
            /// This function returns the maximum end time of all intervals stored in this node.
            ///
            /// @return The maximum end time of the intervals in this node.
            [[nodiscard]] TimeType GetMaxEndTime() const noexcept
            {
                return max_end_time_;
            }

            /// @brief Returns the maximum gap between intervals in this node.
            ///
            /// This function returns the maximum gap between any two intervals stored in this node.
            ///
            /// @return The maximum gap between intervals in this node.
            [[nodiscard]] TimeType GetMaxGap() const noexcept
            {
                return max_gap_;
            }

            /// @brief Returns the start index of the intervals in this node.
            ///
            /// This function returns the index of the first interval in this node.
            ///
            /// @return The start index of the intervals in this node.
            [[nodiscard]] IndexType GetStartIndex() const noexcept
            {
                return start_index_;
            }

            /// @brief Returns the finish index of the intervals in this node.
            ///
            /// This function returns the index of the last interval in this node.
            ///
            /// @return The finish index of the intervals in this node.
            [[nodiscard]] IndexType GetFinishIndex() const noexcept
            {
                return finish_index_;
            }

            /// @brief Returns the index of the parent.
            ///
            /// This function returns the index of the parent.
            ///
            /// @return The index of the parent.
            [[nodiscard]] IndexType GetParentIndex() const noexcept
            {
                return parent_index_;
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
            [[nodiscard]] const TimeIntervalTreeNode<TimeType, TargetNodeSize>* GetChild(
                const IndexType index) const noexcept
            {
                return children_[index];
            }

            /// @brief Sets the child node at the specified index.
            ///
            /// This function sets the child node at the specified index to the given pointer.
            ///
            /// @param index The index of the child node to set.
            /// @param child A pointer to the child node to set.
            ///
            /// @pre 0 <= index < kChildrenSize
            void SetChild(const IndexType index, TimeIntervalTreeNode<TimeType, TargetNodeSize>* child) noexcept
            {
                children_[index] = child;
            }

            /// @brief Returns a reference to the interval at the specified index.
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
                return *reinterpret_cast<const core::TimeInterval<TimeType>*>(&intervals_[index]);
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
                *reinterpret_cast<core::TimeInterval<TimeType>*>(&intervals_[index]) = interval;
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
                *reinterpret_cast<core::TimeInterval<TimeType>*>(&intervals_[index]) = std::move(interval);
            }

            /// @brief Sets the parent node of this node.
            ///
            /// This function sets the parent node of this node to the specified pointer.
            ///
            /// @param parent A pointer to the parent node to set.
            void SetParent(const TimeIntervalTreeNode<TimeType, TargetNodeSize>* parent) noexcept
            {
                parent_ = parent;
            }

            /// @brief Sets the minimum start time of the intervals in this node.
            ///
            /// This function sets the minimum start time of all intervals stored in this node
            ///
            /// @param min_start_time The minimum start time to set.
            void SetMinStartTime(const TimeType min_start_time) noexcept
            {
                min_start_time_ = min_start_time;
            }

            /// @brief Sets the maximum end time of the intervals in this node.
            ///
            /// This function sets the maximum end time of all intervals stored in this node.
            ///
            /// @param max_end_time The maximum end time to set.
            void SetMaxEndTime(const TimeType max_end_time) noexcept
            {
                max_end_time_ = max_end_time;
            }

            /// @brief Sets the maximum gap between intervals in this node.
            ///
            /// This function sets the maximum gap between any two intervals stored in this node.
            ///
            /// @param max_gap The maximum gap to set.
            void SetMaxGap(const TimeType max_gap) noexcept
            {
                max_gap_ = max_gap;
            }

            /// @brief Sets the start index of the intervals in this node.
            ///
            /// This function sets the index of the first interval in this node.
            ///
            /// @param start_index The start index to set.
            void SetStartIndex(const IndexType start_index) noexcept
            {
                start_index_ = start_index;
            }

            /// @brief Sets the finish index of the intervals in this node.
            ///
            /// This function sets the index of the last interval in this node.
            ///
            /// @param finish_index The finish index to set.
            void SetFinishIndex(const IndexType finish_index) noexcept
            {
                finish_index_ = finish_index;
            }

            /// @brief Sets the index of the parent.
            ///
            /// This function sets the index of the parent.
            ///
            /// @param parent_index The index of the parent to set.
            void SetParentIndex(const IndexType& parent_index) noexcept
            {
                parent_index_ = parent_index;
            }

        private:
            TimeIntervalTreeNode<TimeType, TargetNodeSize>* parent_{nullptr};
            TimeIntervalTreeNode<TimeType, TargetNodeSize>* children_[kChildrenSize] = {nullptr};
            IntervalStorage intervals_[kSlotSize];
            IndexType start_index_{0};
            IndexType finish_index_{0};
            IndexType parent_index_{0};
            TimeType min_start_time_{0};
            TimeType max_end_time_{0};
            TimeType max_gap_{0};
        };

        /// @brief The layout of a time-interval tree node, with optimized padding.
        ///
        /// The layout is determined by the \p SLotSize and whether \p TimeType is wider
        /// then the smallest unsigned type that can hold the number of slots.
        ///
        /// @tparam SlotSize the number of slots in the node, must be at least 4.
        template <size_t SlotSize>
            requires (SlotSize >= 4)
        using Layout = LayoutImpl<SlotSize, core::BiggerAlignment_v<
                                      TimeType, core::SmallestUnsignedFor_t<SlotSize + 1>>>;

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
        using LayoutType = typename TimeIntervalTreeNodeLayout<TimeType, TargetNodeSize>::Type;
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
