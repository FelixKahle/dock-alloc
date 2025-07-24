// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_LAYOUT_H_
#define DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_LAYOUT_H_

#include <concepts>
#include <cstddef>
#include "absl/log/check.h"
#include "dockalloc/core/type_traits/smallest_unsigned_for.h"
#include "dockalloc/core/miscellaneous/inline.h"
#include "dockalloc/core/miscellaneous/core_types.h"

#define DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_FIELD_LAYOUT_API \
    public: \
    static constexpr size_t kSlotSize = SlotSize; \
    static constexpr size_t kChildrenSize = SlotSize + 1; \
    using IndexType = core::SmallestUnsignedFor_t<kChildrenSize>; \
    [[nodiscard]] DOCK_ALLOC_FORCE_INLINE TimeType GetMinStartTime() const noexcept { return min_start_time_; } \
    DOCK_ALLOC_FORCE_INLINE void SetMinStartTime(TimeType value) noexcept { min_start_time_ = value; } \
    [[nodiscard]] DOCK_ALLOC_FORCE_INLINE TimeType GetMaxEndTime() const noexcept { return max_end_time_; } \
    DOCK_ALLOC_FORCE_INLINE void SetMaxEndTime(TimeType value) noexcept { max_end_time_ = value; } \
    [[nodiscard]] DOCK_ALLOC_FORCE_INLINE TimeType GetMaxGap() const noexcept { return max_gap_; } \
    DOCK_ALLOC_FORCE_INLINE void SetMaxGap(TimeType value) noexcept { max_gap_ = value; } \
    [[nodiscard]] DOCK_ALLOC_FORCE_INLINE IndexType GetStartIndex() const noexcept { return start_index_; } \
    DOCK_ALLOC_FORCE_INLINE void SetStartIndex(IndexType value) noexcept { start_index_ = value; } \
    [[nodiscard]] DOCK_ALLOC_FORCE_INLINE IndexType GetFinishIndex() const noexcept { return finish_index_; } \
    DOCK_ALLOC_FORCE_INLINE void SetFinishIndex(IndexType value) noexcept { finish_index_ = value; } \
    [[nodiscard]] DOCK_ALLOC_FORCE_INLINE IndexType GetParentIndex() const noexcept { return parent_index_; } \
    DOCK_ALLOC_FORCE_INLINE void SetParentIndex(IndexType value) noexcept { parent_index_ = value; } \
    [[nodiscard]] DOCK_ALLOC_FORCE_INLINE NodeType* GetParent() const noexcept { return parent_; } \
    DOCK_ALLOC_FORCE_INLINE void SetParent(NodeType* value) noexcept { parent_ = value; } \
    [[nodiscard]] DOCK_ALLOC_FORCE_INLINE NodeType* GetChild(const IndexType index) const noexcept \
    { \
        DCHECK_LT(index, kChildrenSize); \
        return children_[index]; \
    } \
    DOCK_ALLOC_FORCE_INLINE void SetChild(const IndexType index, NodeType* value) noexcept \
    { \
        DCHECK_LT(index, kChildrenSize); \
        children_[index] = value; \
    } \
    [[nodiscard]] DOCK_ALLOC_FORCE_INLINE const core::TimeInterval<TimeType>& GetInterval(const IndexType index) const noexcept \
    { \
        DCHECK_LT(index, kSlotSize); \
        return intervals_[index].Get(); \
    } \
    DOCK_ALLOC_FORCE_INLINE void SetInterval(const IndexType index, const core::TimeInterval<TimeType>& interval) noexcept \
    { \
        DCHECK_LT(index, kSlotSize); \
        intervals_[index].Set(interval); \
    } \
    DOCK_ALLOC_FORCE_INLINE void SetInterval(const IndexType index, core::TimeInterval<TimeType>&& interval) noexcept \
    { \
        DCHECK_LT(index, kSlotSize); \
        intervals_[index].Set(std::move(interval)); \
    } \
    private:

namespace dockalloc::solver
{
    namespace internal
    {
        /// @brief The order in which fields are laid out in the time-interval tree node.
        ///
        /// Order of fields in the node affects the padding and alignment of the struct.
        /// We can avoid padding by carefully choosing the order of fields based on their alignment.
        /// A good order is to place the widest fields first,
        /// followed by the narrower ones in descending order of alignment.
        enum class TimeIntervalTreeNodeFieldLayoutOrder
        {
            TimeIndexPointer,
            TimePointerIndex,
            IndexTimePointer,
            IndexPointerTime,
            PointerTimeIndex,
            PointerIndexTime
        };

        /// @brief A storage for time intervals in a time-interval tree node.
        ///
        /// This class provides a storage for a time interval in a time-interval tree node,
        /// by using a raw byte array that is aligned to the size of \c core::TimeInterval<TimeType>.
        /// This allows to allocate uninitialized memory for the time intervals
        /// without requiring a separate allocation for each interval.
        ///
        /// @note Trying to access a time interval before it has been set will
        /// most likely result in undefined behavior.
        ///
        /// @tparam TimeType The unsigned integral type used for timestamp fields.
        template <typename TimeType>
            requires std::unsigned_integral<TimeType>
        class alignas(alignof(core::TimeInterval<TimeType>)) IntervalStorage
        {
        public:
            /// @brief Default constructor.
            ///
            /// This constructor initializes the storage to an empty state.
            ///
            /// @note The storage is not initialized, and accessing it before setting a time interval
            /// may lead to undefined behavior.
            DOCK_ALLOC_FORCE_INLINE IntervalStorage() noexcept = default;

            /// @brief Constructs an \c IntervalStorage from a \c core::TimeInterval<TimeType>.
            ///
            /// This constructor initializes the storage with the given time interval.
            ///
            /// @param interval The time interval to initialize the storage with.
            explicit DOCK_ALLOC_FORCE_INLINE IntervalStorage(const core::TimeInterval<TimeType>& interval) noexcept
            {
                Set(interval);
            }

            /// @brief Returns a reference to the time interval stored in this storage.
            ///
            /// This function provides a way to access the time interval stored in the raw byte array.
            ///
            /// @return A reference to the time interval stored in this storage.
            DOCK_ALLOC_FORCE_INLINE core::TimeInterval<TimeType>& Get() noexcept
            {
                return *reinterpret_cast<core::TimeInterval<TimeType>*>(bytes);
            }

            /// @brief Returns a const reference to the time interval stored in this storage.
            ///
            /// This function provides a way to access the time interval stored in the raw byte array
            ///
            /// @return A const reference to the time interval stored in this storage.
            DOCK_ALLOC_FORCE_INLINE const core::TimeInterval<TimeType>& Get() const noexcept
            {
                return *reinterpret_cast<const core::TimeInterval<TimeType>*>(bytes);
            }

            /// @brief Sets the time interval stored in this storage to the given interval.
            ///
            /// This function sets the time interval stored in the raw byte array to the given interval.
            ///
            /// @param interval The time interval to set in this storage.
            DOCK_ALLOC_FORCE_INLINE void Set(const core::TimeInterval<TimeType>& interval) noexcept
            {
                *reinterpret_cast<core::TimeInterval<TimeType>*>(bytes) = interval;
            }

            /// @brief Sets the time interval stored in this storage to the given interval, moving it.
            ///
            /// This function sets the time interval stored in the raw byte array to the given interval,
            /// which is moved into the storage.
            ///
            /// @param interval The time interval to set in this storage, moved.
            DOCK_ALLOC_FORCE_INLINE void Set(core::TimeInterval<TimeType>&& interval) noexcept
            {
                *reinterpret_cast<core::TimeInterval<TimeType>*>(bytes) = std::move(interval);
            }

        private:
            /// @brief The raw byte array that stores the time interval.
            ///
            /// This array is aligned to the size of \c core::TimeInterval<TimeType>
            /// and provides a way to store the time interval.
            alignas(alignof(core::TimeInterval<TimeType>)) std::byte bytes[sizeof(core::TimeInterval<TimeType>)]{};
        };

        /// @brief The layout of fields in a time-interval tree node.
        ///
        /// This class defines the layout of fields in a time-interval tree node,
        /// which includes the time intervals, pointers to parent and children,
        /// and aggregate fields for minimum start time, maximum end time, and maximum gap.
        /// The template specialization allows for different layouts based on the order of fields,
        /// which is determined by the alignment of the types involved.
        ///
        /// @tparam TimeType The unsigned integral type used for timestamp fields.
        /// @tparam NodeType The type of the node.
        /// @tparam SlotSize The number of \c TimeInterval<TimeType> slots in the node.
        /// @tparam Order The order in which fields are laid out in the node.
        template <typename TimeType, typename NodeType, size_t SlotSize, TimeIntervalTreeNodeFieldLayoutOrder Order>
            requires std::unsigned_integral<TimeType>
        class TimeIntervalTreeNodeFieldLayout;

        /// @brief The layout of fields in a time-interval tree node.
        ///
        /// This class defines the layout of fields in a time-interval tree node,
        /// which includes the time intervals, pointers to parent and children,
        /// and aggregate fields for minimum start time, maximum end time, and maximum gap.
        /// The template specialization allows for different layouts based on the order of fields,
        /// which is determined by the alignment of the types involved.
        ///
        /// @tparam TimeType The unsigned integral type used for timestamp fields.
        /// @tparam NodeType The type of the node.
        /// @tparam SlotSize The number of \c TimeInterval<TimeType> slots in the node.
        template <typename TimeType, typename NodeType, size_t SlotSize>
            requires std::unsigned_integral<TimeType>
        class TimeIntervalTreeNodeFieldLayout<TimeType, NodeType, SlotSize,
                                              TimeIntervalTreeNodeFieldLayoutOrder::TimeIndexPointer>
        {
            DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_FIELD_LAYOUT_API
            // Boolean
            bool is_leaf_{false};

            // Time

            TimeType min_start_time_;
            TimeType max_end_time_;
            TimeType max_gap_;
            IntervalStorage<TimeType> intervals_[kSlotSize];

            // Index

            IndexType start_index_;
            IndexType finish_index_;
            IndexType parent_index_;

            // Pointer

            NodeType* parent_{nullptr};
            NodeType* children_[kChildrenSize]{nullptr};
        };

        /// @brief The layout of fields in a time-interval tree node.
        ///
        /// This class defines the layout of fields in a time-interval tree node,
        /// which includes the time intervals, pointers to parent and children,
        /// and aggregate fields for minimum start time, maximum end time, and maximum gap.
        /// The template specialization allows for different layouts based on the order of fields,
        /// which is determined by the alignment of the types involved.
        ///
        /// @tparam TimeType The unsigned integral type used for timestamp fields.
        /// @tparam NodeType The type of the node.
        /// @tparam SlotSize The number of \c TimeInterval<TimeType> slots in the node.
        template <typename TimeType, typename NodeType, size_t SlotSize>
            requires std::unsigned_integral<TimeType>
        class TimeIntervalTreeNodeFieldLayout<TimeType, NodeType, SlotSize,
                                              TimeIntervalTreeNodeFieldLayoutOrder::TimePointerIndex>
        {
            DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_FIELD_LAYOUT_API
            // Boolean
            bool is_leaf_{false};
            // Time

            TimeType min_start_time_;
            TimeType max_end_time_;
            TimeType max_gap_;
            IntervalStorage<TimeType> intervals_[kSlotSize];

            // Pointer

            NodeType* parent_{nullptr};
            NodeType* children_[kChildrenSize]{nullptr};

            // Index

            IndexType start_index_;
            IndexType finish_index_;
            IndexType parent_index_;
        };

        /// @brief The layout of fields in a time-interval tree node.
        ///
        /// This class defines the layout of fields in a time-interval tree node,
        /// which includes the time intervals, pointers to parent and children,
        /// and aggregate fields for minimum start time, maximum end time, and maximum gap.
        /// The template specialization allows for different layouts based on the order of fields,
        /// which is determined by the alignment of the types involved.
        ///
        /// @tparam TimeType The unsigned integral type used for timestamp fields.
        /// @tparam NodeType The type of the node.
        /// @tparam SlotSize The number of \c TimeInterval<TimeType> slots in the node.
        template <typename TimeType, typename NodeType, size_t SlotSize>
            requires std::unsigned_integral<TimeType>
        class TimeIntervalTreeNodeFieldLayout<TimeType, NodeType, SlotSize,
                                              TimeIntervalTreeNodeFieldLayoutOrder::IndexTimePointer>
        {
            DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_FIELD_LAYOUT_API
            // Boolean
            bool is_leaf_{false};
            // Index

            IndexType start_index_;
            IndexType finish_index_;
            IndexType parent_index_;

            // Time

            TimeType min_start_time_;
            TimeType max_end_time_;
            TimeType max_gap_;
            IntervalStorage<TimeType> intervals_[kSlotSize];

            // Pointer

            NodeType* parent_{nullptr};
            NodeType* children_[kChildrenSize]{nullptr};
        };

        /// @brief The layout of fields in a time-interval tree node.
        ///
        /// This class defines the layout of fields in a time-interval tree node,
        /// which includes the time intervals, pointers to parent and children,
        /// and aggregate fields for minimum start time, maximum end time, and maximum gap.
        /// The template specialization allows for different layouts based on the order of fields,
        /// which is determined by the alignment of the types involved.
        ///
        /// @tparam TimeType The unsigned integral type used for timestamp fields.
        /// @tparam NodeType The type of the node.
        /// @tparam SlotSize The number of \c TimeInterval<TimeType> slots in the node.
        template <typename TimeType, typename NodeType, size_t SlotSize>
            requires std::unsigned_integral<TimeType>
        class TimeIntervalTreeNodeFieldLayout<TimeType, NodeType, SlotSize,
                                              TimeIntervalTreeNodeFieldLayoutOrder::IndexPointerTime>
        {
            DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_FIELD_LAYOUT_API
            // Boolean
            bool is_leaf_{false};
            // Index

            IndexType start_index_;
            IndexType finish_index_;
            IndexType parent_index_;

            // Pointer

            NodeType* parent_{nullptr};
            NodeType* children_[kChildrenSize]{nullptr};

            // Time

            TimeType min_start_time_;
            TimeType max_end_time_;
            TimeType max_gap_;
            IntervalStorage<TimeType> intervals_[kSlotSize];
        };

        /// @brief The layout of fields in a time-interval tree node.
        ///
        /// This class defines the layout of fields in a time-interval tree node,
        /// which includes the time intervals, pointers to parent and children,
        /// and aggregate fields for minimum start time, maximum end time, and maximum gap.
        /// The template specialization allows for different layouts based on the order of fields,
        /// which is determined by the alignment of the types involved.
        ///
        /// @tparam TimeType The unsigned integral type used for timestamp fields.
        /// @tparam NodeType The type of the node.
        /// @tparam SlotSize The number of \c TimeInterval<TimeType> slots in the node.
        template <typename TimeType, typename NodeType, size_t SlotSize>
            requires std::unsigned_integral<TimeType>
        class TimeIntervalTreeNodeFieldLayout<TimeType, NodeType, SlotSize,
                                              TimeIntervalTreeNodeFieldLayoutOrder::PointerTimeIndex>
        {
            DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_FIELD_LAYOUT_API
            // Boolean
            bool is_leaf_{false};

            // Pointer

            NodeType* parent_{nullptr};
            NodeType* children_[kChildrenSize]{nullptr};

            // Time

            TimeType min_start_time_;
            TimeType max_end_time_;
            TimeType max_gap_;
            IntervalStorage<TimeType> intervals_[kSlotSize];

            // Index

            IndexType start_index_;
            IndexType finish_index_;
            IndexType parent_index_;
        };

        /// @brief The layout of fields in a time-interval tree node.
        ///
        /// This class defines the layout of fields in a time-interval tree node,
        /// which includes the time intervals, pointers to parent and children,
        /// and aggregate fields for minimum start time, maximum end time, and maximum gap.
        /// The template specialization allows for different layouts based on the order of fields,
        /// which is determined by the alignment of the types involved.
        ///
        /// @tparam TimeType The unsigned integral type used for timestamp fields.
        /// @tparam NodeType The type of the node.
        /// @tparam SlotSize The number of \c TimeInterval<TimeType> slots in the node.
        template <typename TimeType, typename NodeType, size_t SlotSize>
            requires std::unsigned_integral<TimeType>
        class TimeIntervalTreeNodeFieldLayout<TimeType, NodeType, SlotSize,
                                              TimeIntervalTreeNodeFieldLayoutOrder::PointerIndexTime>
        {
            DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_FIELD_LAYOUT_API
            // Boolean
            bool is_leaf_{false};

            // Pointer

            NodeType* parent_{nullptr};
            NodeType* children_[kChildrenSize]{nullptr};

            // Index

            IndexType start_index_;
            IndexType finish_index_;
            IndexType parent_index_;

            // Time

            TimeType min_start_time_;
            TimeType max_end_time_;
            TimeType max_gap_;
            IntervalStorage<TimeType> intervals_[kSlotSize];
        };

        /// @brief The implementation of the time-interval tree node layout based on the desired size of slots.
        ///
        /// This class provides a layout for the time-interval tree node that matches the desired size of slots.
        ///
        /// @tparam TimeType The unsigned integral type used for timestamp fields.
        /// @tparam NodeType The type of the node.
        /// @tparam SlotSize The number of \c TimeInterval<TimeType> slots in the node.
        template <typename TimeType, typename NodeType, size_t SlotSize>
            requires std::unsigned_integral<TimeType> && (SlotSize >= 4)
        class LayoutImpl
        {
            /// @brief Determines the order of fields in the time-interval tree node layout.
            ///
            /// This function computes the order of fields in the time-interval tree node layout
            /// based on the alignment of the types involved.
            ///
            /// @return The order of fields in the time-interval tree node layout.
            static constexpr TimeIntervalTreeNodeFieldLayoutOrder NodeFieldLayoutOrder() noexcept
            {
                // ReSharper disable once CppTooWideScopeInitStatement
                constexpr size_t alignof_time = alignof(TimeType);
                // ReSharper disable once CppTooWideScopeInitStatement
                constexpr size_t alignof_index = alignof(core::SmallestUnsignedFor_t<SlotSize + 1>);
                // ReSharper disable once CppTooWideScopeInitStatement
                constexpr size_t alignof_pointer = alignof(NodeType*);

                if constexpr (alignof_time >= alignof_index && alignof_index >= alignof_pointer)
                {
                    return TimeIntervalTreeNodeFieldLayoutOrder::TimeIndexPointer;
                }
                else if constexpr (alignof_time >= alignof_pointer && alignof_pointer >=
                    alignof_index)
                {
                    return TimeIntervalTreeNodeFieldLayoutOrder::TimePointerIndex;
                }
                else if constexpr (alignof_index >= alignof_time && alignof_time >=
                    alignof_pointer)
                {
                    return TimeIntervalTreeNodeFieldLayoutOrder::IndexTimePointer;
                }
                else if constexpr (alignof_index >= alignof_pointer && alignof_pointer >=
                    alignof_time)
                {
                    return TimeIntervalTreeNodeFieldLayoutOrder::IndexPointerTime;
                }
                else if constexpr (alignof_pointer >= alignof_time && alignof_time >=
                    alignof_index)
                {
                    return TimeIntervalTreeNodeFieldLayoutOrder::PointerTimeIndex;
                }
                else
                {
                    return TimeIntervalTreeNodeFieldLayoutOrder::PointerIndexTime;
                }
            }

        public:
            /// @brief The order of fields in the time-interval tree node layout.
            ///
            /// This is a compile-time constant that determines the order of fields in the node layout.
            static constexpr TimeIntervalTreeNodeFieldLayoutOrder kFieldLayoutOrder = NodeFieldLayoutOrder();

            /// @brief The Base layout type for the time-interval tree node.
            ///
            /// This is the base layout type that provides the common fields for the implementation.
            using Base = TimeIntervalTreeNodeFieldLayout<TimeType, NodeType, SlotSize, kFieldLayoutOrder>;

            /// @brief The type of the index used to access children and intervals.
            ///
            /// This is the smallest unsigned type that can hold the number of children in the node.
            using IndexType = typename Base::IndexType;

            /// @brief Returns a pointer to the parent node.
            ///
            /// This function returns a pointer to the parent node of this node.
            ///
            /// @return A pointer to the parent node, or \c nullptr if there is no parent.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE NodeType* GetParent() const noexcept
            {
                return fields_.GetParent();
            }

            /// @brief Returns the minimum start time of the intervals in this node.
            ///
            /// This function returns the minimum start time of all intervals stored in this node.
            ///
            /// @return The minimum start time of the intervals in this node.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE TimeType GetMinStartTime() const noexcept
            {
                return fields_.GetMinStartTime();
            }

            /// @brief Returns the maximum end time of the intervals in this node.
            ///
            /// This function returns the maximum end time of all intervals stored in this node.
            ///
            /// @return The maximum end time of the intervals in this node.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE TimeType GetMaxEndTime() const noexcept
            {
                return fields_.GetMaxEndTime();
            }

            /// @brief Returns the maximum gap between intervals in this node.
            ///
            /// This function returns the maximum gap between any two intervals stored in this node.
            ///
            /// @return The maximum gap between intervals in this node.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE TimeType GetMaxGap() const noexcept
            {
                return fields_.GetMaxGap();
            }

            /// @brief Returns the start index of the intervals in this node.
            ///
            /// This function returns the index of the first interval in this node.
            ///
            /// @return The start index of the intervals in this node.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE IndexType GetStartIndex() const noexcept
            {
                return fields_.GetStartIndex();
            }

            /// @brief Returns the finish index of the intervals in this node.
            ///
            /// This function returns the index of the last interval in this node.
            ///
            /// @return The finish index of the intervals in this node.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE IndexType GetFinishIndex() const noexcept
            {
                return fields_.GetFinishIndex();
            }

            /// @brief Returns the index of the parent.
            ///
            /// This function returns the index of the parent.
            ///
            /// @return The index of the parent.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE IndexType GetParentIndex() const noexcept
            {
                return fields_.GetParentIndex();
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
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE const NodeType* GetChild(
                const IndexType index) const noexcept
            {
                return fields_.GetChild(index);
            }

            /// @brief Sets the child node at the specified index.
            ///
            /// This function sets the child node at the specified index to the given pointer.
            ///
            /// @param index The index of the child node to set.
            /// @param child A pointer to the child node to set.
            ///
            /// @pre 0 <= index < kChildrenSize
            DOCK_ALLOC_FORCE_INLINE void SetChild(const IndexType index, NodeType* child) noexcept
            {
                fields_.SetChild(index, child);
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
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE const core::TimeInterval<TimeType>& GetInterval(
                const IndexType index) const noexcept
            {
                return fields_.GetInterval(index);
            }

            /// @brief Sets the interval at the specified index.
            ///
            /// This function sets the interval at the specified index to the given interval.
            ///
            /// @param index The index of the interval to set.
            /// @param interval The interval to set at the specified index.
            ///
            /// @pre 0 <= index < kSlotSize
            DOCK_ALLOC_FORCE_INLINE void SetInterval(const IndexType index,
                                                     const core::TimeInterval<TimeType>& interval) noexcept
            {
                fields_.SetInterval(index, interval);
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
            DOCK_ALLOC_FORCE_INLINE void SetInterval(const IndexType index,
                                                     core::TimeInterval<TimeType>&& interval) noexcept
            {
                fields_.SetInterval(index, std::move(interval));
            }

            /// @brief Sets the parent node of this node.
            ///
            /// This function sets the parent node of this node to the specified pointer.
            ///
            /// @param parent A pointer to the parent node to set.
            DOCK_ALLOC_FORCE_INLINE void SetParent(const NodeType* parent) noexcept
            {
                fields_.SetParent(parent);
            }

            /// @brief Sets the minimum start time of the intervals in this node.
            ///
            /// This function sets the minimum start time of all intervals stored in this node
            ///
            /// @param min_start_time The minimum start time to set.
            DOCK_ALLOC_FORCE_INLINE void SetMinStartTime(const TimeType min_start_time) noexcept
            {
                fields_.SetMinStartTime(min_start_time);
            }

            /// @brief Sets the maximum end time of the intervals in this node.
            ///
            /// This function sets the maximum end time of all intervals stored in this node.
            ///
            /// @param max_end_time The maximum end time to set.
            DOCK_ALLOC_FORCE_INLINE void SetMaxEndTime(const TimeType max_end_time) noexcept
            {
                fields_.SetMaxEndTime(max_end_time);
            }

            /// @brief Sets the maximum gap between intervals in this node.
            ///
            /// This function sets the maximum gap between any two intervals stored in this node.
            ///
            /// @param max_gap The maximum gap to set.
            DOCK_ALLOC_FORCE_INLINE void SetMaxGap(const TimeType max_gap) noexcept
            {
                fields_.SetMaxGap(max_gap);
            }

            /// @brief Sets the start index of the intervals in this node.
            ///
            /// This function sets the index of the first interval in this node.
            ///
            /// @param start_index The start index to set.
            DOCK_ALLOC_FORCE_INLINE void SetStartIndex(const IndexType start_index) noexcept
            {
                fields_.SetStartIndex(start_index);
            }

            /// @brief Sets the finish index of the intervals in this node.
            ///
            /// This function sets the index of the last interval in this node.
            ///
            /// @param finish_index The finish index to set.
            DOCK_ALLOC_FORCE_INLINE void SetFinishIndex(const IndexType finish_index) noexcept
            {
                fields_.SetFinishIndex(finish_index);
            }

            /// @brief Sets the index of the parent.
            ///
            /// This function sets the index of the parent.
            ///
            /// @param parent_index The index of the parent to set.
            DOCK_ALLOC_FORCE_INLINE void SetParentIndex(const IndexType& parent_index) noexcept
            {
                fields_.SetParentIndex(parent_index);
            }

        private:
            Base fields_;
        };
    }

    /// @brief Computes a node struct layout for a time-interval tree, matching a target byte size.
    ///
    /// @tparam TimeType The unsigned integral type used for timestamp fields.
    /// @tparam NodeType The type of the node, which is typically a pointer to the node type itself.
    /// @tparam TargetNodeSize The desired size in bytes of the generated node struct.
    ///
    /// Internally, a compile-time binary search is performed to find the optimal slot count
    /// (each slot holds a \c TimeInterval<TimeType>) so that the resulting \c Type alias
    /// refers to a struct whose \c sizeof is as close to \p TargetNodeSize. Each node stores
    /// an array of \p SlotSize intervals, plus parent/child pointers, aggregate min/max/gap
    /// fields, and slot indices. The layout is optimized to minimize padding.
    ///
    /// @note The \c TimeIntervalTreeNodeLayout does not own any pointers, it only provides
    /// a layout for the node structure. The actual memory management is handled by the caller,
    /// so the caller must ensure that the pointers to parent and children are valid and deallocated.
    template <typename TimeType, typename NodeType, size_t TargetNodeSize>
        requires std::unsigned_integral<TimeType>
    struct TimeIntervalTreeNodeLayout
    {
    private:
        /// @brief The minimum size of the node layout, which is the size of the base layout with 4 slots.
        ///
        /// This is the minimum size of the node layout, which is the size of the base layout with 4 slots.
        static constexpr size_t kMinSize = sizeof(internal::LayoutImpl<TimeType, NodeType, 4>);

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
            if constexpr (Begin == End)
            {
                return Begin;
            }
            else
            {
                if constexpr (constexpr size_t mid_index = (Begin + End) / 2; sizeof(
                    internal::LayoutImpl<
                        TimeType, NodeType, mid_index + 1>) > TargetNodeSize)
                {
                    return NodeTargetSlots<Begin, mid_index>();
                }
                else
                {
                    return NodeTargetSlots<mid_index + 1, End>();
                }
            }
        }

    public:
        /// @brief The number of slots in the node, determined by the compile-time binary search.
        ///
        /// This is the number of \c TimeInterval<TimeType> slots in the node, which is determined
        /// by the compile-time binary search to find the optimal slot count.
        static constexpr size_t kNodeSlotSize = (kMinSize > TargetNodeSize)
                                                    ? 4
                                                    : NodeTargetSlots<4, TargetNodeSize>();

        /// @brief The number of child pointers in the node, which is one more than the number of slots.
        ///
        /// This is the number of child pointers in the node, which is one more than the number of slots.
        static constexpr size_t kNodeChildSize = kNodeSlotSize + 1;

        /// @brief The type of the time-interval tree node layout, with optimized padding and slot count.
        ///
        /// This is the result of the compile-time binary search to find the optimal slot count
        /// and the compile time layout of the node.
        using Type = internal::LayoutImpl<TimeType, NodeType, kNodeSlotSize>;
    };
}

// Undef macro to prevent redefinition and confusion in other headers.
#undef DOCK_ALLOC_SOLVER_TIME_INTERVAL_TREE_NODE_FIELD_LAYOUT_API

#endif
