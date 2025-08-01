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

#ifndef DOCK_ALLOC_SOLVER_CONTAINER_QUAY_H_
#define DOCK_ALLOC_SOLVER_CONTAINER_QUAY_H_

#include <concepts>
#include "dockalloc/solver/container/quay_segment_tree.h"
#include "dockalloc/solver/container/bit_vector.h"

namespace dockalloc::solver
{
    /// @brief Enum class representing the backend types for the Quay class.
    ///
    /// This enum class defines the available backends for managing occupancy in a quay.
    enum class QuayBackend
    {
        QuaySegmentTree,
        BitVector,
    };

    /// @brief Quay class template for managing occupancy of segments using a specified backend.
    ///
    /// This class template provides an interface for managing occupancy of segments in a quay.
    ///
    /// @tparam PositionType The type of positions used in the quay, which must be an unsigned integral type.
    /// @tparam BackendType The backend type used for managing occupancy,
    /// which must be one of the defined \c QuayBackend types.
    template <typename PositionType, QuayBackend BackendType>
        requires std::unsigned_integral<PositionType>
    class Quay;

    /// @brief Concept for a quay that supports occupancy management and querying.
    ///
    /// This concept defines the requirements for a quay type, including methods for occupying and freeing ranges,
    /// checking if ranges are free or occupied, finding free positions, and comparing quays for equality.
    ///
    /// @tparam T The type of the quay, which must support the specified operations.
    /// @tparam PositionType The type of positions used in the quay, which must be
    /// an unsigned integral type.
    template <typename T, typename PositionType>
    concept IsQuay = requires(T quay, const T const_quay, const PositionType position,
                              const core::SegmentRange<PositionType>& range)
    {
        requires std::unsigned_integral<PositionType>;
        { quay.Occupy(range) } -> std::same_as<void>;
        { quay.Free(range) } -> std::same_as<void>;
        { const_quay.IsRangeFree(range) } -> std::same_as<bool>;
        { const_quay.IsRangeOccupied(range) } -> std::same_as<bool>;
        { const_quay.FindFree(position) } -> std::same_as<std::optional<PositionType>>;
        { const_quay.FindFree(position, range) } -> std::same_as<std::optional<PositionType>>;
        { const_quay.GetQuaySegmentCount() } -> std::same_as<size_t>;
        { const_quay == const_quay } -> std::same_as<bool>;
    };

    /// @brief Quay class template specialization for the \c QuaySegmentTree backend.
    ///
    /// This specialization uses a segment tree to manage occupancy of segments in the quay.
    ///
    /// @tparam PositionType The type of positions used in the quay, which must be an unsigned integral type.
    template <typename PositionType>
        requires std::unsigned_integral<PositionType>
    class Quay<PositionType, QuayBackend::QuaySegmentTree>
    {
    public:
        /// @brief Constructs a new Quay instance with a specified number of segments.
        ///
        /// This constructor initializes the quay segment tree with the given number of segments.
        /// The segments are initially marked as free.
        ///
        /// @param num_segments The number of segments in the quay.
        explicit DOCK_ALLOC_FORCE_INLINE Quay(const size_t num_segments)
            : quay_segment_tree_(num_segments)
        {
        }

        /// @brief Occupies a specified range of segments in the quay.
        ///
        /// This method marks the specified range of segments as occupied.
        ///
        /// @param segment_range The range of segments to occupy, specified as a \c core::SegmentRange.
        DOCK_ALLOC_FORCE_INLINE void Occupy(const core::SegmentRange<PositionType>& segment_range) noexcept
        {
            quay_segment_tree_.Occupy(segment_range);
        }

        /// @brief Frees a specified range of segments in the quay.
        ///
        /// This method marks the specified range of segments as free.
        ///
        /// @param segment_range The range of segments to free, specified as a \c core::SegmentRange.
        DOCK_ALLOC_FORCE_INLINE void Free(const core::SegmentRange<PositionType>& segment_range) noexcept
        {
            quay_segment_tree_.Free(segment_range);
        }

        /// @brief Checks if a specified range of segments is free.
        ///
        /// This method checks if all segments in the specified range are free.
        ///
        /// @param segment_range The range of segments to check, specified as a \c core::SegmentRange.
        DOCK_ALLOC_FORCE_INLINE bool IsRangeFree(const core::SegmentRange<PositionType>& segment_range) const noexcept
        {
            return quay_segment_tree_.IsRangeFree(segment_range);
        }

        /// @brief Checks if a specified range of segments is occupied.
        ///
        /// This method checks if all segments in the specified range are occupied.
        ///
        /// @param segment_range The range of segments to check, specified as a \c core::SegmentRange.
        DOCK_ALLOC_FORCE_INLINE bool IsRangeOccupied(
            const core::SegmentRange<PositionType>& segment_range) const noexcept
        {
            return quay_segment_tree_.IsRangeOccupied(segment_range);
        }

        /// @brief Finds the starting position of the first free contiguous block of at least size k.
        ///
        /// This method searches for a free segment of at least the specified size within the quay.
        ///
        /// @param k The minimum required length of the free segment.
        ///
        /// @return A \c std::optional containing the starting position if a suitable segment is found;
        /// \c std::nullopt otherwise.
        DOCK_ALLOC_FORCE_INLINE std::optional<PositionType> FindFree(const PositionType k) const noexcept
        {
            return quay_segment_tree_.FindFree(k);
        }

        /// @brief Finds the starting position of the first free contiguous block of at
        /// least size k within a specified range.
        ///
        /// This method searches for a free segment of at least the specified size within a given range of segments.
        ///
        /// @param k The minimum required length of the free segment.
        /// @param search_range The range of segments [start, end) to search within,
        /// specified as a \c core::SegmentRange.
        ///
        /// @return A \c std::optional containing the starting position if a suitable segment is found;
        /// \c std::nullopt otherwise.
        DOCK_ALLOC_FORCE_INLINE std::optional<PositionType> FindFree(const PositionType k,
                                                                     const core::SegmentRange<PositionType>&
                                                                     search_range) const noexcept
        {
            return quay_segment_tree_.FindFree(k, search_range);
        }

        /// @brief Gets the number of segments in the quay.
        ///
        /// This method returns the total number of segments managed by the quay segment tree.
        ///
        /// @return The number of segments in the quay as a \c size_t.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t GetQuaySegmentCount() const noexcept
        {
            return static_cast<size_t>(quay_segment_tree_.GetSize());
        }

        /// @brief Checks if this quay is logically equal to another quay.
        ///
        /// This method compares the internal state of two quays to determine if they are logically equivalent.
        ///
        /// @param other The other quay to compare against.
        ///
        /// @return \c true if the quays are logically equal, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool operator==(const Quay& other) const noexcept
        {
            return quay_segment_tree_ == other.quay_segment_tree_;
        }

        /// @brief Checks if this quay is logically unequal to another quay.
        ///
        /// This method compares the internal state of two quays to determine if they are logically different.
        ///
        /// @param other The other quay to compare against.
        ///
        /// @return \c true if the quays are logically unequal, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool operator!=(const Quay& other) const noexcept
        {
            return !(*this == other);
        }

    private:
        QuaySegmentTree<PositionType> quay_segment_tree_;
    };

    template <typename PositionType>
        requires std::unsigned_integral<PositionType>
    class Quay<PositionType, QuayBackend::BitVector>
    {
    public:
        using WordType = uint64_t;

        /// @brief Constructs a new Quay instance with a specified number of segments.
        ///
        /// This constructor initializes the quay segment tree with the given number of segments.
        /// The segments are initially marked as free.
        ///
        /// @param num_segments The number of segments in the quay.
        explicit DOCK_ALLOC_FORCE_INLINE Quay(const size_t num_segments)
            : bit_vector_(num_segments, true)
        {
        }

        /// @brief Occupies a specified range of segments in the quay.
        ///
        /// This method marks the specified range of segments as occupied.
        ///
        /// @param segment_range The range of segments to occupy, specified as a \c core::SegmentRange.
        DOCK_ALLOC_FORCE_INLINE void Occupy(const core::SegmentRange<PositionType>& segment_range) noexcept
        {
            const size_t end_segment = std::min(static_cast<size_t>(segment_range.GetEnd()), GetQuaySegmentCount());
            const size_t start_segment = std::min(static_cast<size_t>(segment_range.GetStart()), end_segment);

            bit_vector_.ClearBits(start_segment, end_segment);
        }

        /// @brief Frees a specified range of segments in the quay.
        ///
        /// This method marks the specified range of segments as free.
        ///
        /// @param segment_range The range of segments to free, specified as a \c core::SegmentRange.
        DOCK_ALLOC_FORCE_INLINE void Free(const core::SegmentRange<PositionType>& segment_range) noexcept
        {
            const size_t end_segment = std::min(static_cast<size_t>(segment_range.GetEnd()), GetQuaySegmentCount());
            const size_t start_segment = std::min(static_cast<size_t>(segment_range.GetStart()), end_segment);

            bit_vector_.SetBits(start_segment, end_segment);
        }

        /// @brief Checks if a specified range of segments is free.
        ///
        /// This method checks if all segments in the specified range are free.
        ///
        /// @param segment_range The range of segments to check, specified as a \c core::SegmentRange.
        DOCK_ALLOC_FORCE_INLINE bool IsRangeFree(const core::SegmentRange<PositionType>& segment_range) const noexcept
        {
            const size_t end_segment = std::min(static_cast<size_t>(segment_range.GetEnd()), GetQuaySegmentCount());
            const size_t start_segment = std::min(static_cast<size_t>(segment_range.GetStart()), end_segment);

            if (start_segment >= end_segment)
            {
                return true;
            }

            return bit_vector_.AreBitsSet(start_segment, end_segment);
        }

        /// @brief Checks if a specified range of segments is occupied.
        ///
        /// This method checks if all segments in the specified range are occupied.
        ///
        /// @param segment_range The range of segments to check, specified as a \c core::SegmentRange.
        DOCK_ALLOC_FORCE_INLINE bool IsRangeOccupied(
            const core::SegmentRange<PositionType>& segment_range) const noexcept
        {
            const size_t end_segment = std::min(static_cast<size_t>(segment_range.GetEnd()), GetQuaySegmentCount());
            const size_t start_segment = std::min(static_cast<size_t>(segment_range.GetStart()), end_segment);
  if (start_segment >= end_segment)
            {
                return false;
            }

            return bit_vector_.AreBitsClear(start_segment, end_segment);
        }

        /// @brief Finds the starting position of the first free contiguous block of at least size k.
        ///
        /// This method searches for a free segment of at least the specified size within the quay.
        ///
        /// @param k The minimum required length of the free segment.
        ///
        /// @return A \c std::optional containing the starting position if a suitable segment is found;
        /// \c std::nullopt otherwise.
        DOCK_ALLOC_FORCE_INLINE std::optional<PositionType> FindFree(const PositionType k) const noexcept
        {
            return bit_vector_.FindClearRange(0, GetQuaySegmentCount(), k);
        }

        /// @brief Finds the starting position of the first free contiguous block of at
        /// least size k within a specified range.
        ///
        /// This method searches for a free segment of at least the specified size within a given range of segments.
        ///
        /// @param k The minimum required length of the free segment.
        /// @param search_range The range of segments [start, end) to search within,
        /// specified as a \c core::SegmentRange.
        ///
        /// @return A \c std::optional containing the starting position if a suitable segment is found;
        /// \c std::nullopt otherwise.
        DOCK_ALLOC_FORCE_INLINE std::optional<PositionType> FindFree(const PositionType k,
                                                                     const core::SegmentRange<PositionType>&
                                                                     search_range) const noexcept
        {
            const size_t end_segment = std::min(static_cast<size_t>(search_range.GetEnd()), GetQuaySegmentCount());
            const size_t start_segment = std::min(static_cast<size_t>(search_range.GetStart()), end_segment);

            return bit_vector_.FindClearRange(start_segment, end_segment, k);
        }

        /// @brief Gets the number of segments in the quay.
        ///
        /// This method returns the total number of segments managed by the quay segment tree.
        ///
        /// @return The number of segments in the quay as a \c size_t.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t GetQuaySegmentCount() const noexcept
        {
            return bit_vector_.GetBitCount();
        }

        /// @brief Checks if this quay is logically equal to another quay.
        ///
        /// This method compares the internal state of two quays to determine if they are logically equivalent.
        ///
        /// @param other The other quay to compare against.
        ///
        /// @return \c true if the quays are logically equal, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool operator==(const Quay& other) const noexcept
        {
            return bit_vector_ == other.bit_vector_;
        }

        /// @brief Checks if this quay is logically unequal to another quay.
        ///
        /// This method compares the internal state of two quays to determine if they are logically different.
        ///
        /// @param other The other quay to compare against.
        ///
        /// @return \c true if the quays are logically unequal, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool operator!=(const Quay& other) const noexcept
        {
            return !(*this == other);
        }

    private:
        BitVector<WordType> bit_vector_;
    };
}

#endif
