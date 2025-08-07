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
#include "absl/log/check.h"
#include "dockalloc/solver/container/interval_gap_tree.h"
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
    /// @tparam BackendType The backend type used for managing occupancy,
    /// which must be one of the defined \c QuayBackend types.
    template <QuayBackend BackendType>
    class Quay;

    /// @brief Concept for a quay that supports occupancy management and querying.
    ///
    /// This concept defines the requirements for a quay type, including methods for occupying and freeing ranges,
    /// checking if ranges are free or occupied, finding free positions, and comparing quays for equality.
    ///
    /// @tparam T The type of the quay, which must support the specified operations.
    template <typename T>
    concept IsQuay = requires(T quay, const T const_quay, const size_t position,
                              const core::SegmentRange<size_t>& range)
    {
        { quay.Occupy(range) } -> std::same_as<void>;
        { quay.Free(range) } -> std::same_as<void>;
        { const_quay.IsRangeFree(range) } -> std::same_as<bool>;
        { const_quay.IsRangeOccupied(range) } -> std::same_as<bool>;
        { const_quay.FindFirstFreeRange(position) } -> std::same_as<std::optional<size_t>>;
        { const_quay.FindFirstFreeRange(position, range) } -> std::same_as<std::optional<size_t>>;
        { const_quay.GetQuaySegmentCount() } -> std::same_as<size_t>;
        { const_quay == const_quay } -> std::same_as<bool>;
    };

    /// @brief Quay class template specialization for the \c IntervalGapTree backend.
    ///
    /// This specialization uses a segment tree to manage occupancy of segments in the quay.
    template <>
    class Quay<QuayBackend::QuaySegmentTree>
    {
    public:
        /// @brief The expected maximum height of the quay segment tree.
        ///
        /// This constant defines the expected maximum height of the segment tree used in the quay.
        /// The tree can grow larger than this height, but search and equality operations
        /// are optimized up to this height. Search and equality operations are guaranteed to be inlined
        /// instead of being allocated on the heap, which might help with performance.
        /// The tree can grow larger than this height, falling back to heap allocation
        /// for larger trees.
        static constexpr size_t kExpectedMaxTreeHeight = 16;

        /// @brief Iterator for iterating over free ranges in the quay.
        ///
        /// This iterator allows iteration over the starting positions of free segments of a specified length
        /// of the quay.
        class FreeRangeIterator
        {
        public:
            using value_type = size_t;
            using reference = const size_t&;
            using iterator_category = std::forward_iterator_tag;

            /// @brief Dereferences the iterator to get the current free range starting position.
            ///
            /// Defaults to the current position of the iterator, which is the starting index
            /// of the free range that matches the required length.
            ///
            /// @pre The iterator must not be an "end" iterator.
            DOCK_ALLOC_FORCE_INLINE reference operator*() const noexcept
            {
                return *iterator_;
            }

            /// @brief Increments the iterator to the next free range starting position.
            ///
            /// This method advances the iterator to the next position in the segment tree
            /// that contains a free segment of at least the required length.
            ///
            /// @pre The iterator must not be an "end" iterator.
            DOCK_ALLOC_FORCE_INLINE FreeRangeIterator& operator++() noexcept
            {
                ++iterator_;
                return *this;
            }

            /// @brief Post-increment operator for the iterator.
            ///
            /// This method returns a copy of the iterator before incrementing it,
            /// allowing for postfix increment behavior.
            ///
            /// @pre The iterator must not be an "end" iterator.
            DOCK_ALLOC_FORCE_INLINE FreeRangeIterator operator++(int) noexcept
            {
                auto tmp = *this;
                ++iterator_;
                return tmp;
            }

            /// @brief Compares two iterators for equality.
            ///
            /// This method checks if two iterators point to the same position in the segment tree.
            ///
            /// @param other The other iterator to compare against.
            ///
            /// @return \c true if both iterators point to the same position, \c false otherwise.
            DOCK_ALLOC_FORCE_INLINE bool operator==(const FreeRangeIterator& other) const noexcept
            {
                return iterator_ == other.iterator_;
            }

            /// @brief Compares two iterators for inequality.
            ///
            /// This method checks if two iterators do not point to the same position in the segment tree.
            ///
            /// @param other The other iterator to compare against.
            ///
            /// @return \c true if the iterators point to different positions, \c false if they are equal.
            DOCK_ALLOC_FORCE_INLINE bool operator!=(const FreeRangeIterator& other) const noexcept
            {
                return !(*this == other);
            }

        private:
            friend class Quay;

            /// @brief Default constructor creates an "end" iterator.
            ///
            /// This constructor initializes the iterator to the end of the free ranges,
            explicit DOCK_ALLOC_FORCE_INLINE FreeRangeIterator(
                const IntervalGapTree<kExpectedMaxTreeHeight>& tree) noexcept
                : iterator_(tree.EndFreeRanges())
            {
            }

            /// @brief Constructs a FreeRangeIterator for the specified tree and search parameters.
            ///
            /// This constructor initializes the iterator to search for free ranges of a specified length
            /// within a given range of segments.
            ///
            /// @param tree The segment tree to search within.
            /// @param required_length The minimum length of the free segment to find.
            /// @param search_start The starting index of the search range (inclusive).
            /// @param search_end The ending index of the search range (exclusive).
            explicit DOCK_ALLOC_FORCE_INLINE FreeRangeIterator(const IntervalGapTree<kExpectedMaxTreeHeight>& tree,
                                                               const size_t required_length,
                                                               const size_t search_start,
                                                               const size_t search_end) noexcept
                : iterator_(tree.BeginFreeRanges(required_length, search_start, search_end))
            {
            }

            IntervalGapTree<kExpectedMaxTreeHeight>::FreeRangeIterator iterator_;
        };

        /// @brief Returns an iterator to the beginning of free ranges of a specified length.
        ///
        /// This method returns an iterator that points to the first valid starting position
        /// for a contiguous run of free segments of the specified length within the quay.
        ///
        /// @param required_length The minimum length of the free segment to find.
        /// @param search_start The starting index of the search range (inclusive).
        /// @param search_end The ending index of the search range (exclusive).
        ///
        /// @pre search_start <= search_end
        /// @pre search_end <= GetQuaySegmentCount()
        ///
        /// @return A \c FreeRangeIterator that starts at the first valid position of a free segment.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeIterator BeginFreeRanges(const size_t required_length,
            const size_t search_start, const size_t search_end) const noexcept
        {
            return FreeRangeIterator(quay_segment_tree_, required_length, search_start, search_end);
        }

        /// @brief Returns an iterator to the end of free ranges.
        ///
        /// This method returns an iterator that signifies the end of the valid free range positions,
        /// indicating that there are no more valid starting positions to iterate over.
        ///
        /// @return A \c FreeRangeIterator that acts as an "end" iterator.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeIterator EndFreeRanges() const noexcept
        {
            return FreeRangeIterator(quay_segment_tree_);
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
            /// This constructor initializes the view with the specified quay and search parameters.
            ///
            /// @param quay The quay to search within.
            /// @param required_length The minimum length of the free segment to find.
            /// @param search_start The starting index of the search range (inclusive).
            /// @param search_end The ending index of the search range (exclusive).
            ///
            /// @pre search_start <= search_end
            /// @pre search_end <= quay->GetQuaySegmentCount()
            DOCK_ALLOC_FORCE_INLINE FreeRangeView(const Quay* quay, const size_t required_length,
                                                  const size_t search_start,
                                                  const size_t search_end)
                : quay_(quay),
                  required_length_(required_length),
                  search_start_(search_start),
                  search_end_(search_end)
            {
            }

            /// @brief Returns an iterator to the beginning of the valid free range positions.
            ///
            /// This method returns an iterator that points to the first valid starting position
            /// for a contiguous run of free segments of the specified length within the range defined by
            /// \p search_start and \p search_end.
            ///
            /// @return A \c FreeRangeIterator that starts at the first valid position of a
            /// free segment of the required length.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE auto begin() const
            {
                return quay_->BeginFreeRanges(required_length_, search_start_, search_end_);
            }

            /// @brief Returns an iterator to the end of the valid free range positions.
            ///
            /// This method returns an iterator that signifies the end of the valid free range positions,
            /// indicating that there are no more valid starting positions to iterate over.
            ///
            /// @return A \c FreeRangeIterator that acts as an "end" iterator.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE auto end() const
            {
                return quay_->EndFreeRanges();
            }

        private:
            const Quay* quay_;
            size_t required_length_;
            size_t search_start_;
            size_t search_end_;
        };

        /// @brief Finds free ranges of a specified length within the quay.
        ///
        /// This method constructs a view that allows iteration over all valid starting positions
        /// for a contiguous run of free segments of the specified length within the quay.
        ///
        /// @param required_length The minimum length of the free segment to find.
        /// @param search_start The starting index of the search range (inclusive).
        /// @param search_end The ending index of the search range (exclusive).
        ///
        /// @pre search_start <= search_end
        /// @pre search_end <= GetQuaySegmentCount()
        ///
        /// @return A \c FreeRangeView that can be used in a range-based for loop to iterate over free ranges.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeView FindFreeRanges(const size_t required_length,
                                                                           const size_t search_start,
                                                                           const size_t search_end) const noexcept
        {
            return {this, required_length, search_start, search_end};
        }

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
        ///
        /// @pre segment_range.GetEnd() <= GetQuaySegmentCount()
        DOCK_ALLOC_FORCE_INLINE void Occupy(const core::SegmentRange<size_t>& segment_range) noexcept
        {
            DCHECK_LE(segment_range.GetEnd(), GetQuaySegmentCount()) << "End must not exceed number of segments";

            quay_segment_tree_.Occupy(segment_range.GetStart(), segment_range.GetEnd());
        }

        /// @brief Frees a specified range of segments in the quay.
        ///
        /// This method marks the specified range of segments as free.
        ///
        /// @param segment_range The range of segments to free, specified as a \c core::SegmentRange.
        ///
        /// @pre segment_range.GetEnd() <= GetQuaySegmentCount()
        DOCK_ALLOC_FORCE_INLINE void Free(const core::SegmentRange<size_t>& segment_range) noexcept
        {
            DCHECK_LE(segment_range.GetEnd(), GetQuaySegmentCount()) << "End must not exceed number of segments";

            quay_segment_tree_.Free(segment_range.GetStart(), segment_range.GetEnd());
        }

        /// @brief Checks if a specified range of segments is free.
        ///
        /// This method checks if all segments in the specified range are free.
        ///
        /// @param segment_range The range of segments to check, specified as a \c core::SegmentRange.
        ///
        /// @pre segment_range.GetEnd() <= GetQuaySegmentCount()
        ///
        /// @return \c true if every segment in the range is free, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool IsRangeFree(
            const core::SegmentRange<size_t>& segment_range) const noexcept
        {
            DCHECK_LE(segment_range.GetEnd(), GetQuaySegmentCount()) << "End must not exceed number of segments";

            return quay_segment_tree_.IsRangeFree(segment_range.GetStart(), segment_range.GetEnd());
        }

        /// @brief Checks if a specified range of segments is occupied.
        ///
        /// This method checks if all segments in the specified range are occupied.
        ///
        /// @param segment_range The range of segments to check, specified as a \c core::SegmentRange.
        ///
        /// @pre segment_range.GetEnd() <= GetQuaySegmentCount()
        ///
        /// @return \c true if every segment in the range is occupied, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool IsRangeOccupied(
            const core::SegmentRange<size_t>& segment_range) const noexcept
        {
            DCHECK_LE(segment_range.GetEnd(), GetQuaySegmentCount()) << "End must not exceed number of segments";

            return quay_segment_tree_.IsRangeOccupied(segment_range.GetStart(), segment_range.GetEnd());
        }

        /// @brief Finds the starting position of the first free contiguous block of at least size k.
        ///
        /// This method searches for a free segment of at least the specified size within the quay.
        ///
        /// @param k The minimum required length of the free segment.
        ///
        /// @pre k <= GetQuaySegmentCount()
        ///
        /// @return A \c std::optional containing the starting position if a suitable segment is found;
        /// \c std::nullopt otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE std::optional<size_t> FindFirstFreeRange(const size_t k) const noexcept
        {
            DCHECK_LE(k, GetQuaySegmentCount()) << "k must not exceed number of segments";

            return quay_segment_tree_.FindFirstFreeRange(k);
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
        /// @pre k <= GetQuaySegmentCount()
        /// @pre search_range.GetEnd() <= GetQuaySegmentCount()
        ///
        /// @return A \c std::optional containing the starting position if a suitable segment is found;
        /// \c std::nullopt otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE std::optional<size_t> FindFirstFreeRange(const size_t k,
            const core::SegmentRange<size_t>&
            search_range) const noexcept
        {
            DCHECK_LE(k, GetQuaySegmentCount()) << "k must not exceed number of segments";
            DCHECK_LE(search_range.GetEnd(), GetQuaySegmentCount())
                << "End of search range must not exceed number of segments";

            return quay_segment_tree_.FindFirstFreeRange(k, search_range.GetStart(), search_range.GetEnd());
        }

        /// @brief Gets the number of segments in the quay.
        ///
        /// This method returns the total number of segments managed by the quay segment tree.
        ///
        /// @return The number of segments in the quay as a \c size_t.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t GetQuaySegmentCount() const noexcept
        {
            return static_cast<size_t>(quay_segment_tree_.GetSegmentCount());
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
        IntervalGapTree<kExpectedMaxTreeHeight> quay_segment_tree_;
    };

    /// @brief Quay class template specialization for the \c BitVector backend.
    ///
    /// This specialization uses a bit vector to manage occupancy of segments in the quay.
    template <>
    class Quay<QuayBackend::BitVector>
    {
    public:
        /// @brief Type alias for the word type used in the bit vector.
        ///
        /// \c uint64_t makes the most sense here, as it uses the most bits.
        using WordType = uint64_t;

        class FreeRangeIterator
        {
        public:
            using value_type = size_t;
            using reference = const size_t&;
            using iterator_category = std::forward_iterator_tag;

            /// @brief Dereferences the iterator to get the current free range starting position.
            ///
            /// Defaults to the current position of the iterator, which is the starting index
            /// of the free range that matches the required length.
            ///
            /// @pre The iterator must not be an "end" iterator.
            DOCK_ALLOC_FORCE_INLINE reference operator*() const noexcept
            {
                return *iterator_;
            }

            /// @brief Increments the iterator to the next free range starting position.
            ///
            /// This method advances the iterator to the next position in the segment tree
            /// that contains a free segment of at least the required length.
            ///
            /// @pre The iterator must not be an "end" iterator.
            DOCK_ALLOC_FORCE_INLINE FreeRangeIterator& operator++() noexcept
            {
                ++iterator_;
                return *this;
            }

            /// @brief Post-increment operator for the iterator.
            ///
            /// This method returns a copy of the iterator before incrementing it,
            /// allowing for postfix increment behavior.
            ///
            /// @pre The iterator must not be an "end" iterator.
            DOCK_ALLOC_FORCE_INLINE FreeRangeIterator operator++(int) noexcept
            {
                auto tmp = *this;
                ++iterator_;
                return tmp;
            }

            /// @brief Compares two iterators for equality.
            ///
            /// This method checks if the two iterators point to the same position in the bit vector.
            ///
            /// @param other The other iterator to compare against.
            ///
            /// @return \c true if both iterators point to the same position, \c false otherwise.
            DOCK_ALLOC_FORCE_INLINE bool operator==(const FreeRangeIterator& other) const noexcept
            {
                return iterator_ == other.iterator_;
            }

            /// @brief Compares two iterators for inequality.
            ///
            /// This method checks if two iterators do not point to the same position in the bit vector.
            ///
            /// @param other The other iterator to compare against.
            ///
            /// @return \c true if the iterators point to different positions, \c false if they are equal.
            DOCK_ALLOC_FORCE_INLINE bool operator!=(const FreeRangeIterator& other) const noexcept
            {
                return !(*this == other);
            }

        private:
            friend class Quay;

            /// @brief Default constructor creates an "end" iterator.
            ///
            /// This constructor initializes the iterator to the end of the free ranges,
            /// meaning it will not yield any valid positions.
            ///
            /// @param bit_vector The bit vector to iterate over.
            explicit DOCK_ALLOC_FORCE_INLINE FreeRangeIterator(const BitVector<WordType>& bit_vector) noexcept
                : iterator_(bit_vector.EndFreeRanges())
            {
            }

            /// @brief Constructs a FreeRangeIterator for the specified bit vector and search parameters.
            ///
            /// This constructor initializes the iterator to search for free ranges of a specified length
            /// within a given range of segments.
            ///
            /// @param bit_vector The bit vector to search within.
            /// @param required_length The minimum length of the free segment to find.
            /// @param search_start The starting index of the search range (inclusive).
            /// @param search_end The ending index of the search range (exclusive).
            ///
            /// @pre search_start <= search_end
            /// @pre search_end <= GetQuaySegmentCount()
            explicit DOCK_ALLOC_FORCE_INLINE FreeRangeIterator(const BitVector<WordType>& bit_vector,
                                                               const size_t required_length,
                                                               const size_t search_start,
                                                               const size_t search_end) noexcept
                : iterator_(bit_vector.BeginFreeRanges(required_length, search_start, search_end))
            {
            }

            BitVector<WordType>::FreeRangeIterator iterator_;
        };

        /// @brief Returns an iterator to the beginning of free ranges of a specified length.
        ///
        /// This method returns an iterator that points to the first valid starting position
        /// for a contiguous run of free segments of the specified length within the quay.
        ///
        /// @param required_length The minimum length of the free segment to find.
        /// @param search_start The starting index of the search range (inclusive).
        /// @param search_end The ending index of the search range (exclusive).
        ///
        /// @pre search_start <= search_end
        /// @pre search_end <= GetQuaySegmentCount()
        ///
        /// @return A \c FreeRangeIterator that starts at the first valid position of a free segment.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeIterator BeginFreeRanges(
            const size_t required_length, const size_t search_start, const size_t search_end) const noexcept
        {
            return FreeRangeIterator(bit_vector_, required_length, search_start, search_end);
        }

        /// @brief Returns an iterator to the end of free ranges.
        ///
        /// This method returns an iterator that signifies the end of the valid free range positions,
        /// indicating that there are no more valid starting positions to iterate over.
        ///
        /// @return A \c FreeRangeIterator that acts as an "end" iterator.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeIterator EndFreeRanges() const noexcept
        {
            return FreeRangeIterator(bit_vector_);
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
            /// This constructor initializes the view with the specified quay and search parameters.
            ///
            /// @param quay The quay to search within.
            /// @param required_length The minimum length of the free segment to find.
            /// @param search_start The starting index of the search range (inclusive).
            /// @param search_end The ending index of the search range (exclusive).
            ///
            /// @pre search_start <= search_end
            /// @pre search_end <= quay->GetQuaySegmentCount()
            DOCK_ALLOC_FORCE_INLINE FreeRangeView(const Quay* quay, const size_t required_length,
                                                  const size_t search_start,
                                                  const size_t search_end)
                : quay_(quay),
                  required_length_(required_length),
                  search_start_(search_start),
                  search_end_(search_end)
            {
            }

            /// @brief Returns an iterator to the beginning of the valid free range positions.
            ///
            /// This method returns an iterator that points to the first valid starting position
            /// for a contiguous run of free segments of the specified length within the range defined by
            /// \p search_start and \p search_end.
            ///
            /// @return A \c FreeRangeIterator that starts at the first valid position of a
            /// free segment of the required length.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE auto begin() const
            {
                return quay_->BeginFreeRanges(required_length_, search_start_, search_end_);
            }

            /// @brief Returns an iterator to the end of the valid free range positions.
            ///
            /// This method returns an iterator that signifies the end of the valid free range positions,
            /// indicating that there are no more valid starting positions to iterate over.
            ///
            /// @return A \c FreeRangeIterator that acts as an "end" iterator.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE auto end() const
            {
                return quay_->EndFreeRanges();
            }

        private:
            const Quay* quay_;
            size_t required_length_;
            size_t search_start_;
            size_t search_end_;
        };

        /// @brief Finds free ranges of a specified length within the quay.
        ///
        /// This method constructs a view that allows iteration over all valid starting positions
        /// for a contiguous run of free segments of the specified length within the quay.
        ///
        /// @param required_length The minimum length of the free segment to find.
        /// @param search_start The starting index of the search range (inclusive).
        /// @param search_end The ending index of the search range (exclusive).
        ///
        /// @pre search_start <= search_end
        /// @pre search_end <= GetQuaySegmentCount()
        ///
        /// @return A \c FreeRangeView that can be used in a range-based for loop to iterate over free ranges.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeView FindFreeRanges(const size_t required_length,
                                                                           const size_t search_start,
                                                                           const size_t search_end) const noexcept
        {
            return {this, required_length, search_start, search_end};
        }

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
        ///
        /// @pre segment_range.GetEnd() <= GetQuaySegmentCount()
        DOCK_ALLOC_FORCE_INLINE void Occupy(const core::SegmentRange<size_t>& segment_range) noexcept
        {
            DCHECK_LE(segment_range.GetEnd(), GetQuaySegmentCount()) << "End must not exceed number of segments";

            bit_vector_.ClearBits(static_cast<size_t>(segment_range.GetStart()),
                                  static_cast<size_t>(segment_range.GetEnd()));
        }

        /// @brief Frees a specified range of segments in the quay.
        ///
        /// This method marks the specified range of segments as free.
        ///
        /// @param segment_range The range of segments to free, specified as a \c core::SegmentRange.
        ///
        /// @pre segment_range.GetEnd() <= GetQuaySegmentCount()
        DOCK_ALLOC_FORCE_INLINE void Free(const core::SegmentRange<size_t>& segment_range) noexcept
        {
            DCHECK_LE(segment_range.GetEnd(), GetQuaySegmentCount()) << "End must not exceed number of segments";

            bit_vector_.SetBits(static_cast<size_t>(segment_range.GetStart()),
                                static_cast<size_t>(segment_range.GetEnd()));
        }

        /// @brief Checks if a specified range of segments is free.
        ///
        /// This method checks if all segments in the specified range are free.
        ///
        /// @param segment_range The range of segments to check, specified as a \c core::SegmentRange.
        ///
        /// @pre segment_range.GetEnd() <= GetQuaySegmentCount()
        ///
        /// @return \c true if every segment in the range is free, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool IsRangeFree(
            const core::SegmentRange<size_t>& segment_range) const noexcept
        {
            DCHECK_LE(segment_range.GetEnd(), GetQuaySegmentCount()) << "End must not exceed number of segments";

            return bit_vector_.AreBitsSet(static_cast<size_t>(segment_range.GetStart()),
                                          static_cast<size_t>(segment_range.GetEnd()));
        }

        /// @brief Checks if a specified range of segments is occupied.
        ///
        /// This method checks if all segments in the specified range are occupied.
        ///
        /// @param segment_range The range of segments to check, specified as a \c core::SegmentRange.
        ///
        /// @pre segment_range.GetEnd() <= GetQuaySegmentCount()
        ///
        /// @return \c true if every segment in the range is occupied, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool IsRangeOccupied(
            const core::SegmentRange<size_t>& segment_range) const noexcept
        {
            DCHECK_LE(segment_range.GetEnd(), GetQuaySegmentCount()) << "End must not exceed number of segments";

            return bit_vector_.AreBitsClear(static_cast<size_t>(segment_range.GetStart()),
                                            static_cast<size_t>(segment_range.GetEnd()));
        }

        /// @brief Finds the starting position of the first free contiguous block of at least size k.
        ///
        /// This method searches for a free segment of at least the specified size within the quay.
        ///
        /// @param k The minimum required length of the free segment.
        ///
        /// @pre k <= GetQuaySegmentCount()
        ///
        /// @return A \c std::optional containing the starting position if a suitable segment is found;
        /// \c std::nullopt otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE std::optional<size_t> FindFirstFreeRange(const size_t k) const noexcept
        {
            DCHECK_LE(k, GetQuaySegmentCount()) << "k must not exceed number of segments";
            return bit_vector_.FindFirstClearRange(0, GetQuaySegmentCount(), k);
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
        /// @pre k <= GetQuaySegmentCount()
        /// @pre search_range.GetEnd() <= GetQuaySegmentCount()
        ///
        /// @return A \c std::optional containing the starting position if a suitable segment is found;
        /// \c std::nullopt otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE std::optional<size_t> FindFirstFreeRange(const size_t k,
            const core::SegmentRange<size_t>&
            search_range) const noexcept
        {
            DCHECK_LE(k, GetQuaySegmentCount()) << "k must not exceed number of segments";
            DCHECK_LE(search_range.GetEnd(), GetQuaySegmentCount())
                << "End of search range must not exceed number of segments";

            return bit_vector_.FindFirstClearRange(static_cast<size_t>(search_range.GetStart()),
                                                   static_cast<size_t>(search_range.GetEnd()), k);
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
