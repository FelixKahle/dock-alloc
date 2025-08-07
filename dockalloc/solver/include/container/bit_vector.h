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

#ifndef DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_H_
#define DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_H_

#include <concepts>
#include <limits>
#include <optional>
#include <algorithm>
#include <bit>
#include <vector>
#include "absl/log/check.h"
#include "dockalloc/core/miscellaneous/core_defines.h"
#include "dockalloc/solver/miscellaneous/config.h"
#if DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD
#include "xsimd/xsimd.hpp"
#endif

namespace dockalloc::solver
{
    /// @brief A vector-like container for managing a collection of bits.
    ///
    /// This class provides a dynamic array of bits, allowing for efficient storage and manipulation
    /// of individual bits. It supports operations such as setting, clearing, and checking the state of bits,
    /// as well as resizing the vector. The bits are stored in a vector of words, where each word is of type \c WordType.
    /// The class is designed to be efficient in terms of memory usage and performance,
    /// leveraging the properties of the underlying word type to optimize bit operations.
    /// SIMD operations are used for performance optimization when available.
    ///
    /// @tparam WordType The unsigned integral type used to store the bits. It must be an unsigned integral type.
    template <typename WordType>
        requires std::unsigned_integral<WordType>
    class BitVector
    {
    public:
        /// @brief A reference to a single bit in the bit vector
        ///
        /// This class provides a reference to a single bit in the bit vector, allowing for
        /// read and write access to the bit. It is designed to be lightweight and efficient,
        /// providing a simple interface for manipulating individual bits; mainly used
        /// for the \c operator[] overload.
        class BitReference
        {
        public:
            /// @brief Constructor.
            ///
            /// This constructor initializes a \c BitReference object with the specified word and bit index.
            ///
            /// @param word The reference to the storage word.
            /// @param bit The index of the bit within the word.
            constexpr DOCK_ALLOC_FORCE_INLINE BitReference(WordType& word, const size_t bit)
                : word_(word), bit_(bit)
            {
            }

            // ReSharper disable once CppNonExplicitConversionOperator
            /// @brief Conversion operator to \c bool.
            ///
            /// This operator enables implicit or explicit conversion of the \c BitReference
            /// to a \c bool value. It returns \c true if the referenced bit is set (i.e., equal to 1),
            /// and \c false otherwise.
            ///
            /// @return \c true if the bit is set; \c false if the bit is clear.
            ///
            /// @note This operator does not modify the bit. It only reads its current value.
            constexpr DOCK_ALLOC_FORCE_INLINE operator bool() const noexcept // NOLINT(*-explicit-constructor)
            {
                return word_ >> bit_ & WordType{1};
            }

            /// @brief Overload of the assignment operator for boolean values.
            ///
            /// Assigns the given boolean value to the referenced bit. If \c value is \c true,
            /// the bit is set to 1; if \c false, the bit is cleared to 0.
            ///
            /// @param value The boolean value to assign to the bit.
            /// @return A reference to this \c BitReference, allowing for chained assignments.
            ///
            /// @note This operation modifies the underlying storage word by setting or clearing the bit.
            constexpr DOCK_ALLOC_FORCE_INLINE BitReference& operator=(const bool value) noexcept
            {
                const WordType mask = WordType{1} << bit_;
                word_ = (word_ & ~mask) | (WordType(value) << bit_);
                return *this;
            }

            /// @brief Overload of the copy assignment operator.
            ///
            /// Assigns the value of another \c BitReference to this bit. The assignment is based on the
            /// boolean value of the other reference (i.e., whether its bit is set or not).
            ///
            /// @param other The \c BitReference from which to copy the bit value.
            /// @return A reference to this \c BitReference, allowing for chained assignments.
            ///
            /// @note This does not copy the underlying reference — only the bit value is copied.
            /// @note Implicit conversion to \c bool is allowed and intended.
            constexpr DOCK_ALLOC_FORCE_INLINE BitReference& operator=(const BitReference& other) noexcept
            {
                *this = static_cast<bool>(other);
                return *this;
            }

        private:
            WordType& word_;
            size_t bit_;
        };

        /// @brief An iterator for the \c BitVector class.
        ///
        /// This iterator enables read-write traversal over the individual bits in a \c BitVector.
        /// Dereferencing yields a \c BitReference, allowing for both inspection and assignment.
        ///
        /// @note This iterator satisfies the requirements of a random-access iterator.
        /// It does not provide a pointer type, as \c BitReference is a proxy object.
        class BitVectorIterator
        {
        public:
            /// @brief Difference between iterator positions.
            using difference_type = std::ptrdiff_t;

            /// @brief The value type yielded (via conversion).
            using value_type = bool;

            /// @brief Reference type (proxy to a single bit).
            using reference = BitReference;

            /// @brief Not applicable for proxy types.
            using pointer = void;

            /// @brief The iterator category.
            using iterator_category = std::random_access_iterator_tag;

            /// @brief Constructs a new iterator at a given index.
            ///
            /// @param data Pointer to the bit storage.
            /// @param index Bit index the iterator points to.
            ///
            /// @pre data != nullptr
            explicit DOCK_ALLOC_FORCE_INLINE BitVectorIterator(WordType* data, const size_t index) noexcept
                : data_(data), index_(index)
            {
                DCHECK_NE(data, nullptr);
            }

            /// @brief Dereference operator.
            ///
            /// Returns a proxy reference to the bit at the current index.
            ///
            /// @return A \c BitReference proxy to the current bit.
            DOCK_ALLOC_FORCE_INLINE BitReference operator*() const noexcept
            {
                const size_t word = index_ / kBitsPerWord;
                const size_t bit = index_ % kBitsPerWord;
                return BitReference(data_[word], bit);
            }

            /// @brief Pre-increment operator.
            ///
            /// Pre-increments the iterator to point to the next bit in the span.
            ///
            /// @return Reference to the incremented iterator.
            DOCK_ALLOC_FORCE_INLINE BitVectorIterator& operator++() noexcept
            {
                ++index_;
                return *this;
            }

            /// @brief Post-increment operator.
            ///
            /// Post-increments the iterator to point to the next bit in the span.
            ///
            /// @return Copy of the iterator before increment.
            DOCK_ALLOC_FORCE_INLINE BitVectorIterator operator++(int) noexcept
            {
                BitVectorIterator tmp = *this;
                ++index_;
                return tmp;
            }

            /// @brief Pre-decrement operator.
            ///
            /// Pre-decrements the iterator to point to the previous bit in the span.
            ///
            /// @return Reference to the decremented iterator.
            DOCK_ALLOC_FORCE_INLINE BitVectorIterator& operator--() noexcept
            {
                --index_;
                return *this;
            }

            /// @brief Post-decrement operator.
            ///
            /// Post-decrements the iterator to point to the previous bit in the span.
            ///
            /// @return Copy of the iterator before decrement.
            DOCK_ALLOC_FORCE_INLINE BitVectorIterator operator--(int) noexcept
            {
                BitVectorIterator tmp = *this;
                --index_;
                return tmp;
            }

            /// @brief Compound addition.
            ///
            /// Advances the iterator by the specified number of steps.
            ///
            /// @param n Number of steps to advance.
            ///
            /// @return Reference to the advanced iterator.
            DOCK_ALLOC_FORCE_INLINE BitVectorIterator& operator+=(const difference_type n) noexcept
            {
                index_ += n;
                return *this;
            }

            /// @brief Compound subtraction.
            ///
            /// Retreats the iterator by the specified number of steps.
            ///
            /// @param n Number of steps to retreat.
            ///
            /// @return Reference to the retreated iterator.
            DOCK_ALLOC_FORCE_INLINE BitVectorIterator& operator-=(const difference_type n) noexcept
            {
                index_ -= n;
                return *this;
            }

            /// @brief Iterator addition.
            ///
            /// Advances the iterator by the specified number of positions.
            ///
            /// @param n Number of positions to advance.
            ///
            /// @return New iterator advanced by \c n.
            DOCK_ALLOC_FORCE_INLINE BitVectorIterator operator+(const difference_type n) const noexcept
            {
                return iterator(data_, index_ + n);
            }

            /// @brief Iterator subtraction.
            ///
            /// Retreats the iterator by the specified number of positions.
            ///
            /// @param n Number of positions to retreat.
            ///
            /// @return New iterator retreated by \c n.
            DOCK_ALLOC_FORCE_INLINE BitVectorIterator operator-(const difference_type n) const noexcept
            {
                return iterator(data_, index_ - n);
            }

            /// @brief Distance between iterators.
            ///
            /// Distance between two iterators in terms of bit positions.
            ///
            /// @param other The other iterator.
            ///
            /// @return Difference in bit positions.
            DOCK_ALLOC_FORCE_INLINE difference_type operator-(const BitVectorIterator& other) const noexcept
            {
                return index_ - other.index_;
            }

            /// @brief Equality comparison.
            ///
            /// Compares two iterators to check if they point to the same bit.
            ///
            /// @param other The other iterator.
            ///
            /// @return \c true if both iterators point to the same bit.
            bool operator==(const BitVectorIterator& other) const noexcept
            {
                return index_ == other.index_;
            }

            /// @brief Inequality comparison.
            ///
            /// Compares two iterators to check if they point to different bits.
            ///
            /// @param other The other iterator.
            ///
            /// @return \c true if iterators point to different bits.
            DOCK_ALLOC_FORCE_INLINE bool operator!=(const BitVectorIterator& other) const noexcept
            {
                return index_ != other.index_;
            }

        private:
            WordType* data_;
            size_t index_;
        };

        /// @brief A const iterator for the \c BitVector class.
        ///
        /// This iterator enables read-only traversal over the individual bits in a \c BitVector.
        /// Dereferencing yields a boolean value, indicating whether the bit is set or not.
        class ConstBitVectorIterator
        {
        public:
            /// @brief Difference between iterator positions.
            using difference_type = std::ptrdiff_t;

            /// @brief The value type yielded.
            using value_type = bool;

            /// @brief Reference type.
            using reference = bool;

            /// @brief Not applicable.
            using pointer = void;

            /// @brief The iterator category.
            using iterator_category = std::random_access_iterator_tag;

            /// @brief Constructs a const iterator at a given bit position.
            ///
            /// This constructor initializes a \c ConstBitVectorIterator to point to a specific bit
            /// in the bit span.
            ///
            /// @param data Pointer to the beginning of the storage array.
            /// @param index Bit index the iterator points to.
            ///
            /// @pre data != nullptr
            explicit DOCK_ALLOC_FORCE_INLINE ConstBitVectorIterator(const WordType* data, const size_t index) noexcept
                : data_(data), index_(index)
            {
                DCHECK_NE(data, nullptr);
            }

            /// @brief Returns the boolean value of the current bit.
            ///
            /// This operator dereferences the iterator to yield the value of the bit at the current position.
            ///
            /// @return true if the bit at the current position is set; false if clear.
            DOCK_ALLOC_FORCE_INLINE bool operator*() const noexcept
            {
                size_t word = index_ / kBitsPerWord;
                size_t bit = index_ % kBitsPerWord;
                return (data_[word] >> bit & WordType{1}) != 0;
            }

            /// @brief Advances iterator to the next bit (pre-increment).
            ///
            /// Pre-increments the iterator to point to the next bit in the span.
            ///
            /// @return Reference to the incremented iterator.
            DOCK_ALLOC_FORCE_INLINE ConstBitVectorIterator& operator++() noexcept
            {
                ++index_;
                return *this;
            }

            /// @brief Advances iterator to the next bit (post-increment).
            ///
            /// Post-increments the iterator to point to the next bit in the span.
            ///
            /// @return Iterator state before increment.
            DOCK_ALLOC_FORCE_INLINE ConstBitVectorIterator operator++(int) noexcept
            {
                auto tmp = *this;
                ++index_;
                return tmp;
            }

            /// @brief Moves iterator to the previous bit (pre-decrement).
            ///
            /// Pre-decrements the iterator to point to the previous bit in the span.
            ///
            /// @return Reference to the decremented iterator.
            DOCK_ALLOC_FORCE_INLINE ConstBitVectorIterator& operator--() noexcept
            {
                --index_;
                return *this;
            }

            /// @brief Moves iterator to the previous bit (post-decrement).
            ///
            /// Post-decrements the iterator to point to the previous bit in the span.
            ///
            /// @return Iterator state before decrement.
            DOCK_ALLOC_FORCE_INLINE ConstBitVectorIterator operator--(int) noexcept
            {
                auto tmp = *this;
                --index_;
                return tmp;
            }

            /// @brief Advances iterator by a number of bits.
            ///
            /// This operator allows the iterator to be advanced by a specified number of bits.
            ///
            /// @param n Number of bits to advance.
            ///
            /// @return Reference to the iterator after advancing.
            DOCK_ALLOC_FORCE_INLINE ConstBitVectorIterator& operator+=(const difference_type n) noexcept
            {
                index_ += n;
                return *this;
            }

            /// @brief Retreats iterator by a number of bits.
            ///
            /// This operator allows the iterator to be retreated by a specified number of bits.
            ///
            /// @param n Number of bits to retreat.
            ///
            /// @return Reference to the iterator after retreating.
            DOCK_ALLOC_FORCE_INLINE ConstBitVectorIterator& operator-=(const difference_type n) noexcept
            {
                index_ -= n;
                return *this;
            }

            /// @brief Returns a new iterator advanced by n bits.
            ///
            /// This operator allows the iterator to be advanced by a specified number of bits.
            ///
            /// @param n Number of bits to advance.
            ///
            /// @return New iterator at position index + n.
            ConstBitVectorIterator operator+(const difference_type n) const noexcept
            {
                return ConstBitVectorIterator(data_, index_ + n);
            }

            /// @brief Returns a new iterator retreated by n bits.
            ///
            /// This operator allows the iterator to be retreated by a specified number of bits.
            ///
            /// @param n Number of bits to retreat.
            ///
            /// @return New iterator at position index - n.
            DOCK_ALLOC_FORCE_INLINE ConstBitVectorIterator operator-(const difference_type n) const noexcept
            {
                return ConstBitVectorIterator(data_, index_ - n);
            }

            /// @brief Computes the distance between two iterators.
            ///
            /// This operator computes the difference in bit positions between two iterators.
            ///
            /// @param other Another iterator to compare to.
            ///
            /// @return Difference in bit positions (this - other).
            DOCK_ALLOC_FORCE_INLINE difference_type operator-(const ConstBitVectorIterator& other) const noexcept
            {
                return static_cast<difference_type>(index_) - static_cast<difference_type>(other.index_);
            }

            /// @brief Checks equality of two iterators.
            ///
            /// This operator checks if two iterators point to the same bit index.
            ///
            /// @param other Another iterator to compare.
            ///
            /// @return true if both iterators point to the same bit index.
            bool operator==(const ConstBitVectorIterator& other) const noexcept { return index_ == other.index_; }

            /// @brief Checks inequality of two iterators.
            ///
            /// This operator checks if two iterators point to different bit indices.
            ///
            /// @param other Another iterator to compare.
            ///
            /// @return true if iterators point to different bit indices.
            bool operator!=(const ConstBitVectorIterator& other) const noexcept { return index_ != other.index_; }

        private:
            const WordType* data_;
            size_t index_;
        };

        /// @brief An efficient forward iterator that finds all valid starting positions for a contiguous run of clear bits.
        ///
        /// This iterator is designed for high performance by operating on whole words of bits at a time.
        /// It functions as a state machine that first searches for a large, contiguous block of clear bits
        /// ("free block") that is at least as long as the requested run length. Once a block is found, the
        /// iterator enters a yield phase, returning each possible starting position within that block one by one.
        /// When the current block is exhausted, it automatically resumes the search phase from where it left off,
        /// ensuring that the entire \c BitVector is scanned only once.
        ///
        /// @note This iterator satisfies the \c std::forward_iterator_tag. It can only be moved forward \c operator++
        /// and does not support decrementing, distance calculations, or other random-access features.
        class FreeRangeIterator
        {
        public:
            using value_type = size_t;
            using reference = const size_t&;
            using iterator_category = std::forward_iterator_tag;

            /// @brief Checks if the iterator is in the end state.
            ///
            /// This method checks if the iterator has reached the end of the valid free ranges.
            ///
            /// @return \c true if the iterator is in the end state, \c false otherwise.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool IsEnd() const noexcept
            {
                return is_end_;
            }

            /// @brief Dereference operator to get the current valid starting position.
            ///
            /// This operator returns the current position in the iteration, which is the starting index
            /// of a valid free range of bits.
            ///
            /// @pre !IsEnd()
            ///
            /// @return The current valid starting position for a free range.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE const size_t& operator*() const noexcept
            {
                DCHECK(!is_end_);
                return current_yield_pos_;
            }

            /// @brief Pre-increment operator to advance to the next valid position.
            ///
            /// This operator advances the iterator to the next valid starting position for a free range.
            ///
            /// @return Reference to the incremented iterator.
            DOCK_ALLOC_FORCE_INLINE FreeRangeIterator& operator++() noexcept
            {
                AdvanceToNextPosition();
                return *this;
            }

            /// @brief Post-increment operator.
            ///
            /// This operator advances the iterator to the next valid position and returns
            /// the previous position.
            ///
            /// @return A copy of the iterator before incrementing.
            DOCK_ALLOC_FORCE_INLINE FreeRangeIterator operator++(int) noexcept
            {
                FreeRangeIterator tmp = *this;
                AdvanceToNextPosition();
                return tmp;
            }

            /// @brief Equality comparison.
            ///
            /// This operator checks if two iterators are equal, meaning they point to the same position
            /// or both are in the end state.
            ///
            /// @param other The other iterator to compare against.
            ///
            /// @return \c true if both iterators are equal, \c false otherwise.
            DOCK_ALLOC_FORCE_INLINE bool operator==(const FreeRangeIterator& other) const noexcept
            {
                if (is_end_ && other.is_end_)
                {
                    return true;
                }
                if (is_end_ != other.is_end_)
                {
                    return false;
                }
                return bit_vector_ == other.bit_vector_ && search_length_ == other.search_length_ && current_yield_pos_
                    == other.current_yield_pos_;
            }

            /// @brief Inequality comparison.
            ///
            /// This operator checks if two iterators are not equal, meaning they point to different positions
            /// or one is in the end state while the other is not.
            ///
            /// @param other The other iterator to compare against.
            bool operator!=(const FreeRangeIterator& other) const noexcept
            {
                return !(*this == other);
            }

        private:
            friend class BitVector;

            /// @brief Constructor for the begin iterator.
            ///
            /// This constructor immediately kicks off the search for the first valid free range.
            /// If no range is found, the constructed iterator will be equal to the end iterator.
            ///
            /// @param bv Pointer to the BitVector to iterate over.
            /// @param search_len The number of consecutive clear bits to find.
            /// @param from The starting bit index of the search (inclusive).
            /// @param to The ending bit index of the search (exclusive).
            ///
            /// @pre bv != nullptr
            /// @pre from <= to
            /// @pre to <= bv->GetBitCount()
            DOCK_ALLOC_FORCE_INLINE FreeRangeIterator(const BitVector* bv, const size_t search_len, const size_t from,
                                                      const size_t to) noexcept
                : bit_vector_(bv),
                  search_length_(search_len),
                  search_from_(from), search_to_(to),
                  current_yield_pos_(0),
                  current_range_start_(0),
                  current_range_end_(0),
                  next_search_pos_(from), is_end_(false)
            {
                DCHECK_NE(bv, nullptr);
                DCHECK_LE(from, to);
                DCHECK_LE(to, bv->GetBitCount());

                if (search_length_ == 0 || from >= to || from + search_length_ > to)
                {
                    is_end_ = true;
                    return;
                }

                AdvanceToNextRange();
            }

            /// @brief Constructor for the end iterator.
            ///
            /// This constructor initializes the iterator to an end state, where no valid positions are available.
            ///
            /// @param bv Pointer to the BitVector to iterate over.
            ///
            /// @pre bv != nullptr
            explicit DOCK_ALLOC_FORCE_INLINE FreeRangeIterator(const BitVector* bv) noexcept
                : bit_vector_(bv),
                  search_length_(0),
                  search_from_(0),
                  search_to_(0),
                  current_yield_pos_(0),
                  current_range_start_(0),
                  current_range_end_(0),
                  next_search_pos_(0),
                  is_end_(true)
            {
                DCHECK_NE(bv, nullptr);
            }

            /// @brief Finds the next free range of bits starting from a given position.
            ///
            /// This function searches for a contiguous block of clear bits that is at
            /// least as long as the specified minimum length.
            ///
            /// @param from The starting position to search from (inclusive).
            /// @param to The end of the search range (exclusive).
            /// @param min_length The minimum length of the free range to find.
            ///
            /// @return An optional pair containing the starting position and length of the found range,
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE std::optional<std::pair<size_t, size_t>> FindNextFreeRange(
                const size_t from, const size_t to, const size_t min_length) const noexcept
            {
                size_t pos = from;
                while (true)
                {
                    pos = FindNextClearBit(pos, to);
                    if (pos + min_length > to)
                    {
                        return std::nullopt;
                    }
                    const size_t run_length = MeasureClearRun(pos, to);

                    if (run_length >= min_length)
                    {
                        return std::make_pair(pos, run_length);
                    }

                    pos += run_length + 1;
                }
            }

            /// @brief Efficiently finds the first clear bit at or after a given position.
            ///
            /// This function searches for the first bit that is clear (0) starting from the specified position.
            ///
            /// @param from The position to start searching from (inclusive).
            /// @param to The end of the search range (exclusive).
            ///
            /// @return The index of the first clear bit, or \c to if none is found.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t FindNextClearBit(
                const size_t from, const size_t to) const noexcept
            {
                if (from >= to)
                {
                    return to;
                }

                size_t word_index = from / kBitsPerWord;
                const size_t bit_index = from % kBitsPerWord;
                const size_t word_count = bit_vector_->GetWordCount();

                if (word_index >= word_count)
                {
                    return to;
                }

                // Check the first (potentially partial) word.
                const WordType first_word = bit_vector_->data_[word_index];
                const WordType mask = HighBitsFrom(bit_index);
                const WordType inverted_masked = ~first_word & mask;

                if (inverted_masked != kAllZeroes)
                {
                    return std::min(to, word_index * kBitsPerWord + std::countr_zero(inverted_masked));
                }

                ++word_index;
                while (word_index < word_count && bit_vector_->data_[word_index] == kAllOnes)
                {
                    ++word_index;
                }

                if (word_index >= word_count)
                {
                    return to;
                }

                return std::min(to, word_index * kBitsPerWord + std::countr_zero(
                                    static_cast<WordType>(~bit_vector_->data_[word_index])));
            }

            /// @brief Measures the length of a contiguous clear run starting from a known clear bit.
            ///
            /// This function counts how many consecutive bits are clear starting from the specified position
            /// until it either reaches the end of the search range or encounters a set bit.
            ///
            ///
            /// @param from The starting position of the clear run (must be a clear bit).
            /// @param to The end of the search range (exclusive).
            ///
            /// @pre from <= to
            /// @pre bit_vector_->IsBitClear(from)
            ///
            /// @return The total length of the clear run.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t MeasureClearRun(
                const size_t from, const size_t to) const noexcept
            {
                DCHECK_LE(from, to);
                DCHECK(bit_vector_->IsBitClear(from));

                const size_t word_count = bit_vector_->GetWordCount();
                const size_t word_index = from / kBitsPerWord;
                const size_t bit_index = from % kBitsPerWord;
                const WordType first_word = bit_vector_->data_[word_index];

                size_t run_in_word = std::countr_zero(static_cast<WordType>(first_word >> bit_index));
                run_in_word = std::min(run_in_word, kBitsPerWord - bit_index);

                if (run_in_word == kBitsPerWord - bit_index)
                {
                    size_t next_word_index = word_index + 1;
                    while (next_word_index < word_count && bit_vector_->data_[next_word_index] == kAllZeroes)
                    {
                        run_in_word += kBitsPerWord;
                        ++next_word_index;
                    }
                    if (next_word_index < word_count)
                    {
                        run_in_word += std::countr_zero(bit_vector_->data_[next_word_index]);
                    }
                }

                return std::min(run_in_word, to - from);
            }

            /// @brief Advances the state machine to the next large free range.
            ///
            /// This function finds the next large contiguous block of clear bits that is at least as long as the
            /// specified search length. It updates the internal state to yield positions within that block
            /// until it is exhausted.
            DOCK_ALLOC_FORCE_INLINE void AdvanceToNextRange() noexcept
            {
                const auto range = FindNextFreeRange(next_search_pos_, search_to_, search_length_);
                if (!range)
                {
                    is_end_ = true;
                    return;
                }

                current_range_start_ = range->first;
                current_range_end_ = range->first + range->second;
                current_yield_pos_ = current_range_start_;
                next_search_pos_ = current_range_end_;
            }

            /// @brief Advances to the next valid position, either within the current range or by finding a new one.
            ///
            /// This function checks if the current position is within the current range.
            /// If it is, it increments the position. If the position exceeds the current range,
            /// it calls \c AdvanceToNextRange() to find a new range and reset the position
            /// to the start of that range.
            DOCK_ALLOC_FORCE_INLINE void AdvanceToNextPosition() noexcept
            {
                if (is_end_)
                {
                    return;
                }

                if (current_yield_pos_ + search_length_ < current_range_end_)
                {
                    ++current_yield_pos_;
                }
                else
                {
                    AdvanceToNextRange();
                }
            }

            const BitVector* bit_vector_;
            size_t search_length_;
            size_t search_from_;
            size_t search_to_;

            size_t current_yield_pos_;
            size_t current_range_start_;
            size_t current_range_end_;
            size_t next_search_pos_;
            bool is_end_;
        };

        /// @brief Creates a forward iterator to find all starting positions for a free range.
        ///
        /// This iterator will yield every valid starting bit index `p` such that all bits in the
        /// range `[p, p + search_length)` are clear.
        ///
        /// @param search_length The number of consecutive clear bits required.
        /// @param from The bit index to start searching from (inclusive).
        /// @param to The bit index to end searching at (exclusive).
        /// @return A `FreeRangeIterator` pointing to the first valid position.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeIterator BeginFreeRanges(
            size_t search_length, size_t from, size_t to) const
        {
            return FreeRangeIterator(this, search_length, from, to);
        }

        /// @brief Creates a forward iterator to find all starting positions for a free range in the entire vector.
        /// @param search_length The number of consecutive clear bits required.
        /// @return A `FreeRangeIterator` pointing to the first valid position.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeIterator BeginFreeRanges(size_t search_length) const
        {
            return FreeRangeIterator(this, search_length, 0, GetBitCount());
        }

        /// @brief Creates an end iterator for free range iteration.
        /// @return The end iterator.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeIterator EndFreeRanges() const
        {
            return FreeRangeIterator(this);
        }

        /// @brief A view that provides a range of valid starting positions for a free range.
        ///
        /// This view allows iteration over all valid starting positions for a contiguous run of clear bits
        /// of a specified length within the BitVector. It is designed to be used with range-based for loops
        /// or algorithms that require a range of valid positions.
        class FreeRangeView
        {
        public:
            /// @brief Constructs a FreeRangeView for a specified \c BitVector and search parameters.
            ///
            /// This constructor initializes the view with the given \c BitVector and search parameters,
            /// allowing iteration over all valid starting positions for a contiguous run of clear bits
            /// of the specified length within the range defined by \p from and \p to.
            ///
            /// @param bv Pointer to the \c BitVector to search.
            /// @param search_len The number of consecutive clear bits to find.
            /// @param from The starting bit index of the search (inclusive).
            FreeRangeView(const BitVector* bv, const size_t search_len, const size_t from, const size_t to)
                : bit_vector_(bv),
                  search_length_(search_len),
                  from_(from), to_(to)
            {
            }

            /// @brief Returns an iterator to the beginning of the valid free range positions.
            ///
            /// This method returns an iterator that points to the first valid starting position
            /// for a contiguous run of clear bits of the specified length within the range defined by \p from and \p to.
            ///
            /// @return A \c FreeRangeIterator that starts at the first valid position of a free segment of the required length.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeIterator begin() const
            {
                return bit_vector_->BeginFreeRanges(search_length_, from_, to_);
            }

            /// @brief Returns an iterator to the end of the valid free range positions.
            ///
            /// This method returns an iterator that signifies the end of the valid free range positions,
            /// indicating that there are no more valid starting positions to iterate over.
            ///
            /// @return A \c FreeRangeIterator that acts as an "end" iterator.
            [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeIterator end() const
            {
                return bit_vector_->EndFreeRanges();
            }

        private:
            const BitVector* bit_vector_;
            size_t search_length_;
            size_t from_;
            size_t to_;
        };

        /// @brief Returns a range-based for-loop compatible view of all free ranges.
        ///
        /// @param search_length The number of consecutive clear bits required.
        ///
        /// @return A view object that can be used in a for-each loop.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeView FindFreeRanges(size_t search_length) const
        {
            return FreeRangeView(this, search_length, 0, GetBitCount());
        }

        /// @brief Returns a range-based for-loop compatible view of all free ranges within a sub-range.
        ///
        /// @param search_length The number of consecutive clear bits required.
        /// @param from The bit index to start searching from (inclusive).
        /// @param to The bit index to end searching at (exclusive).
        ///
        /// @return A view object that can be used in a for-each loop.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE FreeRangeView FindFreeRanges(
            size_t search_length, size_t from, size_t to) const
        {
            return FreeRangeView(this, search_length, from, to);
        }

        /// @brief A \c WordType with all bits set to zeroes.
        static constexpr auto kAllZeroes = static_cast<WordType>(0);

        /// @brief A \c WordType with all bits set to ones.
        static constexpr auto kAllOnes = static_cast<WordType>(~WordType{0});

        /// @brief The count of bits in a single Storage word.
        static constexpr int kBitsPerWord = std::numeric_limits<WordType>::digits;

        /// @brief Constructs a BitVector with the specified number of bits.
        constexpr DOCK_ALLOC_FORCE_INLINE BitVector() noexcept = default;

        /// @brief Constructs a BitVector with the specified number of bits.
        ///
        /// This constructor initializes the BitVector with the given number of bits,
        /// setting all bits to \c 0.
        ///
        /// @param bit_count The number of bits in the BitVector.
        explicit constexpr DOCK_ALLOC_FORCE_INLINE BitVector(const size_t bit_count) noexcept
            : bit_count_(bit_count),
              data_((bit_count + kBitsPerWord - 1) / kBitsPerWord, kAllZeroes)
        {
        }

        /// @brief Constructs a BitVector with the specified number of bits, optionally setting all bits to \c 1.
        ///
        /// This constructor initializes the BitVector with the given number of bits,
        /// setting all bits to \c 1 if \p all_bits_set is \c true, or to \c 0 otherwise.
        ///
        /// @param bit_count The number of bits in the BitVector.
        /// @param all_bits_set If \c true, all bits are set to \c 1; otherwise, they are set to \c 0.
        explicit constexpr DOCK_ALLOC_FORCE_INLINE BitVector(const size_t bit_count, const bool all_bits_set) noexcept
            : bit_count_(bit_count),
              data_((bit_count + kBitsPerWord - 1) / kBitsPerWord, all_bits_set ? kAllOnes : kAllZeroes)
        {
            if (all_bits_set && bit_count > 0)
            {
                if (const size_t valid_bits = bit_count % kBitsPerWord; valid_bits != 0)
                {
                    data_.back() &= BitsBetweenInclusive(0, valid_bits - 1);
                }
            }
        }

        /// @brief Returns the number of bits in the \c BitVector.
        ///
        /// This method retrieves the total number of bits stored in the BitVector.
        ///
        /// @return The total number of bits in the BitVector.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t GetBitCount() const noexcept
        {
            return bit_count_;
        }

        /// @brief Returns the number of words in the \c BitVector.
        ///
        /// This method retrieves the total number of words (storage units) used to represent the bits in the BitVector.
        ///
        /// @return The total number of words in the BitVector.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t GetWordCount() const noexcept
        {
            return data_.size();
        }

        /// @brief Clears the \c BitVector.
        ///
        /// This function resets the BitVector, clearing all bits and setting the bit count to zero.
        DOCK_ALLOC_FORCE_INLINE void Clear() noexcept
        {
            data_.clear();
            bit_count_ = 0;
        }

        /// @brief Sets all bits in the \c BitVector to a specified value.
        ///
        /// This function sets all bits in the \c BitVector.
        ///
        /// @param value The value to set all bits to.
        DOCK_ALLOC_FORCE_INLINE void SetAll(const bool value) noexcept
        {
            const WordType fill_word = value ? kAllOnes : kAllZeroes;
            std::fill(data_.begin(), data_.end(), fill_word);
        }

        /// @brief Resizes the BitVector to the specified number of bits.
        ///
        /// This function changes the size of the BitVector to \p new_bit_count.
        /// If \p new_bits_set is \c true, all bits are set to one, otherwise, they are set to zero.
        /// If the new size is larger than the current size, new bits are initialized to zero or one as specified.
        ///
        /// @param new_bit_count The new number of bits for the BitVector.
        /// @param new_bits_set If \c true, new bits are set to one, otherwise, they are set to zero.
        void Resize(const size_t new_bit_count, const bool new_bits_set = false) noexcept
        {
            const size_t old_bit_count = bit_count_;
            const size_t old_words = data_.size();
            const size_t new_words = (new_bit_count + kBitsPerWord - 1) / kBitsPerWord;
            if (new_bit_count > old_bit_count && old_words > 0)
            {
                if (const size_t old_valid = old_bit_count % kBitsPerWord; old_valid != 0)
                {
                    if (new_bits_set)
                    {
                        data_[old_words - 1] |= HighBitsFrom(old_valid);
                    }
                    else
                    {
                        data_[old_words - 1] &= LowBitsTo(old_valid - 1);
                    }
                }
            }
            if (new_bit_count < old_bit_count && new_words > 0)
            {
                if (const size_t valid = new_bit_count % kBitsPerWord; valid != 0)
                {
                    data_[new_words - 1] &= LowBitsTo(valid - 1);
                }
            }

            data_.resize(new_words, new_bits_set ? kAllOnes : kAllZeroes);
            bit_count_ = new_bit_count;

            if (new_words > 0)
            {
                if (const size_t valid = new_bit_count % kBitsPerWord; valid != 0)
                {
                    data_.back() &= LowBitsTo(valid - 1);
                }
            }
        }

        /// @brief Checks if a bit is set.
        ///
        /// This function checks if the bit at the specified index is set to \c 1.
        ///
        /// @param bit_index The index of the bit to check.
        ///
        /// @pre bit_index < GetBitCount()
        ///
        /// @return \c true if the bit is set, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool IsBitSet(const size_t bit_index) const noexcept
        {
            DCHECK_LT(bit_index, bit_count_);

            const size_t word = bit_index / kBitsPerWord;
            const size_t bit = bit_index % kBitsPerWord;
            return data_[word] >> bit & WordType{1};
        }

        /// @brief Checks if a range of bits is set.
        ///
        /// This function checks if all bits in the specified range are set to \c 1.
        /// The range is inclusive of the \p from index and exclusive of the \p to index.
        ///
        /// @param from The starting index of the range (inclusive).
        /// @param to The ending index of the range (exclusive).
        ///
        /// @pre to <= GetBitCount()
        /// @pre from <= to
        ///
        /// @return \c true if all bits in the range are set, \c false otherwise.
        [[nodiscard]] bool AreBitsSet(const size_t from, const size_t to) const noexcept
        {
            DCHECK_LE(to, bit_count_);
            DCHECK_LE(from, to);

            const size_t first_word = from / kBitsPerWord;
            const size_t last_word = (to - 1) / kBitsPerWord;
            const size_t start_bit = from % kBitsPerWord;
            const size_t end_bit = (to - 1) % kBitsPerWord;

            // Case: Range fits entirely within one word
            if (first_word == last_word)
            {
                WordType mask = BitsBetweenInclusive(start_bit, end_bit);
                return (data_[first_word] & mask) == mask;
            }

            // Head word
            WordType head_mask = HighBitsFrom(start_bit);
            if ((data_[first_word] & head_mask) != head_mask)
            {
                return false;
            }
            const size_t second_word = first_word + 1;
#if DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD
            static SimdType ones = SimdType(kAllOnes);

            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - (last_word - second_word) % kSimdWidth;

            for (size_t w = second_word; w < aligned_last; w += kSimdWidth)
            {
                SimdType vec = xsimd::load_aligned(&data_[w]);
                if (!xsimd::all(vec == ones))
                {
                    return false;
                }
            }

            for (size_t w = aligned_last; w < last_word; ++w)
            {
                if (data_[w] != kAllOnes)
                {
                    return false;
                }
            }
#else
            // Scalar fallback: middle words must be entirely ones
            for (size_t w = second_word; w < last_word; ++w)
            {
                if (data_[w] != kAllOnes)
                {
                    return false;
                }
            }
#endif

            // Tail word: bits from LSB up to end_bit
            WordType tail_mask = LowBitsTo(end_bit);
            return (data_[last_word] & tail_mask) == tail_mask;
        }

        /// @brief Sets a bit to \c 1.
        ///
        /// This function sets the bit at the specified index to \c 1.
        ///
        /// @param bit_index The index of the bit to set.
        ///
        /// @pre bit_index < GetBitCount()
        DOCK_ALLOC_FORCE_INLINE void SetBit(const size_t bit_index) noexcept
        {
            DCHECK_LT(bit_index, bit_count_);

            const size_t word = bit_index / kBitsPerWord;
            const size_t bit = bit_index % kBitsPerWord;
            data_[word] |= WordType{1} << bit;
        }

        /// @brief Sets a range of bits to \c 1.
        ///
        /// This function sets all bits in the specified range to \c 1.
        /// The range is inclusive of the \p from index and exclusive of the \p to index.
        ///
        /// @param from The starting index of the range (inclusive).
        /// @param to The ending index of the range (exclusive).
        ///
        /// @pre from <= to
        void SetBits(const size_t from, const size_t to) noexcept
        {
            DCHECK_LE(to, bit_count_);

            if (from >= to)
            {
                return;
            }

            const size_t first_word = from / kBitsPerWord;
            const size_t last_word = (to - 1) / kBitsPerWord;
            const size_t start_bit = from % kBitsPerWord;
            const size_t end_bit = (to - 1) % kBitsPerWord;

            // Case 1: entirely within one word
            if (first_word == last_word)
            {
                data_[first_word] |= BitsBetweenInclusive(start_bit, end_bit);
                return;
            }

            // Head.
            data_[first_word] |= HighBitsFrom(start_bit);
            const size_t second_word = first_word + 1;
#if DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD
            static SimdType ones = SimdType(kAllOnes);

            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - (last_word - second_word) % kSimdWidth;

            // SIMD over aligned region
            for (size_t w = second_word; w < aligned_last; w += kSimdWidth)
            {
                xsimd::store_aligned(&data_[w], ones);
            }

            // Scalar check for the remaining tail
            for (size_t w = aligned_last; w < last_word; ++w)
            {
                data_[w] = kAllOnes;
            }
#else
            // scalar fallback
            for (size_t w = second_word; w < last_word; ++w)
            {
                data_[w] = kAllOnes;
            }
#endif

            // Tail.
            data_[last_word] |= LowBitsTo(end_bit);
        }

        /// @brief Checks if a bit is clear.
        ///
        /// This function checks if the bit at the specified index is set to \c 0.
        ///
        /// @param bit_index The index of the bit to check.
        ///
        /// @pre bit_index < GetBitCount()
        ///
        /// @return \c true if the bit is clear, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool IsBitClear(const size_t bit_index) const noexcept
        {
            DCHECK_LT(bit_index, bit_count_);

            const size_t word = bit_index / kBitsPerWord;
            const size_t bit = bit_index % kBitsPerWord;
            return (data_[word] >> bit & WordType{1}) == 0;
        }

        /// @brief Checks if a range of bits is set to \c 0.
        ///
        /// This function checks if all bits in the specified range are set to \c 0.
        /// The range is inclusive of the \p from index and exclusive of the \p to index.
        ///
        /// @param from The starting index of the range (inclusive).
        /// @param to The ending index of the range (exclusive).
        ///
        /// @pre to <= GetBitCount()
        /// @pre from <= to
        ///
        /// @return \c true if all bits in the range are clear, \c false otherwise.
        [[nodiscard]] bool AreBitsClear(const size_t from, const size_t to) const noexcept
        {
            DCHECK_LE(to, bit_count_);
            DCHECK_LE(from, to);

            const size_t first_word = from / kBitsPerWord;
            const size_t last_word = (to - 1) / kBitsPerWord;
            const size_t start_bit = from % kBitsPerWord;
            const size_t end_bit = (to - 1) % kBitsPerWord;

            // Case: Range fits entirely within one word
            if (first_word == last_word)
            {
                WordType mask = BitsBetweenInclusive(start_bit, end_bit);
                return (data_[first_word] & mask) == kAllZeroes;
            }

            // Head word: bits from start_bit to MSB
            WordType head_mask = HighBitsFrom(start_bit);
            if ((data_[first_word] & head_mask) != kAllZeroes)
            {
                return false;
            }
            const size_t second_word = first_word + 1;
#if DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD
            static const SimdType zeroes = SimdType{kAllZeroes};

            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - (last_word - second_word) % kSimdWidth;

            for (size_t w = second_word; w < aligned_last; w += kSimdWidth)
            {
                SimdType vec = xsimd::load_aligned(&data_[w]);
                if (!xsimd::all(vec == zeroes))
                {
                    return false;
                }
            }

            for (size_t w = aligned_last; w < last_word; ++w)
            {
                if (data_[w] != kAllZeroes)
                {
                    return false;
                }
            }
#else
            // Scalar fallback: middle words must be entirely zero
            for (size_t w = second_word; w < last_word; ++w)
            {
                if (data_[w] != kAllZeroes)
                {
                    return false;
                }
            }
#endif
            // Tail word: bits from LSB up to end_bit
            WordType tail_mask = BitsBetweenInclusive(0, end_bit);
            return (data_[last_word] & tail_mask) == kAllZeroes;
        }

        /// @brief Sets a bit to \c 0.
        ///
        /// This function sets the bit at the specified index to \c 0.
        ///
        /// @param bit_index The index of the bit to clear.
        ///
        /// @pre bit_index < GetBitCount()
        DOCK_ALLOC_FORCE_INLINE void ClearBit(const size_t bit_index) noexcept
        {
            DCHECK_LT(bit_index, bit_count_);

            const size_t word = bit_index / kBitsPerWord;
            const size_t bit = bit_index % kBitsPerWord;
            data_[word] &= ~(WordType{1} << bit);
        }

        /// @brief Clears a range of bits.
        ///
        /// This function clears all bits in the specified range to \c 0.
        /// The range is inclusive of the \p from index and exclusive of the \p to index.
        ///
        /// @param from The starting index of the range (inclusive).
        /// @param to The ending index of the range (exclusive).
        ///
        /// @pre from <= to
        void ClearBits(const size_t from, const size_t to) noexcept
        {
            DCHECK_LE(to, bit_count_);

            if (from >= to)
            {
                return;
            }

            const size_t first_word = from / kBitsPerWord;
            const size_t last_word = (to - 1) / kBitsPerWord;
            const size_t start_bit = from % kBitsPerWord;
            const size_t end_bit = (to - 1) % kBitsPerWord;

            // Case 1: entirely within one word
            if (first_word == last_word)
            {
                data_[first_word] &= ~BitsBetweenInclusive(start_bit, end_bit);
                return;
            }

            // Head.
            data_[first_word] &= ~HighBitsFrom(start_bit);
            const size_t second_word = first_word + 1;
#if DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD
            static SimdType zeros = SimdType(kAllZeroes);

            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - (last_word - second_word) % kSimdWidth;

            // SIMD over aligned region
            for (size_t w = second_word; w < aligned_last; w += kSimdWidth)
            {
                xsimd::store_aligned(&data_[w], zeros);
            }

            // Scalar check for the remaining tail
            for (size_t w = aligned_last; w < last_word; ++w)
            {
                data_[w] = kAllZeroes;
            }
#else
            // scalar fallback
            for (size_t w = second_word; w < last_word; ++w)
            {
                data_[w] = kAllZeroes;
            }
#endif

            // Tail.
            data_[last_word] &= ~LowBitsTo(end_bit);
        }

        /// @brief Finds a clear range of bits.
        ///
        /// This function searches for a contiguous range of \p n bits that are clear (set to \c 0)
        ///
        /// @param from The starting index of the search range (inclusive).
        /// @param to The ending index of the search range (exclusive).
        /// @param n The number of contiguous bits to find.
        ///
        /// @pre to <= GetBitCount()
        /// @pre from <= to
        ///
        /// @return A \c std::optional containing the starting index of the found range,
        /// or \c std::nullopt if no such range exists.
        [[nodiscard]] std::optional<size_t> FindFirstClearRange(const size_t from, const size_t to,
                                                                const size_t n) const noexcept
        {
            // Use the iterator to find the first available position.
            auto it = BeginFreeRanges(n, from, to);

            // If the begin iterator is not equal to the end iterator, a valid range was found.
            if (it != EndFreeRanges())
            {
                // Dereference the iterator to get the starting position of the first found range.
                return *it;
            }

            // Otherwise, no suitable range exists.
            return std::nullopt;
        }


        /// @brief Checks if a bit is set.
        ///
        /// This function checks if the bit at the specified index is set to \c 1.
        ///
        /// @param bit_index The index of the bit to check.
        ///
        /// @pre bit_index < GetBitCount()
        ///
        /// @return \c true if the bit is set, \c false otherwise.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE bool GetBit(const size_t bit_index) const noexcept
        {
            return IsBitSet(bit_index);
        }

        /// @brief Checks if a bit is set.
        ///
        /// This function checks if the bit at the specified index is set to \c 1.
        ///
        /// @param bit_index The index of the bit to check.
        ///
        /// @pre bit_index < GetBitCount()
        ///
        /// @return \c true if the bit is set, \c false otherwise.
        DOCK_ALLOC_FORCE_INLINE bool operator[](const size_t bit_index) const noexcept
        {
            return IsBitSet(bit_index);
        }

        /// @brief Overload of the subscript operator for mutable access.
        ///
        /// Returns a proxy reference to the bit at the specified index, allowing both read and write access.
        ///
        /// @param bit_index The index of the bit to access (must be less than the total bit count).
        ///
        /// @pre \c bit_index < GetBitCount()
        ///
        /// @return A \c BitReference proxy object referring to the specified bit.
        ///
        /// @note The returned object is a lightweight proxy, not a true reference type.
        DOCK_ALLOC_FORCE_INLINE BitReference operator[](const size_t bit_index) noexcept
        {
            DCHECK_LT(bit_index, bit_count_);

            size_t word = bit_index / kBitsPerWord;
            size_t bit = bit_index % kBitsPerWord;
            return BitReference(data_[word], bit);
        }

        /// @brief Bitwise AND assignment operator for two \c BitVector objects.
        ///
        /// This operator performs a bitwise AND operation between the current \c BitVector
        /// and another \c BitVector, modifying the current object in place.
        ///
        /// @param other The \c BitVector to AND with the current object.
        ///
        /// @return A reference to the current \c BitVector after the operation.
        DOCK_ALLOC_FORCE_INLINE BitVector& operator&=(const BitVector& other) noexcept
        {
            DCHECK_EQ(bit_count_, other.bit_count_);
            const size_t words = GetWordCount();

#if DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD
            // Process the bulk of the data using SIMD registers.
            const size_t aligned_last = words - words % kSimdWidth;
            for (size_t i = 0; i < aligned_last; i += kSimdWidth)
            {
                SimdType a = xsimd::load_aligned(&data_[i]);
                SimdType b = xsimd::load_aligned(&other.data_[i]);
                xsimd::store_aligned(&data_[i], a & b);
            }

            // Handle any remaining elements that didn't fit in a full SIMD register.
            for (size_t i = aligned_last; i < words; ++i)
            {
                data_[i] &= other.data_[i];
            }
#else
            // The original scalar fallback for when SIMD is disabled.
            for (size_t i = 0; i < words; ++i)
            {
                data_[i] &= other.data_[i];
            }
#endif
            return *this;
        }

        /// @brief Bitwise AND operator for two \c BitVector objects.
        ///
        /// This operator performs a bitwise AND operation between two \c BitVector objects,
        /// returning a new \c BitVector that contains the result.
        ///
        /// @param lhs The first \c BitVector to AND.
        /// @param rhs The second \c BitVector to AND.
        ///
        /// @return A new \c BitVector containing the result of the bitwise AND operation.
        friend DOCK_ALLOC_FORCE_INLINE BitVector operator&(BitVector lhs, const BitVector& rhs) noexcept
        {
            lhs &= rhs;
            return lhs;
        }

        /// @brief Checks if two \c BitVector objects are equal.
        ///
        /// This function compares two \c BitVector objects for equality.
        ///
        /// @param lhs The first \c BitVector to compare.
        /// @param rhs The second \c BitVector to compare.
        ///
        /// @return \c true if both \c BitVector objects have the same bit count and identical bit values;
        /// \c false otherwise.
        friend constexpr DOCK_ALLOC_FORCE_INLINE bool operator==(const BitVector& lhs, const BitVector& rhs) noexcept
        {
            if (lhs.bit_count_ != rhs.bit_count_)
            {
                return false;
            }
            const size_t words = lhs.GetWordCount();
#if DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD
            // aligned_last is the first word we cannot include in a full SIMD block
            const size_t aligned_last = words - (words % kSimdWidth);

            for (size_t i = 0; i < aligned_last; i += kSimdWidth)
            {
                SimdType a = xsimd::load_aligned(&lhs.data_[i]);
                SimdType b = xsimd::load_aligned(&rhs.data_[i]);
                if (!xsimd::all(a == b))
                {
                    return false;
                }
            }

            // Scalar tail over [aligned_last, words)
            for (size_t i = aligned_last; i < words; ++i)
            {
                if (lhs.data_[i] != rhs.data_[i])
                {
                    return false;
                }
            }
#else
            for (size_t i = 0; i < words; ++i)
            {
                if (lhs.data_[i] != rhs.data_[i])
                {
                    return false;
                }
            }
#endif
            return true;
        }

        /// @brief Checks if two \c BitVector objects are not equal.
        ///
        /// This function compares two \c BitVector objects for inequality.
        ///
        /// @param lhs The first \c BitVector to compare.
        /// @param rhs The second \c BitVector to compare.
        ///
        /// @return \c true if the two \c BitVector objects differ in bit count or bit values;
        /// \c false if they are equal.
        friend constexpr DOCK_ALLOC_FORCE_INLINE bool operator!=(const BitVector& lhs, const BitVector& rhs) noexcept
        {
            return !(lhs == rhs);
        }

        /// @brief The iterator type for the \c BitSpan class.
        using iterator = BitVectorIterator;

        /// @brief The const iterator type for the \c BitSpan class.
        using const_iterator = ConstBitVectorIterator;

        /// @brief The reverse iterator type for the \c BitSpan class.
        using reverse_iterator = std::reverse_iterator<iterator>;

        /// @brief The const reverse iterator type for the \c BitSpan class.
        using const_reverse_iterator = std::reverse_iterator<const_iterator>;

        /// @brief Begin iterator
        ///
        /// This function returns an iterator pointing to the start of the bit span.
        ///
        /// @return An iterator pointing to the start of the bit span.
        iterator begin() noexcept
        {
            return iterator(data_.data(), 0);
        }

        /// @brief End iterator
        ///
        /// This function returns an iterator pointing to the end of the bit span.
        ///
        /// @return An iterator pointing to the end of the bit span.
        iterator end() noexcept
        {
            return iterator(data_.data(), bit_count_);
        }

        /// @brief Begin iterator (const)
        ///
        /// This function returns a const iterator pointing to the start of the bit span.
        ///
        /// @return A const iterator pointing to the start of the bit span.
        const_iterator begin() const noexcept
        {
            return const_iterator(data_.data(), 0);
        }

        /// @brief End iterator (const)
        ///
        /// This function returns a const iterator pointing to the end of the bit span.
        ///
        /// @return A const iterator pointing to the end of the bit span.
        const_iterator end() const noexcept
        {
            return const_iterator(data_.data(), bit_count_);
        }

        /// @brief Const begin iterator
        ///
        /// This function returns a const iterator pointing to the start of the bit span.
        ///
        /// @return A const iterator pointing to the start of the bit span.
        const_iterator cbegin() const noexcept
        {
            return const_iterator(data_.data(), 0);
        }

        /// @brief Const end iterator
        ///
        /// This function returns a const iterator pointing to the end of the bit span.
        ///
        /// @return A const iterator pointing to the end of the bit span.
        const_iterator cend() const noexcept
        {
            return const_iterator(data_.data(), bit_count_);
        }

        /// @brief Start reverse iterator
        ///
        /// This function returns a reverse iterator pointing to the start of the bit span.
        ///
        /// @return A reverse iterator pointing to the start of the bit span.
        reverse_iterator rbegin() noexcept
        {
            return reverse_iterator(end());
        }

        /// @brief End reverse iterator
        ///
        /// This function returns a reverse iterator pointing to the end of the bit span.
        ///
        /// @return A reverse iterator pointing to the end of the bit span.
        reverse_iterator rend() noexcept
        {
            return reverse_iterator(begin());
        }

        /// @brief Start reverse iterator (const)
        ///
        /// This function returns a const reverse iterator pointing to the start of the bit span.
        ///
        /// @return A const reverse iterator pointing to the start of the bit span.
        const_reverse_iterator rbegin() const noexcept
        {
            return const_reverse_iterator(end());
        }

        /// @brief End reverse iterator (const)
        ///
        /// This function returns a const reverse iterator pointing to the end of the bit span.
        ///
        /// @return A const reverse iterator pointing to the end of the bit span.
        const_reverse_iterator rend() const noexcept
        {
            return const_reverse_iterator(begin());
        }

        /// @brief Const start reverse iterator
        ///
        /// This function returns a const reverse iterator pointing to the start of the bit span.
        ///
        /// @return A const reverse iterator pointing to the start of the bit span.
        const_reverse_iterator crbegin() const noexcept
        {
            return const_reverse_iterator(end());
        }

        /// @brief Const end reverse iterator
        ///
        /// This function returns a const reverse iterator pointing to the end of the bit span.
        ///
        /// @return A const reverse iterator pointing to the end of the bit span.
        const_reverse_iterator crend() const noexcept
        {
            return const_reverse_iterator(begin());
        }

    private:
        /// @brief Creates a bitmask with all bits from the given index (inclusive) to the most significant bit set to 1.
        ///
        /// This function is used to generate a bitmask where all bits at or above the specified bit index
        /// are set to \c 1. Bits below the given index are set to \c 0. This is useful for clearing or preserving
        /// higher-order bits, particularly in alignment operations or boundary masking.
        ///
        /// If the bit index \p bit is equal to or exceeds the width of the \c Storage type, the result is \c 0.
        ///
        /// @param bit The bit index from which to start setting bits to \c 1 (inclusive).
        /// @return A bitmask with bits [\p bit, \c kBitsPerWord - 1] set to \c 1 and bits [0, \p bit - 1] set to \c 0.
        static constexpr DOCK_ALLOC_FORCE_INLINE WordType HighBitsFrom(const size_t bit) noexcept
        {
            return (bit >= kBitsPerWord) ? kAllZeroes : static_cast<WordType>(kAllOnes << bit);
        }

        /// @brief Creates a bitmask with all bits from the least significant bit up to and
        /// including the given index set to 1.
        ///
        /// This function is used to generate a bitmask where all bits from bit index \c 0 up to and including
        /// the specified index \p bit are set to \c 1. Higher-order bits are set to \c 0. This is commonly used
        /// to isolate low-order bits or implement index masking for small ranges.
        ///
        /// If the bit index \p bit is equal to or exceeds the width of the \c Storage type, the result is all \c 1s.
        ///
        /// @param bit The highest bit index to include in the mask (inclusive).
        /// @return A bitmask with bits [0, \p bit] set to \c 1 and bits [\p bit + 1, \c kBitsPerWord - 1] set to \c 0.
        static constexpr DOCK_ALLOC_FORCE_INLINE WordType LowBitsTo(const size_t bit) noexcept
        {
            return (bit >= kBitsPerWord) ? kAllOnes : static_cast<WordType>(kAllOnes >> (kBitsPerWord - bit - 1));
        }

        /// @brief Creates a bitmask with all bits in the closed interval [\p from, \p to] set to 1.
        ///
        /// This function combines a high-mask and low-mask to produce a bitmask with \c 1 bits in the range
        /// of bits from \p from to \p to, inclusive. It is used to isolate or update a specific range of bits
        /// within a word without affecting surrounding bits.
        ///
        /// Both \p from and \p to must satisfy \c from <= to, and both must be less than the number of bits
        /// in the \c Storage type for meaningful results. If either exceeds the bit width, results are truncated.
        ///
        /// @param from The starting bit index of the interval (inclusive).
        /// @param to The ending bit index of the interval (inclusive).
        ///
        /// @pre \p from and \p to must be less than \c kBitsPerWord.
        ///
        /// @return A bitmask with bits [\p from, \p to] set to \c 1 and all other bits set to \c 0.
        static constexpr DOCK_ALLOC_FORCE_INLINE WordType BitsBetweenInclusive(
            const size_t from, const size_t to) noexcept
        {
            DCHECK_LE(from, to);
            DCHECK_LT(from, kBitsPerWord);
            DCHECK_LT(to, kBitsPerWord);

            return HighBitsFrom(from) & LowBitsTo(to);
        }

        size_t bit_count_{};
#if DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD
        /// @brief The SIMD type used for vectorized operations.
        using SimdType = xsimd::batch<WordType>;

        /// @brief The Width of the SIMD type.
        static constexpr std::size_t kSimdWidth = SimdType::size;

        std::vector<WordType, xsimd::aligned_allocator<WordType>> data_;
#else
        std::vector<WordType> data_;
#endif
    };
}

#endif
