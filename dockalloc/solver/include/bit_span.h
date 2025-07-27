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

#ifndef DOCK_ALLOC_SOLVER_BIT_SPAN_H_
#define DOCK_ALLOC_SOLVER_BIT_SPAN_H_

#ifndef DOCK_ALLOC_SOLVER_BIT_SPAN_USE_SIMD
#define DOCK_ALLOC_SOLVER_BIT_SPAN_USE_SIMD 1
#endif

#include <concepts>
#include <limits>
#include <iterator>
#include <bit>
#include "absl/log/check.h"
#if DOCK_ALLOC_SOLVER_BIT_SPAN_USE_SIMD
#include "xsimd/xsimd.hpp"
#endif
#include "dockalloc/core/memory/aligned_storage.h"

namespace dockalloc::solver
{
    /// @brief A lightweight non-owning view over a packed bit array.
    ///
    /// This class provides a low-overhead interface to a contiguous sequence of bits
    /// stored in an array of unsigned integral words (e.g., uint64_t). It is designed to enable
    /// efficient bit-level access and manipulation, while exposing only the range of valid bits.
    ///
    /// @tparam StorageType An unsigned integral type used to store bits (e.g., uint64_t).
    ///
    /// @note This class does not own the underlying memory. The user is responsible for ensuring
    /// that the lifetime of the data outlives the \c BitSpan instance. Modifying or deallocating
    /// the underlying memory while a \c BitSpan is in use results in undefined behavior.
    /// Also, the user must ensure that the data provided is large enough to hold the
    /// specified number of bits. Otherwise, accessing out-of-bounds bits may lead to undefined behavior.
    ///
    /// @note The number of valid bits is tracked independently of the number of storage words.
    /// It is the caller’s responsibility to ensure that the storage contains enough words
    /// to safely represent all bits.
    template <typename Storage>
        requires core::AlignedStorageView<Storage> && std::unsigned_integral<typename Storage::Type>
    class BitSpan
    {
    public:
        /// @brief The type of the storage used to hold bits.
        ///
        /// This type is an alias for the underlying storage type used to hold the bits.
        using StorageType = typename Storage::Type;

        /// @brief The alignment of the data stored.
        ///
        /// This constant specifies the alignment in bytes required for the storage.
        static constexpr size_t kAlignedSize = Storage::kAlignment;

    private:
        /// @brief A reference to a single bit in the bit span.
        ///
        /// This class provides a reference to a single bit in the bit span, allowing for
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
            BitReference(StorageType& word, const size_t bit)
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
            operator bool() const noexcept // NOLINT(*-explicit-constructor)
            {
                return word_ >> bit_ & StorageType{1};
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
            BitReference& operator=(const bool value) noexcept
            {
                const StorageType mask = StorageType{1} << bit_;
                word_ = (word_ & ~mask) | (StorageType(value) << bit_);
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
            BitReference& operator=(const BitReference& other) noexcept
            {
                *this = static_cast<bool>(other);
                return *this;
            }

        private:
            StorageType& word_;
            size_t bit_;
        };

    public:
        /// @brief An iterator for the \c BitSpan class.
        ///
        /// This iterator enables read-write traversal over the individual bits in a \c BitSpan.
        /// Dereferencing yields a \c BitReference, allowing for both inspection and assignment.
        ///
        /// @note This iterator satisfies the requirements of a random-access iterator.
        /// It does not provide a pointer type, as \c BitReference is a proxy object.
        class BitSpanIterator
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
            /// @param data Aligned storage containing the bit data.
            /// @param index Bit index the iterator points to.
            ///
            /// @pre data != nullptr
            explicit BitSpanIterator(Storage data, const size_t index) noexcept
                : data_(data), index_(index)
            {
                DCHECK_NE(data.Get(), nullptr);
            }

            /// @brief Dereference operator.
            ///
            /// Returns a proxy reference to the bit at the current index.
            ///
            /// @return A \c BitReference proxy to the current bit.
            BitReference operator*() const noexcept
            {
                const size_t word = index_ / kBitsPerWord;
                const size_t bit = index_ % kBitsPerWord;
                return BitReference(data_.Get()[word], bit);
            }

            /// @brief Pre-increment operator.
            ///
            /// Pre-increments the iterator to point to the next bit in the span.
            ///
            /// @return Reference to the incremented iterator.
            BitSpanIterator& operator++() noexcept
            {
                ++index_;
                return *this;
            }

            /// @brief Post-increment operator.
            ///
            /// Post-increments the iterator to point to the next bit in the span.
            ///
            /// @return Copy of the iterator before increment.
            BitSpanIterator operator++(int) noexcept
            {
                BitSpanIterator tmp = *this;
                ++index_;
                return tmp;
            }

            /// @brief Pre-decrement operator.
            ///
            /// Pre-decrements the iterator to point to the previous bit in the span.
            ///
            /// @return Reference to the decremented iterator.
            BitSpanIterator& operator--() noexcept
            {
                --index_;
                return *this;
            }

            /// @brief Post-decrement operator.
            ///
            /// Post-decrements the iterator to point to the previous bit in the span.
            ///
            /// @return Copy of the iterator before decrement.
            BitSpanIterator operator--(int) noexcept
            {
                BitSpanIterator tmp = *this;
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
            BitSpanIterator& operator+=(const difference_type n) noexcept
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
            BitSpanIterator& operator-=(const difference_type n) noexcept
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
            BitSpanIterator operator+(const difference_type n) const noexcept
            {
                return iterator(data_.Get(), index_ + n);
            }

            /// @brief Iterator subtraction.
            ///
            /// Retreats the iterator by the specified number of positions.
            ///
            /// @param n Number of positions to retreat.
            ///
            /// @return New iterator retreated by \c n.
            BitSpanIterator operator-(const difference_type n) const noexcept
            {
                return iterator(data_.Get(), index_ - n);
            }

            /// @brief Distance between iterators.
            ///
            /// Distance between two iterators in terms of bit positions.
            ///
            /// @param other The other iterator.
            ///
            /// @return Difference in bit positions.
            difference_type operator-(const BitSpanIterator& other) const noexcept
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
            bool operator==(const BitSpanIterator& other) const noexcept
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
            bool operator!=(const BitSpanIterator& other) const noexcept
            {
                return index_ != other.index_;
            }

        private:
            Storage data_;
            size_t index_;
        };

        /// @brief A const iterator for the \c BitSpan class.
        ///
        /// This iterator enables read-only traversal over the individual bits in a \c BitSpan.
        /// Dereferencing yields a boolean value, indicating whether the bit is set or not.
        class ConstBitSpanIterator
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
            /// This constructor initializes a \c ConstBitSpanIterator to point to a specific bit
            /// in the bit span.
            ///
            /// @param data Aligned storage containing the bit data.
            /// @param index Bit index the iterator points to.
            ///
            /// @pre data != nullptr
            explicit ConstBitSpanIterator(const Storage data, const size_t index) noexcept
                : data_(data), index_(index)
            {
                DCHECK_NE(data.Get(), nullptr);
            }

            /// @brief Returns the boolean value of the current bit.
            ///
            /// This operator dereferences the iterator to yield the value of the bit at the current position.
            ///
            /// @return true if the bit at the current position is set; false if clear.
            bool operator*() const noexcept
            {
                size_t word = index_ / kBitsPerWord;
                size_t bit = index_ % kBitsPerWord;
                return (data_.Get()[word] >> bit & StorageType{1}) != 0;
            }

            /// @brief Advances iterator to the next bit (pre-increment).
            ///
            /// Pre-increments the iterator to point to the next bit in the span.
            ///
            /// @return Reference to the incremented iterator.
            ConstBitSpanIterator& operator++() noexcept
            {
                ++index_;
                return *this;
            }

            /// @brief Advances iterator to the next bit (post-increment).
            ///
            /// Post-increments the iterator to point to the next bit in the span.
            ///
            /// @return Iterator state before increment.
            ConstBitSpanIterator operator++(int) noexcept
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
            ConstBitSpanIterator& operator--() noexcept
            {
                --index_;
                return *this;
            }

            /// @brief Moves iterator to the previous bit (post-decrement).
            ///
            /// Post-decrements the iterator to point to the previous bit in the span.
            ///
            /// @return Iterator state before decrement.
            ConstBitSpanIterator operator--(int) noexcept
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
            ConstBitSpanIterator& operator+=(difference_type n) noexcept
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
            ConstBitSpanIterator& operator-=(difference_type n) noexcept
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
            ConstBitSpanIterator operator+(difference_type n) const noexcept
            {
                return ConstBitSpanIterator(data_.Get(), index_ + n);
            }

            /// @brief Returns a new iterator retreated by n bits.
            ///
            /// This operator allows the iterator to be retreated by a specified number of bits.
            ///
            /// @param n Number of bits to retreat.
            ///
            /// @return New iterator at position index - n.
            ConstBitSpanIterator operator-(difference_type n) const noexcept
            {
                return ConstBitSpanIterator(data_.Get(), index_ - n);
            }

            /// @brief Computes the distance between two iterators.
            ///
            /// This operator computes the difference in bit positions between two iterators.
            ///
            /// @param other Another iterator to compare to.
            ///
            /// @return Difference in bit positions (this - other).
            difference_type operator-(const ConstBitSpanIterator& other) const noexcept
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
            bool operator==(const ConstBitSpanIterator& other) const noexcept { return index_ == other.index_; }

            /// @brief Checks inequality of two iterators.
            ///
            /// This operator checks if two iterators point to different bit indices.
            ///
            /// @param other Another iterator to compare.
            ///
            /// @return true if iterators point to different bit indices.
            bool operator!=(const ConstBitSpanIterator& other) const noexcept { return index_ != other.index_; }

        private:
            const Storage data_;
            size_t index_;
        };

        /// @brief The count of bits in a single Storage word.
        static constexpr int kBitsPerWord = std::numeric_limits<StorageType>::digits;

        /// @brief Constructor.
        ///
        /// This constructor initializes a \c BitSpan object with the specified data pointer and bit count.
        ///
        /// @param data The aligned storage containing the bit data.
        /// @param bit_count The number of bits in the span.
        ///
        /// @pre data != nullptr
        /// @pre bit_count > 0
        explicit BitSpan(const Storage data, const size_t bit_count) noexcept
            : data_(data), bit_count_(bit_count)
        {
            CHECK(data.Get() != nullptr);
        }

        /// @brief Getter for the data pointer.
        ///
        /// This function returns the pointer to the data.
        ///
        /// @return The pointer to the data.
        [[nodiscard]] StorageType* GetData() const noexcept
        {
            return data_.Get();
        }

        /// @brief Getter for the bit count.
        ///
        /// This function returns the number of bits in the span.
        ///
        /// @return The number of bits in the span.
        [[nodiscard]] size_t GetBitCount() const noexcept
        {
            return bit_count_;
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
        [[nodiscard]] bool IsBitSet(const size_t bit_index) const noexcept
        {
            DCHECK_LT(bit_index, bit_count_);

            const size_t word = bit_index / kBitsPerWord;
            const size_t bit = bit_index % kBitsPerWord;
            return data_.Get()[word] >> bit & StorageType{1};
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
                StorageType mask = BitsBetweenInclusive(start_bit, end_bit);
                return (data_.Get()[first_word] & mask) == mask;
            }

            // Head word
            StorageType head_mask = HighBitsFrom(start_bit);
            if ((data_.Get()[first_word] & head_mask) != head_mask)
            {
                return false;
            }

            const size_t second_word = first_word + 1;
#if DOCK_ALLOC_SOLVER_BIT_SPAN_USE_SIMD
            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - (last_word - second_word) % kSimdWidth;

            for (size_t w = second_word; w < aligned_last; w += kSimdWidth)
            {
                SimdType vec;
                if constexpr (kAlignedSize >= kSimdAlignment)
                {
                    vec = xsimd::load_aligned(data_.Get() + w);
                }
                else
                {
                    vec = xsimd::load_unaligned(data_.Get() + w);
                }
                if (!xsimd::all(vec == SimdType{~StorageType{0}}))
                {
                    return false;
                }
            }

            for (size_t w = aligned_last; w < last_word; ++w)
            {
                if (data_.Get()[w] != ~StorageType{0})
                {
                    return false;
                }
            }
#else
            // Scalar fallback: middle words must be entirely ones
            for (size_t w = second_word; w < last_word; ++w)
            {
                if (data_.Get()[w] != ~StorageType{0})
                {
                    return false;
                }
            }
#endif

            // Tail word: bits from LSB up to end_bit
            StorageType tail_mask = LowBitsTo(end_bit);
            return (data_.Get()[last_word] & tail_mask) == tail_mask;
        }

        /// @brief Sets a bit to \c 1.
        ///
        /// This function sets the bit at the specified index to \c 1.
        ///
        /// @param bit_index The index of the bit to set.
        ///
        /// @pre bit_index < GetBitCount()
        void SetBit(const size_t bit_index) noexcept
        {
            DCHECK_LT(bit_index, bit_count_);

            const size_t word = bit_index / kBitsPerWord;
            const size_t bit = bit_index % kBitsPerWord;
            data_.Get()[word] |= StorageType{1} << bit;
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
                data_.Get()[first_word] |= BitsBetweenInclusive(start_bit, end_bit);
                return;
            }

            // Head.
            data_.Get()[first_word] |= HighBitsFrom(start_bit);

            const size_t second_word = first_word + 1;
#if DOCK_ALLOC_SOLVER_BIT_SPAN_USE_SIMD
            SimdType ones = SimdType(~StorageType{0});

            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - (last_word - second_word) % kSimdWidth;

            // SIMD over aligned region
            for (size_t w = second_word; w < aligned_last; w += kSimdWidth)
            {
                if constexpr (kAlignedSize >= kSimdAlignment)
                {
                    xsimd::store_aligned(&data_.Get()[w], ones);
                }
                else
                {
                    xsimd::store_unaligned(&data_.Get()[w], ones);
                }
            }

            // Scalar check for the remaining tail
            for (size_t w = aligned_last; w < last_word; ++w)
            {
                data_.Get()[w] = ~StorageType{0};
            }
#else
            // scalar fallback
            for (size_t w = second_word; w < last_word; ++w)
            {
                data_.Get()[w] = ~StorageType{0};
            }
#endif

            // Tail.
            data_.Get()[last_word] |= LowBitsTo(end_bit);
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
        [[nodiscard]] bool IsBitClear(const size_t bit_index) const noexcept
        {
            DCHECK_LT(bit_index, bit_count_);

            const size_t word = bit_index / kBitsPerWord;
            const size_t bit = bit_index % kBitsPerWord;
            return (data_.Get()[word] >> bit & StorageType{1}) == 0;
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
                StorageType mask = BitsBetweenInclusive(start_bit, end_bit);
                return (data_.Get()[first_word] & mask) == StorageType{0};
            }

            // Head word: bits from start_bit to MSB
            StorageType head_mask = HighBitsFrom(start_bit);
            if ((data_.Get()[first_word] & head_mask) != StorageType{0})
            {
                return false;
            }

            const size_t second_word = first_word + 1;
#if DOCK_ALLOC_SOLVER_BIT_SPAN_USE_SIMD
            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - (last_word - second_word) % kSimdWidth;

            for (size_t w = second_word; w < aligned_last; w += kSimdWidth)
            {
                SimdType vec;
                if constexpr (kAlignedSize >= kSimdAlignment)
                {
                    vec = xsimd::load_aligned(&data_.Get()[w]);
                }
                else
                {
                    vec = xsimd::load_unaligned(&data_.Get()[w]);
                }
                if (!xsimd::all(vec == SimdType{0}))
                {
                    return false;
                }
            }

            for (size_t w = aligned_last; w < last_word; ++w)
            {
                if (data_.Get()[w] != StorageType{0})
                {
                    return false;
                }
            }
#else
            // Scalar fallback: middle words must be entirely zero
            for (size_t w = second_word; w < last_word; ++w)
            {
                if (data_.Get()[w] != StorageType{0})
                {
                    return false;
                }
            }
#endif
            // Tail word: bits from LSB up to end_bit
            StorageType tail_mask = LowBitsTo(end_bit);
            return (data_.Get()[last_word] & tail_mask) == StorageType{0};
        }

        /// @brief Sets a bit to \c 0.
        ///
        /// This function sets the bit at the specified index to \c 0.
        ///
        /// @param bit_index The index of the bit to clear.
        ///
        /// @pre bit_index < GetBitCount()
        void ClearBit(const size_t bit_index) noexcept
        {
            DCHECK_LT(bit_index, bit_count_);

            const size_t word = bit_index / kBitsPerWord;
            const size_t bit = bit_index % kBitsPerWord;
            data_.Get()[word] &= ~(StorageType{1} << bit);
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
                data_.Get()[first_word] &= ~BitsBetweenInclusive(start_bit, end_bit);
                return;
            }

            // Head.
            data_.Get()[first_word] &= ~HighBitsFrom(start_bit);

            const size_t second_word = first_word + 1;
#if DOCK_ALLOC_SOLVER_BIT_SPAN_USE_SIMD
            SimdType zeros = SimdType(StorageType{0});

            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - (last_word - second_word) % kSimdWidth;

            // SIMD over aligned region
            for (size_t w = second_word; w < aligned_last; w += kSimdWidth)
            {
                if constexpr (kAlignedSize >= kSimdAlignment)
                {
                    xsimd::store_aligned(&data_.Get()[w], zeros);
                }
                else
                {
                    xsimd::store_unaligned(&data_.Get()[w], zeros);
                }
            }

            // Scalar check for the remaining tail
            for (size_t w = aligned_last; w < last_word; ++w)
            {
                data_.Get()[w] = StorageType{0};
            }
#else
            // scalar fallback
            for (size_t w = second_word; w < last_word; ++w)
            {
                data_.Get()[w] = StorageType{0};
            }
#endif

            // Tail.
            data_.Get()[last_word] &= ~LowBitsTo(end_bit);
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
        [[nodiscard]] std::optional<size_t> FindClearRange(const size_t from, const size_t to,
                                                           const size_t n) const noexcept
        {
            DCHECK_LE(to, bit_count_);
            DCHECK_LE(from, to);

            if (n == 0)
            {
                return from < to ? std::optional{from} : std::nullopt;
            }
            if (from + n > to || to > bit_count_)
            {
                return std::nullopt;
            }

            size_t run = 0;
            size_t run_start = from;
            size_t pos = from;

            const size_t last_word = (to - 1) / kBitsPerWord;
            const size_t last_bit = (to - 1) % kBitsPerWord;

            while (pos < to)
            {
                const size_t w = pos / kBitsPerWord;
                const size_t b = pos % kBitsPerWord;
                const size_t base = w * kBitsPerWord;

                StorageType mask = HighBitsFrom(b);
                if (w == last_word)
                {
                    mask &= LowBitsTo(last_bit);
                }

                StorageType word = data_.Get()[w];

                if ((word & mask) == StorageType{0})
                {
                    const size_t chunk = std::min<size_t>(
                        w * kBitsPerWord + kBitsPerWord - pos,
                        to - pos
                    );
                    if (run == 0)
                    {
                        run_start = pos;
                    }
                    run += chunk;
                    if (run >= n)
                    {
                        return run_start;
                    }
                    pos += chunk;
                    continue;
                }

                StorageType inv = ~word & mask;
                while (inv)
                {
                    const int off = std::countr_zero(inv);
                    inv &= inv - 1;
                    const size_t p = base + off;

                    if (p == pos)
                    {
                        ++run;
                    }
                    else
                    {
                        run_start = p;
                        run = 1;
                    }
                    if (run >= n)
                    {
                        return run_start;
                    }
                    pos = p + 1;
                }

                run = 0;
                pos = base + kBitsPerWord;
            }

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
        [[nodiscard]] bool GetBit(const size_t bit_index) const noexcept
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
        bool operator[](const size_t bit_index) const noexcept
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
        BitReference operator[](const size_t bit_index) noexcept
        {
            DCHECK_LT(bit_index, bit_count_);

            size_t word = bit_index / kBitsPerWord;
            size_t bit = bit_index % kBitsPerWord;
            return BitReference(data_.Get()[word], bit);
        }

        /// @brief The iterator type for the \c BitSpan class.
        using iterator = BitSpanIterator;

        /// @brief The const iterator type for the \c BitSpan class.
        using const_iterator = ConstBitSpanIterator;

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
            return iterator(data_.Get(), 0);
        }

        /// @brief End iterator
        ///
        /// This function returns an iterator pointing to the end of the bit span.
        ///
        /// @return An iterator pointing to the end of the bit span.
        iterator end() noexcept
        {
            return iterator(data_.Get(), bit_count_);
        }

        /// @brief Begin iterator (const)
        ///
        /// This function returns a const iterator pointing to the start of the bit span.
        ///
        /// @return A const iterator pointing to the start of the bit span.
        const_iterator begin() const noexcept
        {
            return const_iterator(data_.Get(), 0);
        }

        /// @brief End iterator (const)
        ///
        /// This function returns a const iterator pointing to the end of the bit span.
        ///
        /// @return A const iterator pointing to the end of the bit span.
        const_iterator end() const noexcept
        {
            return const_iterator(data_.Get(), bit_count_);
        }

        /// @brief Const begin iterator
        ///
        /// This function returns a const iterator pointing to the start of the bit span.
        ///
        /// @return A const iterator pointing to the start of the bit span.
        const_iterator cbegin() const noexcept
        {
            return const_iterator(data_.Get(), 0);
        }

        /// @brief Const end iterator
        ///
        /// This function returns a const iterator pointing to the end of the bit span.
        ///
        /// @return A const iterator pointing to the end of the bit span.
        const_iterator cend() const noexcept
        {
            return const_iterator(data_.Get(), bit_count_);
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

#if DOCK_ALLOC_SOLVER_BIT_SPAN_USE_SIMD
        /// @brief The SIMD type used for vectorized operations.
        using SimdType = xsimd::batch<StorageType>;

        /// @brief The Width of the SIMD type.
        static constexpr std::size_t kSimdWidth = SimdType::size;

        /// @brief The alignment requirement for the SIMD type.
        static constexpr size_t kSimdAlignment = alignof(SimdType);
#endif

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
        static constexpr StorageType HighBitsFrom(const size_t bit) noexcept
        {
            DCHECK_LT(bit, kBitsPerWord);

            return ~StorageType{0} << bit;
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
        static constexpr StorageType LowBitsTo(const size_t bit) noexcept
        {
            DCHECK_LT(bit, kBitsPerWord);

            return ~StorageType{0} >> (kBitsPerWord - bit - 1);
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
        static constexpr StorageType BitsBetweenInclusive(const size_t from, const size_t to) noexcept
        {
            DCHECK_LE(from, to);
            DCHECK_LT(from, kBitsPerWord);
            DCHECK_LT(to, kBitsPerWord);

            return HighBitsFrom(from) & LowBitsTo(to);
        }

        /// @brief Non owning pointer to the data.
        Storage data_;

        /// @brief The number of bits in the span.
        ///
        /// Assumption is that \c data_.Get() is large enough to hold the number of bits.
        size_t bit_count_;
    };
}

#endif
