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

#ifndef DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD
#define DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD 1
#include "dockalloc/core/include/miscellaneous/inline.h"
#endif

#include <concepts>
#include <limits>
#include <optional>
#include <algorithm>
#include <bit>
#include <vector>
#include "absl/log/check.h"
#if DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD
#include "xsimd/xsimd.hpp"
#endif
#include "dockalloc/core/miscellaneous/core_defines.h"

namespace dockalloc::solver
{
    template <typename WordType>
        requires std::unsigned_integral<WordType>
    class BitVector
    {
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

    public:
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
              data_((bit_count + kBitsPerWord - 1) / kBitsPerWord, WordType{0})
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
              data_((bit_count + kBitsPerWord - 1) / kBitsPerWord, all_bits_set ? ~WordType{0} : WordType{0})
        {
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

            data_.resize(new_words, new_bits_set ? ~WordType{0} : WordType{0});
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
            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - (last_word - second_word) % kSimdWidth;

            for (size_t w = second_word; w < aligned_last; w += kSimdWidth)
            {
                SimdType vec = xsimd::load_aligned(&data_[w]);
                if (!xsimd::all(vec == SimdType{static_cast<WordType>(~WordType{0})}))
                {
                    return false;
                }
            }

            for (size_t w = aligned_last; w < last_word; ++w)
            {
                if (data_[w] != ~WordType{0})
                {
                    return false;
                }
            }
#else
            // Scalar fallback: middle words must be entirely ones
            for (size_t w = second_word; w < last_word; ++w)
            {
                if (data_[w] != ~WordType{0})
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
            SimdType ones = SimdType(~WordType{0});

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
                data_[w] = ~WordType{0};
            }
#else
            // scalar fallback
            for (size_t w = second_word; w < last_word; ++w)
            {
                data_[w] = ~WordType{0};
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
                return (data_[first_word] & mask) == WordType{0};
            }

            // Head word: bits from start_bit to MSB
            WordType head_mask = HighBitsFrom(start_bit);
            if ((data_[first_word] & head_mask) != WordType{0})
            {
                return false;
            }

            const size_t second_word = first_word + 1;
#if DOCK_ALLOC_SOLVER_CONTAINER_BIT_VECTOR_USES_SIMD
            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - (last_word - second_word) % kSimdWidth;

            for (size_t w = second_word; w < aligned_last; w += kSimdWidth)
            {
                SimdType vec = xsimd::load_aligned(&data_[w]);
                if (!xsimd::all(vec == SimdType{static_cast<WordType>(WordType{0})}))
                {
                    return false;
                }
            }

            for (size_t w = aligned_last; w < last_word; ++w)
            {
                if (data_[w] != WordType{0})
                {
                    return false;
                }
            }
#else
            // Scalar fallback: middle words must be entirely zero
            for (size_t w = second_word; w < last_word; ++w)
            {
                if (data_[w] != WordType{0})
                {
                    return false;
                }
            }
#endif
            // Tail word: bits from LSB up to end_bit
            WordType tail_mask = LowBitsTo(end_bit);
            return (data_[last_word] & tail_mask) == WordType{0};
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
            SimdType zeros = SimdType(WordType{0});

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
                data_[w] = WordType{0};
            }
#else
            // scalar fallback
            for (size_t w = second_word; w < last_word; ++w)
            {
                data_[w] = WordType{0};
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

                WordType mask = HighBitsFrom(b);
                if (w == last_word)
                {
                    mask &= LowBitsTo(last_bit);
                }

                WordType word = data_[w];

                if ((word & mask) == WordType{0})
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

                WordType inv = ~word & mask;
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
            for (size_t i = 0; i < words; ++i)
            {
                if (lhs.data_[i] != rhs.data_[i])
                {
                    return false;
                }
            }
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
            static constexpr auto all_ones = static_cast<WordType>(~WordType{0});
            return (bit >= kBitsPerWord) ? WordType{0} : static_cast<WordType>(all_ones << bit);
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
            static constexpr auto all_ones = static_cast<WordType>(~WordType{0});
            return (bit >= kBitsPerWord) ? all_ones : static_cast<WordType>(all_ones >> (kBitsPerWord - bit - 1));
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
