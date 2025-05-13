// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SLOT_TIMELINE_BIT_SPAN_H_
#define DOCK_ALLOC_SLOT_TIMELINE_BIT_SPAN_H_

#ifndef DOCK_ALLOC_SOLVER_SLOT_TIMELINE_BIT_SPAN_USE_SIMD
#define DOCK_ALLOC_SOLVER_SLOT_TIMELINE_BIT_SPAN_USE_SIMD 1
#endif

#include <cstdint>
#include <limits>
#include <concepts>
#include <type_traits>
#include <array>
#include <vector>
#include <ranges>
#include "absl/log/check.h"
#include "dockalloc/solver/time_slot_range.h"

#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_BIT_SPAN_USE_SIMD
#include "xsimd/xsimd.hpp"
#endif

namespace dockalloc::solver
{
    /// @brief Represents a non-owning span of bits within a \c SlotTimeline.
    ///
    /// This class provides an efficient, low-level interface to manipulate and query
    /// a contiguous range of bits. It does not own the underlying memory, but acts
    /// as a view over externally managed bit storage (e.g., a bitmap vector).
    ///
    /// The caller is responsible for ensuring the validity and lifetime of the underlying
    /// data pointer and for ensuring that \c word_count accurately reflects the storage size.
    ///
    /// @tparam Storage The word type used to store bits. Must be an unsigned integral type.
    template <typename Storage>
        requires std::unsigned_integral<Storage>
    class SlotTimelineBitSpan
    {
    public:
        /// @brief The count of bits in a single Storage word.
        static constexpr int kBitsPerWord = std::numeric_limits<Storage>::digits;

        /// @brief Copy constructor.
        ///
        /// This constructor creates a new \c SlotTimelineBitSpan object as a copy of another.
        ///
        /// @param other The \c SlotTimelineBitSpan object to copy.
        SlotTimelineBitSpan(const SlotTimelineBitSpan& other) noexcept = default;

        /// @brief Move constructor.
        ///
        /// This constructor creates a new \c SlotTimelineBitSpan object by moving another.
        ///
        /// @param other The \c SlotTimelineBitSpan object to move.
        SlotTimelineBitSpan(SlotTimelineBitSpan&& other) noexcept = default;

        /// @brief Constructor.
        ///
        /// This constructor initializes a \c SlotTimelineBitSpan object with the specified data and word count.
        ///
        /// @param data The pointer to the data array representing the bit span.
        /// @param word_count The number of words in the data array.
        ///
        /// @pre The data pointer must not be null.
        explicit SlotTimelineBitSpan(Storage* const data, const size_t word_count) noexcept
            : data_(data), word_count_(word_count)
        {
            DCHECK_NE(data, nullptr);
        }

        /// @brief Constructor.
        ///
        /// This constructor creates a \c SlotTimelineBitSpan object from a vector of Storage words.
        ///
        /// @param vec The vector of Storage words representing the bit span.
        explicit SlotTimelineBitSpan(std::vector<Storage>& vec) noexcept
            : data_(vec.data()), word_count_(vec.size())
        {
            DCHECK_NE(data_, nullptr);
        }

        /// @brief Constructor.
        ///
        /// This constructor creates a \c SlotTimelineBitSpan object from a span of Storage words.
        ///
        /// @param span The span of Storage words representing the bit span.
        explicit SlotTimelineBitSpan(std::span<Storage> span) noexcept
            : data_(span.data()), word_count_(span.size())
        {
            DCHECK_NE(data_, nullptr);
        }

        /// @brief Getter for the data pointer.
        ///
        /// This function returns the pointer to the underlying data array.
        ///
        /// @return A pointer to the data array representing the bit span.
        [[nodiscard]] Storage* GetData() const noexcept
        {
            return data_;
        }

        /// @brief Getter for the word count.
        ///
        /// This function returns the number of words in the bit span.
        ///
        /// @return The number of words in the bit span.
        [[nodiscard]] size_t GetWordCount() const noexcept
        {
            return word_count_;
        }

        /// @brief Sets a specific bit to \c 1.
        ///
        /// This function sets a specific bit in the bit span to \c 1.
        ///
        /// @param index The index of the bit to set.
        ///
        /// @pre The index must be within the bounds of the bit span.
        void SetBit(const size_t index) const noexcept
        {
            DCHECK_LT(index, word_count_ * kBitsPerWord);

            const size_t word = index / kBitsPerWord;
            const size_t bit = index % kBitsPerWord;
            data_[word] |= (Storage{1} << bit);
        }

        /// @brief Sets a range of bits to \c 1.
        ///
        /// This function sets a range of bits in the bit span to \c 1.
        ///
        /// @param range The range of bits to set.
        ///
        /// @pre Range must not be empty and must be within the bounds of the bit span.
        void SetBitRange(const TimeSlotRange& range) const noexcept
        {
            DCHECK(!range.IsEmpty());
            DCHECK_LE(range.GetEnd(), word_count_ * kBitsPerWord);

            const size_t first_word = range.GetStart() / kBitsPerWord;
            const size_t last_word = (range.GetEnd() - 1) / kBitsPerWord;

            const size_t start_bit = range.GetStart() % kBitsPerWord;
            const size_t end_bit = (range.GetEnd() - 1) % kBitsPerWord;

            // Case 1: entirely within one word
            if (first_word == last_word)
            {
                data_[first_word] |= BitsBetweenInclusive(start_bit, end_bit);
                return;
            }

            // Head.
            data_[first_word] |= HighBitsFrom(start_bit);

            const size_t second_word = first_word + 1;

#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_BIT_SPAN_USE_SIMD
            SimdType ones = SimdType(~Storage{0});

            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - ((last_word - second_word) % kSimdWidth);

            // SIMD over aligned region
            for (size_t w = second_word; w + kSimdWidth <= aligned_last; w += kSimdWidth)
            {
                xsimd::store_unaligned(&data_[w], ones);
            }

            // Scalar check for the remaining tail
            for (size_t w = aligned_last; w < last_word; ++w)
            {
                data_[w] = ~Storage{0};
            }
#else
            // scalar fallback
            for (size_t w = second_word; w < last_word; ++w)
            {
                data_[w] = ~Storage{0};
            }
#endif

            // Tail.
            data_[last_word] |= LowBitsTo(end_bit);
        }


        /// @brief Checks if a specific bit is set.
        ///
        /// This function checks if a specific bit in the bit span is set to \c 1.
        ///
        /// @param index The index of the bit to check.
        ///
        /// @pre The index must be within the bounds of the bit span.
        ///
        /// @return \c true if the bit is set, \c false otherwise.
        [[nodiscard]] bool IsBitSet(const size_t index) const noexcept
        {
            DCHECK_LT(index, word_count_ * kBitsPerWord);

            const size_t word = index / kBitsPerWord;
            const size_t bit = index % kBitsPerWord;
            return (data_[word] >> bit) & Storage{1};
        }

        /// @brief Checks if a range of bits is set.
        ///
        /// This function checks if all bits in a specified range are set to \c 1.
        ///
        /// @param range The range of bits to check.
        ///
        /// @pre Range must not be empty and must be within the bounds of the bit span.
        ///
        /// @return \c true if all bits in the range are set, \c false otherwise.
        [[nodiscard]] bool IsBitRangeSet(const TimeSlotRange& range) const noexcept
        {
            DCHECK(!range.IsEmpty());
            DCHECK_LE(range.GetEnd(), word_count_ * kBitsPerWord);

            const size_t first_word = range.GetStart() / kBitsPerWord;
            const size_t last_word = (range.GetEnd() - 1) / kBitsPerWord;

            const size_t start_bit = range.GetStart() % kBitsPerWord;
            const size_t end_bit = (range.GetEnd() - 1) % kBitsPerWord;

            // Range fits within a single word
            if (first_word == last_word)
            {
                Storage mask = BitsBetweenInclusive(start_bit, end_bit);
                return (data_[first_word] & mask) == mask;
            }

            // Head word
            Storage head_mask = HighBitsFrom(start_bit);
            if ((data_[first_word] & head_mask) != head_mask)
            {
                return false;
            }

            const size_t second_word = first_word + 1;

#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_BIT_SPAN_USE_SIMD
            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - ((last_word - second_word) % kSimdWidth);

            // SIMD over aligned region
            for (size_t w = second_word; w + kSimdWidth <= aligned_last; w += kSimdWidth)
            {
                SimdType vec = xsimd::load_unaligned(&data_[w]);
                if (!xsimd::all(vec == SimdType{~Storage{0}}))
                {
                    return false;
                }
            }

            // Scalar check for the remaining tail
            for (size_t w = aligned_last; w < last_word; ++w)
            {
                if (data_[w] != ~Storage{0})
                {
                    return false;
                }
            }
#else
            for (size_t w = second_word; w < last_word; ++w)
            {
                if (data_[w] != ~Storage{0})
                {
                    return false;
                }
            }
#endif
            // Tail word
            Storage tail_mask = LowBitsTo(end_bit);
            return (data_[last_word] & tail_mask) == tail_mask;
        }

        /// @brief Checks if a range of bits is clear.
        ///
        /// This function checks if all bits in a specified range are clear (set to \c 0).
        ///
        /// @param range The range of bits to check.
        ///
        /// @pre Range must not be empty and must be within the bounds of the bit span.
        ///
        /// @return \c true if all bits in the range are clear, \c false otherwise.
        [[nodiscard]] bool IsBitRangeClear(const TimeSlotRange& range) const noexcept
        {
            DCHECK(!range.IsEmpty());
            DCHECK_LE(range.GetEnd(), word_count_ * kBitsPerWord);

            const size_t first_word = range.GetStart() / kBitsPerWord;
            const size_t last_word = (range.GetEnd() - 1) / kBitsPerWord;

            const size_t start_bit = range.GetStart() % kBitsPerWord;
            const size_t end_bit = (range.GetEnd() - 1) % kBitsPerWord;

            // Case: Range fits entirely within one word
            if (first_word == last_word)
            {
                Storage mask = BitsBetweenInclusive(start_bit, end_bit);
                return (data_[first_word] & mask) == Storage{0};
            }

            // Head word: bits from start_bit to MSB
            Storage head_mask = HighBitsFrom(start_bit);
            if ((data_[first_word] & head_mask) != Storage{0})
            {
                return false;
            }

            const size_t second_word = first_word + 1;

            // SIMD check of full words in the middle
#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_BIT_SPAN_USE_SIMD
            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - ((last_word - second_word) % kSimdWidth);

            for (size_t w = second_word; w + kSimdWidth <= aligned_last; w += kSimdWidth)
            {
                SimdType vec = xsimd::load_unaligned(&data_[w]);
                if (!xsimd::all(vec == SimdType{0}))
                {
                    return false;
                }
            }

            for (size_t w = aligned_last; w < last_word; ++w)
            {
                if (data_[w] != Storage{0})
                {
                    return false;
                }
            }
#else
            // Scalar fallback: middle words must be entirely zero
            for (size_t w = second_word; w < last_word; ++w)
            {
                if (data_[w] != Storage{0})
                {
                    return false;
                }
            }
#endif

            // Tail word: bits from LSB up to end_bit
            Storage tail_mask = LowBitsTo(end_bit);
            return (data_[last_word] & tail_mask) == Storage{0};
        }

        /// @brief Clears a specific bit (sets it to \c 0).
        ///
        /// This function clears a specific bit in the bit span, setting it to \c 0.
        ///
        /// @param index The index of the bit to clear.
        ///
        /// @pre The index must be within the bounds of the bit span.
        void ClearBit(const size_t index) const noexcept
        {
            DCHECK_LT(index, word_count_ * kBitsPerWord);

            const size_t word = index / kBitsPerWord;
            const size_t bit = index % kBitsPerWord;
            data_[word] &= ~(Storage{1} << bit);
        }

        /// @brief Clears a range of bits (sets them to \c 0).
        ///
        /// This function clears a range of bits in the bit span, setting them to \c 0.
        ///
        /// @param range The range of bits to clear.
        ///
        /// @pre Range must not be empty and must be within the bounds of the bit span.
        void ClearBitRange(const TimeSlotRange& range) const noexcept
        {
            DCHECK(!range.IsEmpty());
            DCHECK_LE(range.GetEnd(), word_count_ * kBitsPerWord);

            const size_t first_word = range.GetStart() / kBitsPerWord;
            const size_t last_word = (range.GetEnd() - 1) / kBitsPerWord;

            const size_t start_bit = range.GetStart() % kBitsPerWord;
            const size_t end_bit = (range.GetEnd() - 1) % kBitsPerWord;

            // Case 1: entirely within one word
            if (first_word == last_word)
            {
                data_[first_word] &= ~BitsBetweenInclusive(start_bit, end_bit);
                return;
            }

            // Head.
            data_[first_word] &= ~HighBitsFrom(start_bit);

            const size_t second_word = first_word + 1;

#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_BIT_SPAN_USE_SIMD
            SimdType zeros = SimdType(Storage{0});

            // aligned_last is the first word we cannot include in a full SIMD block
            // SIMD loop will process words in [first_word+1, aligned_last), step kSimdWidth
            const size_t aligned_last = last_word - ((last_word - second_word) % kSimdWidth);

            // SIMD over aligned region
            for (size_t w = second_word; w + kSimdWidth <= aligned_last; w += kSimdWidth)
            {
                xsimd::store_unaligned(&data_[w], zeros);
            }

            // Scalar check for the remaining tail
            for (size_t w = aligned_last; w < last_word; ++w)
            {
                data_[w] = Storage{0};
            }
#else
            // scalar fallback
            for (size_t w = second_word; w < last_word; ++w)
            {
                data_[w] = Storage{0};
            }
#endif

            // Tail.
            data_[last_word] &= ~LowBitsTo(end_bit);
        }

        /// @brief Checks if a specific bit is cleared.
        ///
        /// This function checks if a specific bit in the bit span is cleared (set to \c 0).
        ///
        /// @param index The index of the bit to check.
        ///
        /// @pre The index must be within the bounds of the bit span.
        ///
        /// @return \c true if the bit is cleared, \c false otherwise.
        [[nodiscard]] bool IsBitCleared(const size_t index) const noexcept
        {
            DCHECK_LT(index, word_count_ * kBitsPerWord);

            const size_t word = index / kBitsPerWord;
            const size_t bit = index % kBitsPerWord;
            return ((data_[word] >> bit) & Storage{1}) == 0;
        }

        /// @brief Checks if a specific bit is set.
        ///
        /// This function checks if a specific bit in the bit span is set to \c 1.
        ///
        /// @param index The index of the bit to check.
        ///
        /// @pre The index must be within the bounds of the bit span.
        ///
        /// @return \c true if the bit is set, \c false otherwise.
        [[nodiscard]] bool GetBit(const size_t index) const noexcept
        {
            DCHECK_LT(index, word_count_ * kBitsPerWord);

            size_t word = index / kBitsPerWord;
            size_t bit = index % kBitsPerWord;
            return (data_[word] >> bit) & Storage{1};
        }

        /// @brief Toggles a specific bit (flips its value).
        ///
        /// This function toggles a specific bit in the bit span,
        /// flipping its value from \c 0 to \c 1 or from \c 1 to \c 0.
        ///
        /// @param index The index of the bit to toggle.
        ///
        /// @pre The index must be within the bounds of the bit span.
        void ToggleBit(const size_t index) const noexcept
        {
            DCHECK_LT(index, word_count_ * kBitsPerWord);

            const size_t word = index / kBitsPerWord;
            const size_t bit = index % kBitsPerWord;
            data_[word] ^= (Storage{1} << bit);
        }

        /// @brief Sets all bits in the bit span to \c 0.
        ///
        /// This function clears all bits in the bit span, setting them to \c 0.
        void ClearAll() const noexcept
        {
            std::memset(data_, 0x00, word_count_ * sizeof(Storage));
        }

        /// @brief Sets all bits in the bit span to \c 1.
        ///
        /// This function sets all bits in the bit span to \c 1.
        void SetAll() const noexcept
        {
            std::memset(data_, 0xFF, word_count_ * sizeof(Storage));
        }

        /// @brief Index operator.
        ///
        /// This operator allows access to a specific bit in the bit span using the \c [] operator.
        ///
        /// @param index The index of the bit to access.
        ///
        /// @pre The index must be within the bounds of the bit span.
        [[nodiscard]] bool operator[](const size_t index) const noexcept
        {
            return GetBit(index);
        }

    private:
#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_BIT_SPAN_USE_SIMD
        /// @brief The SIMD type used for vectorized operations.
        using SimdType = xsimd::batch<Storage>;

        /// @brief The Width of the SIMD type.
        static constexpr std::size_t kSimdWidth = SimdType::size;
#endif

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
        static constexpr Storage HighBitsFrom(const size_t bit) noexcept
        {
            DCHECK_LT(bit, kBitsPerWord);

            return ~Storage{0} << bit;
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
        static constexpr Storage LowBitsTo(const size_t bit) noexcept
        {
            DCHECK_LT(bit, kBitsPerWord);

            return (Storage{1} << (bit + 1)) - 1;
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
        static constexpr Storage BitsBetweenInclusive(const size_t from, const size_t to) noexcept
        {
            DCHECK_LE(from, to);
            DCHECK_LT(from, kBitsPerWord);
            DCHECK_LT(to, kBitsPerWord);

            return HighBitsFrom(from) & LowBitsTo(to);
        }

        Storage* data_;
        size_t word_count_;
    };
}

#endif
