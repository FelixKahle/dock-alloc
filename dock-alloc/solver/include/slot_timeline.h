// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_SLOT_TIMELINE_H_
#define DOCK_ALLOC_SOLVER_SLOT_TIMELINE_H_

/// @brief This enables/disables whether the SlotTimeline class uses SIMD
#ifndef DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD
#define DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD 1
#endif

#include <limits>
#include <algorithm>
#include <concepts>
#include <type_traits>
#include <vector>
#include <memory>
#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD
#include "xsimd/xsimd.hpp"
#endif

namespace dockalloc::solver
{
    template <typename T>
        requires std::unsigned_integral<T> && std::is_trivial_v<T>
    class SlotTimeline
    {
    public:
        /// @brief The amount of bits taken up by the storage type.
        static constexpr int kBitsPerStorage = std::numeric_limits<T>::digits;

        /// @brief Constructs a SlotTimeline with the given slot count and occupancy.
        ///
        /// @param slot_count The number of slots to track.
        /// @param occupied If true, all slots are considered occupied.
        explicit SlotTimeline(const size_t slot_count = 0, const bool occupied = false) noexcept
            : slot_count_(slot_count),
              bitmap_(NumWordsForSlots(slot_count), occupied ? ~T{0} : T{0})
        {
        }

        /// @brief Returns the number of slots tracked by this SlotTimeline.
        ///
        /// @return The number of slots tracked.
        [[nodiscard]] size_t SlotCount() const noexcept
        {
            return slot_count_;
        }

        /// @brief Ensures that the SlotTimeline has enough storage for the given slot count.
        ///
        /// @param count The number of slots to ensure storage for.
        /// @param occupied If true, all new slots are considered occupied.
        void EnsureSlotCount(const size_t count, const bool occupied = false) noexcept
        {
            if (count <= slot_count_)
            {
                return;
            }

            const size_t old_words = bitmap_.size();
            const size_t new_words = NumWordsForSlots(count);

            bitmap_.resize(new_words, occupied ? ~T{0} : T{0});

            if (new_words == old_words && old_words > 0)
            {
                const size_t start_bit = slot_count_ % kBitsPerStorage;
                const size_t end_bit = (count - 1) % kBitsPerStorage;
                const T mask = MakeBitMask(start_bit, end_bit);
                bitmap_[old_words - 1] = occupied ? (bitmap_.back() | mask) : (bitmap_.back() & ~mask);
            }

            slot_count_ = count;
        }

        /// @brief Marks the given slot as occupied.
        ///
        /// @param slot The slot to mark as occupied.
        /// @param occupied If true, all new slots except the given slot are considered occupied.
        void OccupySlot(const size_t slot, const bool occupied = false)
        {
            EnsureSlotCount(slot + 1, occupied);

            size_t word = slot / kBitsPerStorage;
            size_t bit = slot % kBitsPerStorage;
            bitmap_[word] |= (T{1} << bit);
        }

        /// @brief Occupies a range of slots.
        ///
        /// @param start The starting slot of the range.
        /// @param count The number of slots in the range.
        void OccupySlotRange(const size_t start, const size_t count) noexcept
        {
            if (count == 0)
            {
                return;
            }

            EnsureSlotCount(start + count);

            const size_t end = start + count;
            const size_t first_word = start / kBitsPerStorage;
            const size_t last_word = (end - 1) / kBitsPerStorage;
            const size_t start_bit = start % kBitsPerStorage;
            const size_t end_bit = (end - 1) % kBitsPerStorage;

            if (first_word == last_word)
            {
                T mask = MakeBitMask(start_bit, end_bit);
                bitmap_[first_word] |= mask;
                return;
            }

            T head_mask = MaskFrom(start_bit);
            bitmap_[first_word] |= head_mask;

#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD
            simd_type ones(~T{0});
            const size_t simd_limit = last_word - ((last_word - first_word - 1) % kSimdWidth);
            for (size_t w = first_word + 1; w + kSimdWidth <= simd_limit; w += kSimdWidth)
            {
                xsimd::store_unaligned(&bitmap_[w], ones);
            }

            for (size_t w = simd_limit; w < last_word; ++w)
            {
                bitmap_[w] = ~T{0};
            }
#else
            for (size_t w = first_word + 1; w < last_word; ++w)
            {
                bitmap_[w] = ~T{0};
            }
#endif
            T tail_mask = MaskTo(end_bit);
            bitmap_[last_word] |= tail_mask;
        }

        /// @brief Marks the given slot as free.
        ///
        /// @param slot The slot to mark as free.
        /// @param occupied If true, all new slots except the given slot are considered occupied.
        void FreeSlot(const size_t slot, const bool occupied = false)
        {
            EnsureSlotCount(slot + 1, occupied);

            size_t word = slot / kBitsPerStorage;
            size_t bit = slot % kBitsPerStorage;
            bitmap_[word] &= ~(T{1} << bit);
        }

        void FreeSlotRange(const size_t start, const size_t count)
        {
            if (count == 0)
            {
                return;
            }

            EnsureSlotCount(start + count);

            const size_t end = start + count;
            const size_t first_word = start / kBitsPerStorage;
            const size_t last_word = (end - 1) / kBitsPerStorage;
            const size_t start_bit = start % kBitsPerStorage;
            const size_t end_bit = (end - 1) % kBitsPerStorage;

            if (first_word == last_word)
            {
                T mask = MakeBitMask(start_bit, end_bit);
                bitmap_[first_word] &= ~mask;
                return;
            }

            T head_mask = MaskFrom(start_bit);
            bitmap_[first_word] &= ~head_mask;

#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD
            simd_type zeros(T{0});
            const size_t simd_limit = last_word - ((last_word - first_word - 1) % kSimdWidth);
            for (size_t w = first_word + 1; w + kSimdWidth <= simd_limit; w += kSimdWidth)
            {
                xsimd::store_unaligned(&bitmap_[w], zeros);
            }

            for (size_t w = simd_limit; w < last_word; ++w)
            {
                bitmap_[w] = T{0};
            }
#else
            for (size_t w = first_word + 1; w < last_word; ++w)
            {
                bitmap_[w] = T{0};
            }
#endif
            T tail_mask = MaskTo(end_bit);
            bitmap_[last_word] &= ~tail_mask;
        }

        /// @brief Sets all slots to occupied.
        void SetAllOccupied() noexcept
        {
            std::memset(bitmap_.data(), 0xFF, bitmap_.size() * sizeof(T));
        }

        /// @brief Sets all slots to free.
        void SetAllFree() noexcept
        {
            std::memset(bitmap_.data(), 0x00, bitmap_.size() * sizeof(T));
        }

        /// @brief Checks if the given slot is occupied.
        ///
        /// @param slot The slot to check.
        ///
        /// @return True if the slot is occupied, false otherwise.
        ///
        /// @note Slots that are not tracked by this SlotTimeline are considered not occupied.
        [[nodiscard]] bool IsOccupied(const size_t slot) const noexcept
        {
            // Slots we do not keep track of are
            // considered to be free by definition.
            if (slot >= slot_count_)
            {
                return false;
            }

            size_t word = slot / kBitsPerStorage;
            size_t bit = slot % kBitsPerStorage;
            return (bitmap_[word] >> bit) & T{1};
        }

        /// @brief Checks if the given range of slots is fully occupied.
        ///
        /// @param start The starting slot of the range.
        /// @param count The number of slots in the range.
        ///
        /// @return True if the range of slots is occupied, false otherwise.
        ///
        /// @note Slots that are not tracked by this SlotTimeline are considered not occupied.
        [[nodiscard]] bool IsOccupied(const size_t start, const size_t count) const noexcept
        {
            // A zero-length range is always free by definition.
            // Also, if the start index is beyond the tracked range, everything requested is implicitly free,
            // so the range cannot be fully occupied.
            if (count == 0 || start >= slot_count_)
            {
                return false;
            }

            // Prevent out-of-bounds or wraparound access:
            // if the range overruns, it can't be fully occupied.
            if (count > slot_count_ - start)
            {
                return false;
            }

            // Now the range is safe to check.
            const size_t end = start + count;

            // Identify which storage words are involved.
            const size_t first_word = start / kBitsPerStorage;
            const size_t last_word = (end - 1) / kBitsPerStorage;

            // Compute bit offsets within those words.
            const size_t start_bit = start % kBitsPerStorage;
            const size_t end_bit = (end - 1) % kBitsPerStorage;

            // If the range fits entirely within a single word, use a single mask to check it.
            if (first_word == last_word)
            {
                // Mask the relevant bit range and ensure all those bits are 1 (i.e., occupied).
                T mask = MakeBitMask(start_bit, end_bit);
                return (bitmap_[first_word] & mask) == mask;
            }

            // Check head word: ensure all bits from start_bit to end of word are 1.
            T head_mask = MaskFrom(start_bit);
            if ((bitmap_[first_word] & head_mask) != head_mask)
            {
                return false;
            }

#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD
            const size_t simd_limit = last_word - ((last_word - first_word - 1) % kSimdWidth);
            for (size_t w = first_word + 1; w + kSimdWidth <= simd_limit; w += kSimdWidth)
            {
                simd_type vec = xsimd::load_unaligned(&bitmap_[w]);
                if (!xsimd::all(vec == simd_type(~T{0})))
                {
                    return false;
                }
            }

            for (size_t w = simd_limit; w < last_word; ++w)
            {
                if (bitmap_[w] != ~T{0})
                {
                    return false;
                }
            }
#else
            // Check all full words in the middle: they must be entirely one.
            for (size_t w = first_word + 1; w < last_word; ++w)
            {
                if (bitmap_[w] != ~T{0})
                {
                    return false;
                }
            }
#endif

            // Check tail word: ensure all bits from bit 0 to end_bit are 1.
            T tail_mask = MaskTo(end_bit);
            return (bitmap_[last_word] & tail_mask) == tail_mask;
        }

        /// @brief Checks if the given slot is free.
        ///
        /// @param slot The slot to check.
        ///
        /// @return True if the slot is free, false otherwise.
        ///
        /// @note Slots that are not tracked by this SlotTimeline are considered free.
        [[nodiscard]] bool IsFree(const size_t slot) const noexcept
        {
            if (slot >= slot_count_)
            {
                return true;
            }

            size_t word = slot / kBitsPerStorage;
            size_t bit = slot % kBitsPerStorage;
            return ((bitmap_[word] >> bit) & T{1}) == 0;
        }

        /// @brief Checks if the given range of slots is fully free.
        ///
        /// @param start The starting slot of the range.
        /// @param count The number of slots in the range.
        ///
        /// @return True if the range of slots is free, false otherwise.
        ///
        /// @note Slots that are not tracked by this SlotTimeline are considered free.
        [[nodiscard]] bool IsFree(const size_t start, const size_t count) const noexcept
        {
            // A zero-length range is always free by definition.
            // Also, if the start index is beyond the tracked range, everything requested is implicitly free.
            if (count == 0 || start >= slot_count_)
            {
                return true;
            }

            // Clamp the requested count to avoid reading past the end of the bitmap.
            // This also protects against overflow in `start + count`.
            const size_t max_count = slot_count_ - start;
            const size_t real_count = std::min(count, max_count);
            const size_t end = start + real_count;

            // Identify which storage words are involved.
            const size_t first_word = start / kBitsPerStorage;
            const size_t last_word = (end - 1) / kBitsPerStorage;

            // Compute bit offsets within those words.
            const size_t start_bit = start % kBitsPerStorage;
            const size_t end_bit = (end - 1) % kBitsPerStorage;

            // If the range fits entirely within a single word, use a single mask to check it.
            if (first_word == last_word)
            {
                // Mask the relevant bit range and ensure all those bits are 0 (i.e., free).
                T mask = MakeBitMask(start_bit, end_bit);
                return (bitmap_[first_word] & mask) == T{0};
            }

            T head_mask = MaskFrom(start_bit);
            if ((bitmap_[first_word] & head_mask) != T{0})
            {
                return false;
            }

#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD
            const size_t simd_limit = last_word - ((last_word - first_word - 1) % kSimdWidth);
            for (size_t w = first_word + 1; w + kSimdWidth <= simd_limit; w += kSimdWidth)
            {
                simd_type vec = xsimd::load_unaligned(&bitmap_[w]);
                if (!xsimd::all(vec == simd_type(T{0})))
                {
                    return false;
                }
            }

            for (size_t w = simd_limit; w < last_word; ++w)
            {
                if (bitmap_[w] != T{0})
                {
                    return false;
                }
            }
#else
            // Check all full words in the middle: they must be entirely zero.
            for (size_t w = first_word + 1; w < last_word; ++w)
            {
                if (bitmap_[w] != T{0})
                {
                    return false;
                }
            }
#endif

            // Check tail word: ensure all bits from bit 0 to end_bit are 0.
            T tail_mask = MaskTo(end_bit);
            return (bitmap_[last_word] & tail_mask) == T{0};
        }

    private:
#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD
        using simd_type = xsimd::batch<T>;
        static constexpr std::size_t kSimdWidth = simd_type::size;
#endif

        /// @brief Returns the number of storage words needed to store the given slot amount.
        ///
        /// @param slot_amount The amount of slots.
        ///
        /// @return The number of storage words needed.
        static constexpr size_t NumWordsForSlots(size_t slot_amount) noexcept
        {
            return (slot_amount + kBitsPerStorage - 1) / kBitsPerStorage;
        }

        /// @brief Creates a bitmask with bits from the given bit index to the most significant bit set to 1.
        ///
        /// @param bit The starting bit index (inclusive).
        ///
        /// @return A mask with bits [bit, kBitsPerStorage-1] set to 1, all lower bits 0.
        static constexpr T MaskFrom(const size_t bit) noexcept
        {
            return ~T{0} << bit;
        }

        /// @brief Creates a bitmask with bits from the least significant bit to the given bit index set to 1.
        ///
        /// @param bit The ending bit index (inclusive).
        ///
        /// @return A mask with bits [0, bit] set to 1, all higher bits 0.
        static constexpr T MaskTo(const size_t bit) noexcept
        {
            return (T{1} << (bit + 1)) - 1;
        }

        /// @brief Creates a bitmask with bits in the closed interval [from, to] set to 1.
        ///
        /// @param from The starting bit index (inclusive).
        /// @param to The ending bit index (inclusive).
        ///
        /// @return A mask with bits [from, to] set to 1, all others 0.
        static constexpr T MakeBitMask(const size_t from, const size_t to) noexcept
        {
            return MaskFrom(from) & MaskTo(to);
        }

        size_t slot_count_;
        std::vector<T> bitmap_;
    };
}

#endif
