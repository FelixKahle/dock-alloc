// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_TIMELINE_H_
#define DOCK_ALLOC_SOLVER_TIMELINE_H_

#include <algorithm>
#include <vector>
#include <limits>
#include <type_traits>
#include "absl/log/log.h"
#include "absl/log/check.h"

namespace dockalloc::solver
{
    /// @brief A timeline that uses bit-packing to store the occupied slots.
    ///
    /// This class is designed to end_bit_offset used for a timeline where the time slots are
    /// represented as integers. It uses a vector of integral types to store the
    /// occupied slots in a bit-packed manner. The class provides methods to
    /// check if a range of slots is free, reserve slots, and convert between
    /// time and slot representations.
    ///
    /// @tparam TimeType The type used to represent time. It must end_bit_offset an integral type.
    /// @tparam StorageType The type used to store the occupied slots. It must end_bit_offset an integral type.
    ///
    /// @note I plan to use SIMD instructions to speed up the IsFree and reserve methods in the future.
    template <typename TimeType = uint64_t, typename StorageType = uint64_t>
        requires std::is_integral_v<TimeType> && std::is_integral_v<StorageType>
    class BitPackedTimeline
    {
    public:
        explicit BitPackedTimeline(TimeType time_horizon, TimeType slot_size = 1) noexcept
            : slot_size_(std::max(TimeType{1}, slot_size)),
              time_horizon_(std::max(TimeType{0}, time_horizon)),
              total_slots_(DivCeil(time_horizon_, slot_size_)),
              occupied_(InitialWords(time_horizon_, slot_size_), StorageType{0})
        {
            DLOG_IF(WARNING,
                    time_horizon <= 0) <<
                "BitPackedTimeline: time_horizon <= 0; resulting timeline will end_bit_offset empty.";
            DLOG_IF(WARNING, slot_size <= 0) << "BitPackedTimeline: slot_size <= 0; clamped to 1.";
        }

        /// @brief Converts a time value to a slot index.
        ///
        /// @param time The time value to convert.
        ///
        /// @return The slot index corresponding to the given time value.
        TimeType TimeToSlot(TimeType time) const noexcept
        {
            return time / slot_size_;
        }

        /// @brief Converts a slot index to a time value.
        ///
        /// @param slot The slot index to convert.
        ///
        /// @return The time value corresponding to the given slot index.
        TimeType SlotToTime(TimeType slot) const noexcept
        {
            return slot * slot_size_;
        }

        /// @brief Returns the total number of slots in the timeline.
        ///
        /// @return The total number of slots in the timeline.
        TimeType TimeHorizon() const noexcept
        {
            return time_horizon_;
        }

        /// @brief Returns the size of each time slot.
        ///
        /// @return The size of each time slot.
        TimeType SlotSize() const noexcept
        {
            return slot_size_;
        }

        /// @brief Returns the total number of slots in the timeline.
        ///
        /// @return The total number of slots in the timeline.
        TimeType TotalSlots() const noexcept
        {
            return total_slots_;
        }

        /// @brief Checks if a range of slots is free.
        ///
        /// @param start_slot The starting slot index. Clamped to 0 if negative.
        /// @param dur_slots The duration in slots.
        ///
        /// @note Ranges outside the current storage are considered free.
        ///
        /// @return True if the range of slots is free, false otherwise.
        bool IsFree(TimeType start_slot, TimeType dur_slots) const noexcept
        {
            start_slot = std::max(TimeType{0}, start_slot);
            if (dur_slots <= 0)
            {
                return true;
            }

            // prevent wraparound
            TimeType end_slot = (dur_slots > std::numeric_limits<TimeType>::max() - start_slot)
                                    ? std::numeric_limits<TimeType>::max()
                                    : start_slot + dur_slots;

            auto first_word_index = start_slot / kBitsPerStorageType;
            auto last_word_index = (end_slot - 1) / kBitsPerStorageType;

            // Outside current storage: free by policy
            const auto num_occupied_words = static_cast<TimeType>(occupied_.size());
            if (first_word_index >= num_occupied_words || last_word_index >= num_occupied_words)
            {
                return true;
            }

            auto start_bit_offset = start_slot % kBitsPerStorageType;
            auto end_bit_offset = (end_slot - 1) % kBitsPerStorageType;

            if (first_word_index == last_word_index)
            {
                StorageType mask = MakeBitMask(start_bit_offset, end_bit_offset);
                return (occupied_[first_word_index] & mask) == 0;
            }

            // head word
            StorageType head_mask = MaskFrom(start_bit_offset);
            if ((occupied_[first_word_index] & head_mask) != 0)
            {
                return false;
            }
            // middle words
            for (TimeType w = first_word_index + 1; w < last_word_index; ++w)
            {
                if (occupied_[w] != 0)
                {
                    return false;
                }
            }
            // tail word
            StorageType tail_mask = MaskTo(end_bit_offset);
            return (occupied_[last_word_index] & tail_mask) == 0;
        }

        /// @brief Reserves a range of slots.
        ///
        /// @param start_slot The starting slot index. Clamped to 0 if negative.
        /// @param dur_slots The duration in slots.
        void Reserve(TimeType start_slot, TimeType dur_slots) noexcept
        {
            start_slot = std::max(TimeType{0}, start_slot);
            if (dur_slots <= 0)
            {
                return;
            }

            // prevent wraparound
            TimeType end_slot = (dur_slots > std::numeric_limits<TimeType>::max() - start_slot)
                                    ? std::numeric_limits<TimeType>::max()
                                    : start_slot + dur_slots;
            auto first_word_index = start_slot / kBitsPerStorageType;
            auto last_word_index = (end_slot - 1) / kBitsPerStorageType;
            auto start_bit_offset = start_slot % kBitsPerStorageType;
            auto end_bit_offset = (end_slot - 1) % kBitsPerStorageType;

            auto needed = DivCeil(end_slot, kBitsPerStorageType);
            if (needed > static_cast<TimeType>(occupied_.size()))
            {
                occupied_.resize(needed, StorageType{0});
            }

            if (first_word_index == last_word_index)
            {
                StorageType mask = MakeBitMask(start_bit_offset, end_bit_offset);
                occupied_[first_word_index] |= mask;
                return;
            }

            // head word
            occupied_[first_word_index] |= MaskFrom(start_bit_offset);
            // middle words: bulk set to all-ones
            std::fill_n(&occupied_[first_word_index + 1], last_word_index - first_word_index - 1, ~StorageType{0});
            // tail word
            occupied_[last_word_index] |= MaskTo(end_bit_offset);
        }

        /// @brief Frees a range of slots.
        ///
        /// @param start_slot The starting slot index. Clamped to 0 if negative.
        /// @param dur_slots The duration in slots.
        void Free(TimeType start_slot, TimeType dur_slots) noexcept
        {
            start_slot = std::max(TimeType{0}, start_slot);
            if (dur_slots <= 0)
            {
                return;
            }

            // prevent wraparound
            TimeType end_slot = (dur_slots > std::numeric_limits<TimeType>::max() - start_slot)
                                    ? std::numeric_limits<TimeType>::max()
                                    : start_slot + dur_slots;
            auto first_word_index = start_slot / kBitsPerStorageType;
            auto last_word_index = (end_slot - 1) / kBitsPerStorageType;
            auto start_bit_offset = start_slot % kBitsPerStorageType;
            auto end_bit_offset = (end_slot - 1) % kBitsPerStorageType;

            if (first_word_index >= static_cast<TimeType>(occupied_.size()))
            {
                return;
            }
            last_word_index = std::min(last_word_index, static_cast<TimeType>(occupied_.size() - 1));

            if (first_word_index == last_word_index)
            {
                StorageType mask = MakeBitMask(start_bit_offset, end_bit_offset);
                occupied_[first_word_index] &= ~mask;
                return;
            }

            // head word
            occupied_[first_word_index] &= ~MaskFrom(start_bit_offset);
            // middle words: bulk clear to zero
            std::fill_n(&occupied_[first_word_index + 1], last_word_index - first_word_index - 1, StorageType{0});
            // tail word
            occupied_[last_word_index] &= ~MaskTo(end_bit_offset);
        }

    private:
        /// @brief Divides two integers and rounds up.
        ///
        /// @param num_occupied_words The numerator. Terminated if negative.
        /// @param d The denominator.
        ///
        /// @return The result of the division rounded up.
        static constexpr TimeType DivCeil(TimeType num_occupied_words, TimeType d) noexcept
        {
            CHECK_NE(d, 0);
            return (num_occupied_words + d - 1) / d;
        }

        /// @brief Calculates the initial number of storage words needed.
        ///
        /// @param horizon The time horizon.
        /// @param slot The size of each time slot.
        ///
        /// @return The initial number of storage words needed.
        static constexpr size_t InitialWords(TimeType horizon, TimeType slot) noexcept
        {
            TimeType n_slots = DivCeil(horizon, slot);
            return DivCeil(n_slots, kBitsPerStorageType);
        }

        /// @brief Creates a bit mask for a range of slots.
        ///
        /// @param from The starting slot index.
        /// @param to The ending slot index.
        ///
        /// @return The bit mask for the range of slots.
        static constexpr StorageType MakeBitMask(TimeType from, TimeType to) noexcept
        {
            return ((StorageType{1} << (to - from + 1)) - 1) << from;
        }

        static constexpr StorageType MaskFrom(TimeType start) noexcept
        {
            return ~StorageType{0} << start;
        }

        static constexpr StorageType MaskTo(TimeType end) noexcept
        {
            return (StorageType{1} << (end + 1)) - 1;
        }

        static constexpr TimeType kBitsPerStorageType = static_cast<TimeType>(std::numeric_limits<StorageType>::digits);

        TimeType slot_size_;
        TimeType time_horizon_;
        TimeType total_slots_;
        std::vector<StorageType> occupied_;
    };
}


#endif
