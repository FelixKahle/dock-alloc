// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SLOT_TIMELINE_H_
#define DOCK_ALLOC_SLOT_TIMELINE_H_

#include <cstdint>
#include <limits>
#include <concepts>
#include <type_traits>
#include <array>
#include <vector>

namespace dockalloc::solver
{
    /// @brief A multi-level bitmap for fast slot allocation with hierarchical summaries.
    ///
    /// SlotTimeline tracks the occupancy of a number of slots using a hierarchical
    /// structure. Level 0 stores the raw bit-level occupancy, and each higher level stores
    /// coarser summaries (1 bit per Storage-word from the previous level).
    ///
    /// This design enables top-down skipping of large full/free regions with excellent
    /// performance and cache locality, avoiding pointer chasing.
    ///
    /// @tparam Depth Number of levels in the timeline hierarchy (must be > 0).
    /// @tparam Storage Unsigned integral type used to represent bits (e.g. uint64_t or uint8_t).
    template <size_t Depth, typename Storage>
        requires (Depth > 0) && std::unsigned_integral<Storage> && std::is_trivial_v<Storage>
    class SlotTimeline
    {
    public:
        /// @brief The count of bits in a single Storage word.
        static constexpr int kBitsPerWord = std::numeric_limits<Storage>::digits;

        /// @brief The number of levels in the timeline hierarchy.
        static constexpr size_t kDepth = Depth;

        /// @brief Constructor to create a SlotTimeline with a specified number of slots.
        ///
        /// @param slot_count The number of slots to track.
        /// @param occupied If true, initializes all slots as occupied; otherwise, initializes them as free.
        explicit SlotTimeline(const size_t slot_count = 0, const bool occupied = false) noexcept
            : SlotTimeline(std::make_index_sequence<Depth>{}, slot_count, occupied)
        {
        }

        /// @brief Returns the number of slots tracked by this SlotTimeline.
        ///
        /// @return The number of slots tracked.
        [[nodiscard]] size_t SlotCount() const noexcept
        {
            return slot_count_;
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

            size_t word = slot / kBitsPerWord;
            size_t bit = slot % kBitsPerWord;
            return (data_[0][word] >> bit) & Storage{1};
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
            // Slots we do not keep track of are
            // considered to be free by definition.
            if (slot >= slot_count_)
            {
                return true;
            }

            size_t word = slot / kBitsPerWord;
            size_t bit = slot % kBitsPerWord;
            return ((data_[0][word] >> bit) & Storage{1}) == 0;
        }

    private:
        /// @brief Constructs the SlotTimeline using a compile-time index sequence.
        ///
        /// This constructor is used to initialize the data structure with the specified
        /// number of slots and occupancy state as well as filling the data array with
        /// the appropriate levels.
        ///
        /// @tparam LevelIndex The level indices for the SlotTimeline.
        ///
        /// @param slot_count The number of slots to track.
        /// @param occupied If true, initializes all slots as occupied; otherwise, initializes them as free.
        template <size_t... LevelIndex>
        SlotTimeline(const std::index_sequence<LevelIndex...>, const size_t slot_count, const bool occupied) noexcept
            : slot_count_(slot_count), data_{MakeLevel<LevelIndex>(slot_count, occupied)...}
        {
        }

        /// @brief Calculates the number of words at a given level for a specified slot count.
        ///
        /// This function computes the number of Storage words needed to represent the occupancy
        /// of the slots at a specific level in the hierarchy.
        ///
        /// @param slot_count The number of slots to track.
        /// @param level The level in the hierarchy for which to calculate the number of words.
        ///
        /// @return The number of Storage words needed at the specified level.
        static constexpr size_t NumWordsAtLevel(const size_t slot_count, const size_t level) noexcept
        {
            size_t block_size = kBitsPerWord;
            for (size_t i = 0; i < level; ++i)
            {
                block_size *= kBitsPerWord;
            }
            return (slot_count + block_size - 1) / block_size;
        }

        /// @brief Calculates the size of a block at a given depth in the hierarchy.
        ///
        /// This function computes the size of a block at a specific depth in the hierarchy.
        ///
        /// @param depth The depth in the hierarchy for which to calculate the block size.
        ///
        /// @return The size of the block at the specified depth.
        static constexpr size_t BlockSizeAtDepth(const size_t depth) noexcept
        {
            size_t block_size = 1;
            for (size_t i = 0; i < depth; ++i)
            {
                block_size *= kBitsPerWord;
            }
            return block_size;
        }

        /// @brief Creates a level of the SlotTimeline with the specified occupancy state.
        ///
        /// This function initializes a level of the SlotTimeline with either all occupied or all free slots.
        ///
        /// @tparam LevelIndex The index of the level to create.
        ///
        /// @param slot_count The number of slots to track.
        /// @param occupied If true, initializes all slots as occupied; otherwise, initializes them as free.
        template <size_t LevelIndex>
        static std::vector<Storage> MakeLevel(const size_t slot_count, const bool occupied) noexcept
        {
            return std::vector<Storage>(NumWordsAtLevel(slot_count, LevelIndex), occupied ? ~Storage{0} : Storage{0});
        }

        size_t slot_count_;
        std::array<std::vector<Storage>, Depth> data_;
    };
}

#endif
