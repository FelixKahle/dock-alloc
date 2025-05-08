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
    /// @brief A hierarchical bitset that tracks occupancy status over a range of discrete slots.
    ///
    /// The SlotTimeline is a multilevel bitmap structure optimized for efficient occupancy tracking,
    /// enabling fast single-slot queries and potential future support for range-based queries.
    ///
    /// It divides a linear space of slots into blocks and sub-blocks, maintaining summary layers for
    /// both free and occupied bits at higher levels. This enables future optimization of operations
    /// such as finding the first free block, determining continuous availability, and range scanning.
    ///
    /// @tparam SummaryDepth The number of summary levels in the hierarchy.
    /// @tparam Storage The unsigned integral type used to store occupancy bits (e.g., uint64_t).
    template <size_t SummaryDepth, typename Storage>
        requires std::unsigned_integral<Storage> && std::is_trivial_v<Storage>
    class SlotTimeline
    {
    public:
        /// @brief The count of bits in a single Storage word.
        static constexpr int kBitsPerWord = std::numeric_limits<Storage>::digits;

        /// @brief The number of levels in the timeline hierarchy.
        static constexpr size_t kSummaryDepth = SummaryDepth;

        /// @brief Constructor to create a SlotTimeline with a specified number of slots.
        ///
        /// @param slot_count The number of slots to track.
        /// @param occupied If true, initializes all slots as occupied; otherwise, initializes them as free.
        explicit SlotTimeline(const size_t slot_count = 0, const bool occupied = false) noexcept
            : SlotTimeline(std::make_index_sequence<SummaryDepth>{}, slot_count, occupied)
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
            return (bitmap_[word] >> bit) & Storage{1};
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
            return ((bitmap_[word] >> bit) & Storage{1}) == 0;
        }

    private:
        /// @brief Private constructor for internal use with compile-time index sequence.
        ///
        /// Constructs the SlotTimeline with the given number of slots and occupancy state. This constructor
        /// is invoked by the public constructor using a compile-time-generated `std::index_sequence`
        /// to instantiate each summary level.
        ///
        /// @tparam LevelIndex The compile-time indices for each level in the hierarchy.
        /// @param slot_count The number of base-level slots to manage.
        /// @param occupied Whether to initialize all slots as occupied (`true`) or free (`false`).
        template <size_t... LevelIndex>
        SlotTimeline(const std::index_sequence<LevelIndex...>, const size_t slot_count, const bool occupied) noexcept
            : slot_count_(slot_count),
              bitmap_(NumWordsAtLevel(slot_count, 0), occupied ? ~Storage{0} : Storage{0}),
              free_summaries_{MakeSummaryLevel<LevelType::Free, LevelIndex + 1>(slot_count, occupied)...},
              occupied_summaries_{MakeSummaryLevel<LevelType::Occupied, LevelIndex + 1>(slot_count, occupied)...}
        {
        }

        /// @brief Computes the number of Storage words required at a given level of the hierarchy.
        ///
        /// Each level of the timeline represents blocks of increasingly larger size (powers of kBitsPerWord).
        /// This function determines how many words are needed to represent a level, given the number of base-level slots.
        ///
        /// @param slot_count The number of slots at the base level.
        /// @param level The level in the hierarchy (0 = base level, 1 = first summary, ...).
        /// @return The number of Storage words needed to represent the occupancy at the given level.
        static constexpr size_t NumWordsAtLevel(const size_t slot_count, const size_t level) noexcept
        {
            size_t block_size = kBitsPerWord;
            for (size_t i = 0; i < level; ++i)
            {
                block_size *= kBitsPerWord;
            }
            return (slot_count + block_size - 1) / block_size;
        }

        /// @brief Returns the block size (in slots) at a specific depth in the hierarchy.
        ///
        /// For example, depth 0 corresponds to individual slots, depth 1 to blocks of `kBitsPerWord`,
        /// depth 2 to blocks of `kBitsPerWord^2`, and so on.
        ///
        /// @param depth The depth in the hierarchy (0 = slot level, 1 = first summary, ...).
        /// @return The number of base-level slots grouped by a block at the specified depth.
        static constexpr size_t BlockSizeAtDepth(const size_t depth) noexcept
        {
            size_t block_size = 1;
            for (size_t i = 0; i < depth; ++i)
            {
                block_size *= kBitsPerWord;
            }
            return block_size;
        }

        /// @brief Indicates the type of summary level to create.
        ///
        /// This enum is used to distinguish whether a summary level tracks occupied or free slots.
        enum class LevelType
        {
            /// @brief Summary level for free slots.
            Free,
            /// @brief Summary level for occupied slots.
            Occupied
        };

        /// @brief Generates a summary level vector initialized to either free or occupied state.
        ///
        /// Used to construct the hierarchy of summary levels for quick access to block-level free/occupied information.
        /// This method is templated on the level index and the type of summary (free or occupied).
        ///
        /// @tparam Type Whether to create a summary of free or occupied blocks.
        /// @tparam LevelIndex The depth level of the summary hierarchy (1 = first summary above base, etc.).
        ///
        /// @param slot_count The number of base-level slots being tracked.
        /// @param occupied Indicates whether the base level should be initialized as fully occupied.
        ///
        /// @return A vector of `Storage` words for the summary, initialized based on `occupied` and `Type`.
        template <LevelType Type, size_t LevelIndex>
        static std::vector<Storage> MakeSummaryLevel(const size_t slot_count, const bool occupied) noexcept
        {
            const bool fill = (Type == LevelType::Occupied) ? occupied : !occupied;
            return std::vector<Storage>(NumWordsAtLevel(slot_count, LevelIndex), fill ? ~Storage{0} : Storage{0});
        }

        size_t slot_count_;
        std::vector<Storage> bitmap_;
        std::array<std::vector<Storage>, SummaryDepth> free_summaries_;
        std::array<std::vector<Storage>, SummaryDepth> occupied_summaries_;
    };
}

#endif
