// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_SLOT_TIMELINE_H_
#define DOCK_ALLOC_SOLVER_SLOT_TIMELINE_H_

#ifndef DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD
#define DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD 1
#endif

#include <cstdint>
#include <limits>
#include <concepts>
#include <type_traits>
#include <array>
#include <vector>

namespace dockalloc::solver
{
    template <size_t SummaryDepth, typename Storage>
        requires std::unsigned_integral<Storage> && std::is_trivial_v<Storage>
    class SlotTimeline;

    template <typename Storage>
        requires std::unsigned_integral<Storage> && std::is_trivial_v<Storage>
    class SlotTimeline<0, Storage>
    {
    public:
        /// @brief The count of bits in a single Storage word.
        static constexpr int kBitsPerWord = std::numeric_limits<Storage>::digits;

        /// @brief Constructor.
        ///
        /// This constructor initializes the SlotTimeline with a specified number of slots.
        /// It creates a bitmap of the specified size, where each slot is represented by a bit.
        /// The bitmap is initialized to either occupied or free, depending on the \p occupied parameter.
        ///
        /// @param slot_count The number of slots to be tracked.
        /// @param occupied If \c true, all slots are initialized as occupied; otherwise, they are free.
        explicit SlotTimeline(const size_t slot_count = 0, const bool occupied = false) noexcept
            : slot_count_(slot_count),
              bitmap_(NumWordsForSlots(slot_count), occupied ? ~Storage{0} : Storage{0})
        {
        }

        /// @brief Returns the number of slots tracked by this SlotTimeline.
        ///
        /// This function returns the number of slots that are being tracked by this SlotTimeline.
        ///
        /// @return The number of slots tracked.
        [[nodiscard]] size_t SlotCount() const noexcept
        {
            return slot_count_;
        }

        /// @brief Checks if a specific slot is occupied.
        ///
        /// This function checks if a specific slot is occupied in the SlotTimeline.
        ///
        /// @param slot The index of the slot to check.
        ///
        /// @return \c true if the slot is occupied, \c false otherwise.
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

        /// @brief Checks if a specific slot is free.
        ///
        /// This function checks if a specific slot is free in the SlotTimeline.
        ///
        /// @param slot The index of the slot to check.
        ///
        /// @return \c true if the slot is free, \c false otherwise.
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
        /// @brief Calculates the number of words needed to store a given number of slots.
        ///
        /// This function computes the number of Storage words required to store a specified
        /// number of slots. It takes into account the number of bits in each Storage word.
        ///
        /// @param slot_amount The number of slots to be stored.
        ///
        /// @return The number of Storage words needed to store the specified number of slots.
        static constexpr size_t NumWordsForSlots(const size_t slot_amount) noexcept
        {
            return (slot_amount + kBitsPerWord - 1) / kBitsPerWord;
        }

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
            return bit < kBitsPerWord ? ~Storage{0} << bit : Storage{0};
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
            return bit < kBitsPerWord ? (Storage{1} << (bit + 1)) - 1 : ~Storage{0};
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
        /// @return A bitmask with bits [\p from, \p to] set to \c 1 and all other bits set to \c 0.
        static constexpr Storage BitsBetweenInclusive(const size_t from, const size_t to) noexcept
        {
            return HighBitsFrom(from) & LowBitsTo(to);
        }


        size_t slot_count_;
        std::vector<Storage> bitmap_;
    };

    template <size_t SummaryDepth, typename Storage>
        requires std::unsigned_integral<Storage> && std::is_trivial_v<Storage>
    class SlotTimeline
    {
    public:
        /// @brief The count of bits in a single Storage word.
        static constexpr int kBitsPerWord = std::numeric_limits<Storage>::digits;

        /// @brief The number of summary levels.
        static constexpr size_t kSummaryDepth = SummaryDepth;

        /// @brief Constructor.
        ///
        /// This constructor initializes the SlotTimeline with a specified number of slots.
        /// It creates a bitmap of the specified size, where each slot is represented by a bit.
        /// The bitmap is initialized to either occupied or free, depending on the \p occupied parameter.
        ///
        /// @param slot_count The number of slots to be tracked.
        /// @param occupied If \c true, all slots are initialized as occupied; otherwise, they are free.
        explicit SlotTimeline(const size_t slot_count = 0, const bool occupied = false) noexcept
            : SlotTimeline(std::make_index_sequence<SummaryDepth>{}, slot_count, occupied)
        {
        }

        /// @brief Returns the number of slots tracked by this SlotTimeline.
        ///
        /// This function returns the number of slots that are being tracked by this SlotTimeline.
        ///
        /// @return The number of slots tracked.
        [[nodiscard]] size_t SlotCount() const noexcept
        {
            return slot_count_;
        }

        /// @brief Checks if a specific slot is occupied.
        ///
        /// This function checks if a specific slot is occupied in the SlotTimeline.
        ///
        /// @param slot The index of the slot to check.
        ///
        /// @return \c true if the slot is occupied, \c false otherwise.
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

        /// @brief Checks if a specific slot is free.
        ///
        /// This function checks if a specific slot is free in the SlotTimeline.
        ///
        /// @param slot The index of the slot to check.
        ///
        /// @return \c true if the slot is free, \c false otherwise.
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
        /// @brief Actual constructor.
        ///
        /// This constructor initializes the \c SlotTimeline with a specified number of slots
        /// and creates the summary levels.
        ///
        /// @tparam LevelIndex A sequence of indices [0, SummaryDepth).
        /// @param slot_count The number of slots to be tracked.
        /// @param occupied If \c true, all slots are initialized as occupied; otherwise, they are free.
        template <size_t... LevelIndex>
        SlotTimeline(const std::index_sequence<LevelIndex...>, const size_t slot_count, const bool occupied) noexcept
            : slot_count_(slot_count),
              bitmap_(NumWordsAtLevel(slot_count, 0), occupied ? ~Storage{0} : Storage{0}),
              free_summaries_{MakeSummaryLevel<LevelType::Free, LevelIndex + 1>(slot_count, occupied)...},
              occupied_summaries_{MakeSummaryLevel<LevelType::Occupied, LevelIndex + 1>(slot_count, occupied)...}
        {
        }

        /// @brief Computes the number of Storage words required at a given level of the SlotTimeline hierarchy.
        ///
        /// Each level of the SlotTimeline hierarchy groups slots into exponentially larger blocks.
        /// This function calculates how many such blocks (i.e., Storage words) are needed to cover
        /// the total number of base-level slots at a specified level.
        ///
        /// At level `l`, a single Storage word summarizes `kBitsPerWord^l` base slots.
        ///
        /// @param slot_count The total number of slots at the base level (depth 0).
        /// @param level The level in the summary hierarchy (0 = base level, 1 = first summary, ...).
        ///
        /// @return The number of Storage words required to cover all base slots at the given level.
        static constexpr size_t NumWordsAtLevel(const size_t slot_count, const size_t level) noexcept
        {
            size_t block_size = kBitsPerWord;
            for (size_t i = 0; i < level; ++i)
            {
                block_size *= kBitsPerWord;
            }
            return (slot_count + block_size - 1) / block_size;
        }

        /// @brief Computes the block size, in terms of base-level slots, represented by a single bit at a given summary depth.
        ///
        /// At depth `d`, one bit summarizes a block of `kBitsPerWord^d` base-level slots.
        /// This function returns that block size, which is essential for range-skipping logic
        /// in top-down traversal of the timeline hierarchy.
        ///
        /// @param depth The summary hierarchy depth (0 = base level, 1 = first summary, etc.).
        ///
        /// @return The number of base-level slots represented by a single bit at the given depth.
        static constexpr size_t BlockSizeAtDepth(const size_t depth) noexcept
        {
            size_t block_size = 1;
            for (size_t i = 0; i < depth; ++i)
            {
                block_size *= kBitsPerWord;
            }
            return block_size;
        }

        /// @brief Specifies the semantic type of summary level being constructed.
        ///
        /// Used as a tag for distinguishing between free and occupied summaries.
        enum class LevelType
        {
            /// @brief Summary level for free slots.
            Free,
            /// @brief Summary level for occupied slots.
            Occupied
        };

        /// @brief Constructs a summary level bitmap with a default initialization pattern.
        ///
        /// Each summary level is a coarse-grained bitmap that encodes block-level status information.
        /// Depending on whether it tracks free or occupied slots, this function initializes it to either
        /// all-0s or all-1s depending on the \p occupied flag and the \c LevelType.
        ///
        /// @tparam Type The kind of summary level to construct (Free or Occupied).
        /// @tparam LevelIndex The index of the level in the hierarchy (1 = first summary above base).
        /// @param slot_count The total number of base-level slots managed.
        /// @param occupied If true, base-level slots are considered occupied; otherwise, free.
        ///
        /// @return A vector of Storage words representing the summary level, initialized accordingly.
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
