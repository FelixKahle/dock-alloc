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
#include <ranges>
#include "absl/log/check.h"
#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD
#include "xsimd/xsimd.hpp"
#endif

namespace dockalloc::solver
{
    /// @brief Represents a range of slots in a \c SlotTimeline.
    ///
    /// This class encapsulate a range of slots, defined by the inclusive start
    /// and exclusive end indices [start, end).
    class TimeSlotRange
    {
    public:
        /// @brief Copy constructor.
        ///
        /// This constructor creates a new \c TimeSlotRange object as a copy of another.
        ///
        /// @param other The \c TimeSlotRange object to copy.
        TimeSlotRange(const TimeSlotRange& other) noexcept = default;

        /// @brief Move constructor.
        ///
        /// This constructor creates a new \c TimeSlotRange object by moving another.
        ///
        /// @param other The \c TimeSlotRange object to move.
        TimeSlotRange(TimeSlotRange&& other) noexcept = default;

        /// @brief Constructor.
        ///
        /// This constructor initializes a \c TimeSlotRange object with the specified start (inclusive) and end
        /// (exclusive) indices.
        ///
        /// @param start_inclusive The inclusive start index of the range.
        /// @param end_exclusive The exclusive end index of the range.
        explicit TimeSlotRange(const size_t start_inclusive, const size_t end_exclusive) noexcept
            : start_inclusive_(std::min(start_inclusive, end_exclusive)),
              end_exclusive_(std::max(start_inclusive, end_exclusive))
        {
        }

        /// @brief Getter for the start index.
        ///
        /// This function returns the inclusive start index of the range.
        ///
        /// @return The inclusive start index of the range.
        [[nodiscard]] size_t GetStart() const noexcept
        {
            return start_inclusive_;
        }

        /// @brief Getter for the end index.
        ///
        /// This function returns the exclusive end index of the range.
        ///
        /// @return The exclusive end index of the range.
        [[nodiscard]] size_t GetEnd() const noexcept
        {
            return end_exclusive_;
        }

        /// @brief Returns the length of the range.
        ///
        /// This function calculates the length of the range by subtracting the start index
        /// from the end index. The result is the number of slots in the range.
        ///
        /// @return The length of the range, calculated as end - start.
        [[nodiscard]] size_t Length() const noexcept
        {
            return end_exclusive_ - start_inclusive_;
        }

        /// @brief Checks if the range is empty.
        ///
        /// This function checks if the range is empty by comparing the start and end indices.
        /// If they are equal, the range is considered empty.
        ///
        /// @return \c true if the range is empty (start == end), \c false otherwise.
        [[nodiscard]] bool IsEmpty() const noexcept
        {
            return start_inclusive_ == end_exclusive_;
        }

        /// @brief Compares two \c TimeSlotRange objects for equality.
        ///
        /// This function checks if two \c TimeSlotRange objects are equal by comparing their
        /// start and end indices. If both the start and end indices are equal, the ranges are considered equal.
        ///
        /// @param lhs The first \c TimeSlotRange object to compare.
        /// @param rhs The second \c TimeSlotRange object to compare.
        ///
        /// @return \c true if the ranges are equal (start and end indices match), \c false otherwise.
        friend bool operator==(const TimeSlotRange& lhs, const TimeSlotRange& rhs) noexcept
        {
            return lhs.start_inclusive_ == rhs.start_inclusive_ && lhs.end_exclusive_ == rhs.end_exclusive_;
        }

        /// @brief Compares two \c TimeSlotRange objects for inequality.
        ///
        /// This function checks if two \c TimeSlotRange objects are not equal by comparing their
        /// start and end indices. If either the start or end indices are different,
        /// the ranges are considered not equal.
        ///
        /// @param lhs The first \c TimeSlotRange object to compare.
        /// @param rhs The second \c TimeSlotRange object to compare.
        ///
        /// @return \c true if the ranges are not equal (start or end indices differ), \c false otherwise.
        friend bool operator!=(const TimeSlotRange& lhs, const TimeSlotRange& rhs) noexcept
        {
            return !(lhs == rhs);
        }

    private:
        size_t start_inclusive_;
        size_t end_exclusive_;
    };

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
            DCHECK_NE(data, nullptr) << "Data pointer cannot be null";
        }

        /// @brief Constructor.
        ///
        /// This constructor creates a \c SlotTimelineBitSpan object from a vector of Storage words.
        ///
        /// @param vec The vector of Storage words representing the bit span.
        explicit SlotTimelineBitSpan(std::vector<Storage>& vec) noexcept
            : data_(vec.data()), word_count_(vec.size())
        {
        }

        /// @brief Constructor.
        ///
        /// This constructor creates a \c SlotTimelineBitSpan object from a span of Storage words.
        ///
        /// @param span The span of Storage words representing the bit span.
        explicit SlotTimelineBitSpan(std::span<Storage> span) noexcept
            : data_(span.data()), word_count_(span.size())
        {
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
            DCHECK(index / kBitsPerWord < word_count_) << "Index out of bounds";

            size_t word = index / kBitsPerWord;
            size_t bit = index % kBitsPerWord;
            return (data_[word] >> bit) & Storage{1};
        }

        /// @brief Sets a specific bit to \c 1.
        ///
        /// This function sets a specific bit in the bit span to \c 1.
        ///
        /// @param index The index of the bit to set.
        ///
        /// @pre The index must be within the bounds of the bit span.
        void SetBit(const size_t index) noexcept
        {
            DCHECK(index / kBitsPerWord < word_count_) << "Index out of bounds";

            size_t word = index / kBitsPerWord;
            size_t bit = index % kBitsPerWord;
            data_[word] |= (Storage{1} << bit);
        }

        /// @brief Clears a specific bit (sets it to \c 0).
        ///
        /// This function clears a specific bit in the bit span, setting it to \c 0.
        ///
        /// @param index The index of the bit to clear.
        ///
        /// @pre The index must be within the bounds of the bit span.
        void ClearBit(const size_t index) noexcept
        {
            DCHECK(index / kBitsPerWord < word_count_) << "Index out of bounds";

            size_t word = index / kBitsPerWord;
            size_t bit = index % kBitsPerWord;
            data_[word] &= ~(Storage{1} << bit);
        }

        /// @brief Toggles a specific bit (flips its value).
        ///
        /// This function toggles a specific bit in the bit span,
        /// flipping its value from \c 0 to \c 1 or from \c 1 to \c 0.
        ///
        /// @param index The index of the bit to toggle.
        ///
        /// @pre The index must be within the bounds of the bit span.
        void ToggleBit(const size_t index) noexcept
        {
            DCHECK(index / kBitsPerWord < word_count_) << "Index out of bounds";

            size_t word = index / kBitsPerWord;
            size_t bit = index % kBitsPerWord;
            data_[word] ^= (Storage{1} << bit);
        }

        /// @brief Sets all bits in the bit span to \c 0.
        ///
        /// This function clears all bits in the bit span, setting them to \c 0.
        void ClearAll() noexcept
        {
            std::memset(data_.data(), 0x00, word_count_ * sizeof(Storage));
        }

        /// @brief Sets all bits in the bit span to \c 1.
        ///
        /// This function sets all bits in the bit span to \c 1.
        void SetAll() noexcept
        {
            std::memset(data_.data(), 0xFF, word_count_ * sizeof(Storage));
        }

        /// @brief Index operator.
        ///
        /// This operator allows access to a specific bit in the bit span using the \c [] operator.
        ///
        /// @param index The index of the bit to access.
        [[nodiscard]] bool operator[](const size_t index) const noexcept
        {
            return GetBit(index);
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

        Storage* data_;
        size_t word_count_;
    };

    template <size_t SummaryDepth, typename Storage>
        requires std::unsigned_integral<Storage>
    class SlotTimeline;

    template <typename Storage>
        requires std::unsigned_integral<Storage>
    class SlotTimeline<0, Storage>
    {
    public:
        /// @brief The count of bits in a single Storage word.
        static constexpr int kBitsPerWord = std::numeric_limits<Storage>::digits;

        /// @brief The number of summary levels.
        static constexpr size_t kSummaryDepth = 0;

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

            SlotTimelineBitSpan<Storage> bit_span(bitmap_);
            return bit_span.GetBit(slot);
        }

        [[nodiscard]] bool IsOccupied(const TimeSlotRange& range) const noexcept
        {
            // TODO: Implement.
            return false;
        }

        /// @brief Marks the given slot as occupied.
        ///
        /// @param slot The slot to mark as occupied.
        /// @param occupied If \c true, all new slots except the given slot are considered occupied.
        void Occupy(const size_t slot, const bool occupied = false) noexcept
        {
            // Slots are zero indexed, so we need to add 1 to the slot count.
            EnsureSlotCount(slot + 1, occupied);

            size_t word = slot / kBitsPerWord;
            size_t bit = slot % kBitsPerWord;
            bitmap_[word] |= (Storage{1} << bit);
        }

        void Occupy(const TimeSlotRange& range) noexcept
        {
            // TODO: Implement.
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

        [[nodiscard]] bool IsFree(const TimeSlotRange& range) const noexcept
        {
            // TODO: Implement.
            return false;
        }

        /// @brief Marks the given slot as free.
        ///
        /// @param slot The slot to mark as free.
        /// @param occupied If true, all new slots except the given slot are considered occupied.
        void Free(const size_t slot, const bool occupied = false)
        {
            // Slots we do not keep track of are
            // considered to be free by definition.
            if (slot >= slot_count_)
            {
                return;
            }

            size_t word = slot / kBitsPerWord;
            size_t bit = slot % kBitsPerWord;
            bitmap_[word] &= ~(Storage{1} << bit);
        }

        void Free(const TimeSlotRange& range) noexcept
        {
            // TODO: Implement.
        }

        /// @brief Sets all slots to occupied.
        void SetAllOccupied() noexcept
        {
            std::memset(bitmap_.data(), 0xFF, bitmap_.size() * sizeof(Storage));
        }

        /// @brief Sets all slots to free.
        void SetAllFree() noexcept
        {
            std::memset(bitmap_.data(), 0x00, bitmap_.size() * sizeof(Storage));
        }

        /// @brief Ensures that the \c SlotTimeline has enough storage for the given slot count.
        ///
        /// @param count The number of slots to ensure storage for.
        /// @param occupied If true, all new slots are considered occupied. Default is \c false.
        void EnsureSlotCount(const size_t count, const bool occupied = false) noexcept
        {
            // We do not need to resize if the new slot count is less than or equal to the current one,
            // because we already have enough storage to store the requested slot amount.
            if (count <= slot_count_)
            {
                return;
            }

            const size_t old_words = bitmap_.size();
            const size_t new_words = NumWordsForSlots(count);

            bitmap_.resize(new_words, occupied ? ~Storage{0} : Storage{0});

            if (old_words > 0)
            {
                const size_t start_bit = slot_count_ % kBitsPerWord;
                const size_t end_bit = kBitsPerWord - 1;
                const Storage mask = BitsBetweenInclusive(start_bit, end_bit);

                bitmap_[old_words - 1] = (bitmap_[old_words - 1] & ~mask) | (occupied ? mask : Storage{0});
            }

            slot_count_ = count;
        }

    private:
#if DOCK_ALLOC_SOLVER_SLOT_TIMELINE_USE_SIMD
        /// @brief The SIMD type used for vectorized operations.
        using SimdType = xsimd::batch<Storage>;

        /// @brief The number of slots that can be processed in parallel using SIMD.
        static constexpr std::size_t kSimdWidth = SimdType::size;
#endif

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

    template <typename Storage>
        requires std::unsigned_integral<Storage>
    class SlotTimeline<1, Storage>
    {
    public:
        /// @brief The count of bits in a single Storage word.
        static constexpr int kBitsPerWord = std::numeric_limits<Storage>::digits;

        /// @brief The number of summary levels.
        static constexpr size_t kSummaryDepth = 1;

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
              bitmap_(NumWordsAtLevel(slot_count, 0), occupied ? ~Storage{0} : Storage{0}),
              free_summary_(NumWordsAtLevel(slot_count, 1), occupied ? Storage{0} : ~Storage{0}),
              occupied_summary_(NumWordsAtLevel(slot_count, 1), occupied ? ~Storage{0} : Storage{0})
        {
        }

    private:
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

        size_t slot_count_;
        std::vector<Storage> bitmap_;
        std::vector<Storage> free_summary_;
        std::vector<Storage> occupied_summary_;
    };

    template <size_t SummaryDepth, typename Storage>
        requires std::unsigned_integral<Storage>
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
