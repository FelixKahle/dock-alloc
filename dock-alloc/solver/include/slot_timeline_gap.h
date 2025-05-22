// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_SLOT_TIMELINE_GAP_H_
#define DOCK_ALLOC_SOLVER_SLOT_TIMELINE_GAP_H_

#include <optional>
#include <algorithm>

namespace dockalloc::solver
{
    /// @brief Represents a gap in a slot timeline.
    ///
    /// This class encapsulates a gap in a slot timeline, defined by the inclusive start
    /// and optional exclusive end indices [start, end).
    /// If the end index is not provided, the gap extends indefinitely.
    class SlotTimelineGap
    {
    public:
        /// @brief Copy constructor.
        ///
        /// This constructor creates a new \c SlotTimelineGap object as a copy of another.
        ///
        /// @param other The \c SlotTimelineGap object to copy.
        constexpr SlotTimelineGap(const SlotTimelineGap& other) noexcept = default;

        /// @brief Move constructor.
        ///
        /// This constructor creates a new \c SlotTimelineGap object by moving another.
        ///
        /// @param other The \c SlotTimelineGap object to move.
        constexpr SlotTimelineGap(SlotTimelineGap&& other) noexcept = default;

        /// @brief Constructor.
        ///
        /// This constructor initializes a \c SlotTimelineGap object with the specified start (inclusive) and optional end
        /// (exclusive) indices.
        /// If the end index is not provided, the gap extends indefinitely.
        /// In the case of end index being less than start index, the start and end indices are swapped.
        ///
        /// @param start_inclusive The inclusive start index of the gap.
        /// @param end_exclusive The optional exclusive end index of the gap.
        explicit constexpr SlotTimelineGap(const size_t start_inclusive, const std::optional<size_t> end_exclusive)
            : start_inclusive_(end_exclusive ? std::min(start_inclusive, *end_exclusive) : start_inclusive),
              end_exclusive_(end_exclusive ? std::optional{std::max(start_inclusive, *end_exclusive)} : std::nullopt)
        {
        }

        /// @brief Getter for the start index.
        ///
        /// This function returns the inclusive start index of the gap.
        ///
        /// @return The inclusive start index of the gap.
        [[nodiscard]] constexpr size_t GetStart() const noexcept
        {
            return start_inclusive_;
        }

        /// @brief Getter for the end index.
        ///
        /// This function returns the optional exclusive end index of the gap.
        ///
        /// @return The optional exclusive end index of the gap.
        [[nodiscard]] constexpr std::optional<size_t> GetEnd() const noexcept
        {
            return end_exclusive_;
        }

        /// @brief Checks if the gap is empty.
        ///
        /// This function checks if the gap is empty,
        /// which means that the end index is less than or equal to the start index.
        /// If the end index is not provided, the gap is not considered empty.
        ///
        /// @return \c true if the gap is empty, \c false otherwise.
        [[nodiscard]] constexpr bool IsEmpty() const noexcept
        {
            return end_exclusive_ ? *end_exclusive_ <= start_inclusive_ : false;
        }

        /// @brief Returns the length of the gap.
        ///
        /// This function calculates the length of the gap by subtracting the start index
        /// from the end index. If the end index is not provided, the length is not defined as
        /// the gap extends indefinitely, having no finite length.
        [[nodiscard]] constexpr std::optional<size_t> GetLength() const noexcept
        {
            return end_exclusive_ ? std::optional{*end_exclusive_ - start_inclusive_} : std::nullopt;
        }

        /// @brief Checks if the gap has an end index.
        ///
        /// This function checks if the gap has an exclusive end index.
        ///
        /// @return \c true if the gap has an end index, \c false otherwise.
        [[nodiscard]] constexpr bool HasEnd() const noexcept
        {
            return end_exclusive_.has_value();
        }

        /// @brief Equality operator.
        ///
        /// This operator checks if two \c SlotTimelineGap objects are equal.
        ///
        /// @param lhs The left-hand side \c SlotTimelineGap object.
        /// @param rhs The right-hand side \c SlotTimelineGap object.
        ///
        /// @return \c true if the gaps are equal (start and end indices match), \c false otherwise.
        friend constexpr bool operator==(const SlotTimelineGap& lhs, const SlotTimelineGap& rhs) noexcept
        {
            return lhs.GetStart() == rhs.GetStart() && lhs.GetEnd() == rhs.GetEnd();
        }

        /// @brief Inequality operator.
        ///
        /// This operator checks if two \c SlotTimelineGap objects are not equal.
        ///
        /// @param lhs The left-hand side \c SlotTimelineGap object.
        /// @param rhs The right-hand side \c SlotTimelineGap object.
        ///
        /// @return \c true if the gaps are not equal (start or end indices differ), \c false otherwise.
        friend constexpr bool operator!=(const SlotTimelineGap& lhs, const SlotTimelineGap& rhs) noexcept
        {
            return !(lhs == rhs);
        }

        // Delete the copy and move assignment operators to prevent copying or moving,
        // as the class is designed to be immutable after construction.

        SlotTimelineGap& operator=(const SlotTimelineGap& other) = delete;
        SlotTimelineGap& operator=(SlotTimelineGap&& other) = delete;

    private:
        size_t start_inclusive_;
        std::optional<size_t> end_exclusive_;
    };
}

#endif
