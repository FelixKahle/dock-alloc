// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_TIME_SLOT_RANGE_H_
#define DOCK_ALLOC_SOLVER_TIME_SLOT_RANGE_H_

#include <cstdint>

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
        constexpr TimeSlotRange(const TimeSlotRange& other) noexcept = default;

        /// @brief Move constructor.
        ///
        /// This constructor creates a new \c TimeSlotRange object by moving another.
        ///
        /// @param other The \c TimeSlotRange object to move.
        constexpr TimeSlotRange(TimeSlotRange&& other) noexcept = default;

        /// @brief Constructor.
        ///
        /// This constructor initializes a \c TimeSlotRange object with the specified start (inclusive) and end
        /// (exclusive) indices.
        ///
        /// @param start_inclusive The inclusive start index of the range.
        /// @param end_exclusive The exclusive end index of the range.
        explicit constexpr TimeSlotRange(const size_t start_inclusive, const size_t end_exclusive) noexcept
            : start_inclusive_(std::min(start_inclusive, end_exclusive)),
              end_exclusive_(std::max(start_inclusive, end_exclusive))
        {
        }

        /// @brief Getter for the start index.
        ///
        /// This function returns the inclusive start index of the range.
        ///
        /// @return The inclusive start index of the range.
        [[nodiscard]] constexpr size_t GetStart() const noexcept
        {
            return start_inclusive_;
        }

        /// @brief Getter for the end index.
        ///
        /// This function returns the exclusive end index of the range.
        ///
        /// @return The exclusive end index of the range.
        [[nodiscard]] constexpr size_t GetEnd() const noexcept
        {
            return end_exclusive_;
        }

        /// @brief Returns the length of the range.
        ///
        /// This function calculates the length of the range by subtracting the start index
        /// from the end index. The result is the number of slots in the range.
        ///
        /// @return The length of the range, calculated as end - start.
        [[nodiscard]] constexpr size_t Length() const noexcept
        {
            return end_exclusive_ - start_inclusive_;
        }

        /// @brief Checks if the range is empty.
        ///
        /// This function checks if the range is empty by comparing the start and end indices.
        /// If they are equal, the range is considered empty.
        ///
        /// @return \c true if the range is empty (start == end), \c false otherwise.
        [[nodiscard]] constexpr bool IsEmpty() const noexcept
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
        friend constexpr bool operator==(const TimeSlotRange& lhs, const TimeSlotRange& rhs) noexcept
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
        friend constexpr bool operator!=(const TimeSlotRange& lhs, const TimeSlotRange& rhs) noexcept
        {
            return !(lhs == rhs);
        }

    private:
        size_t start_inclusive_;
        size_t end_exclusive_;
    };
}

#endif
