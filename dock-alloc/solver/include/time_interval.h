// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_INCLUDE_TIME_INTERVAL_H_
#define DOCK_ALLOC_SOLVER_INCLUDE_TIME_INTERVAL_H_

#include <type_traits>
#include <algorithm>
#include <optional>
#include <format>
#include "absl/strings/str_format.h"

namespace dockalloc::solver
{
    /// @brief Represents a closed time interval [\p start, \p end].
    ///
    /// The \c TimeInterval class models a closed interval of time, where both the \p start and \p end
    /// points are inclusive. It is a value-type utility that can be used to represent periods,
    /// ranges, or durations in a consistent and type-safe manner.
    ///
    /// The constructor automatically normalizes the interval by ensuring that the \p start is always
    /// less than or equal to the \p end, regardless of the order of inputs. This guarantees a well-formed
    /// interval without requiring the caller to pre-sort the values.
    ///
    /// The class is immutable after construction: assignment operators are explicitly deleted to
    /// prevent reassigning the time interval after creation. However, copying and moving at
    /// construction time are allowed, making it safe to pass \c TimeInterval objects by value.
    ///
    /// @tparam TimeType A scalar arithmetic type representing time values (e.g., \c int, \c float, \c double).
    ///
    /// @author Felix Kahle (felix.kahle21@gmail.com)
    template <typename TimeType>
        requires std::is_arithmetic_v<TimeType>
    class TimeInterval
    {
    public:
        /// @brief Copy constructor.
        ///
        /// Constructs a new \c TimeInterval object as a copy of an existing one.
        ///
        /// @param other The \c TimeInterval object to copy.
        constexpr TimeInterval(const TimeInterval& other) noexcept = default;

        /// @brief Move constructor.
        ///
        /// Constructs a new \c TimeInterval object by moving an existing one.
        ///
        /// @param other The \c TimeInterval object to move.
        constexpr TimeInterval(TimeInterval&& other) noexcept = default;

        /// @brief Constructs a \c TimeInterval object with the specified \a start and \a end times.
        ///
        /// The constructor takes two time values and normalizes the interval by ensuring that
        /// the \p start time is less than or equal to the \p end time.
        ///
        /// @param start The start time of the interval.
        /// @param end The end time of the interval.
        constexpr explicit TimeInterval(const TimeType start, const TimeType end) noexcept
            : start_(std::min(start, end)), end_(std::max(start, end))
        {
        }

        /// @brief Getter for the start time of the interval.
        ///
        /// Returns the start time of the interval.
        ///
        /// @return The start time of the interval.
        [[nodiscard]] constexpr TimeType GetStart() const noexcept
        {
            return start_;
        }

        /// @brief Getter for the end time of the interval.
        ///
        /// Returns the end time of the interval.
        ///
        /// @return The end time of the interval.
        [[nodiscard]] constexpr TimeType GetEnd() const noexcept
        {
            return end_;
        }

        /// @brief Getter for the duration of the interval.
        ///
        /// Returns the duration of the interval, which is the difference between the end and start times.
        ///
        /// @return The duration of the interval.
        [[nodiscard]] constexpr TimeType GetDuration() const noexcept
        {
            return end_ - start_;
        }

        /// @brief Checks if the interval is empty.
        ///
        /// Returns \c true if the interval is empty (i.e., start and end times are equal), \c false otherwise.
        [[nodiscard]] constexpr bool IsEmpty() const noexcept
        {
            return start_ == end_;
        }

        /// @brief Gets the midpoint of the interval.
        ///
        /// Returns the midpoint of the interval, which is calculated as the average of the start and end times.
        ///
        /// @return The midpoint of the interval.
        [[nodiscard]] constexpr TimeType GetMidpoint() const noexcept
        {
            // floating point types do not overflow.
            // dividing them this way will yield more accurate results.
            if constexpr (std::is_floating_point_v<TimeType>)
            {
                return (start_ + end_) / static_cast<TimeType>(2);
            }
            else
            {
                return start_ + (end_ - start_) / 2;
            }
        }

        /// @brief Checks if a given time value is contained within the interval.
        ///
        /// Returns \c true if the specified time value is within the interval (inclusive), \c false otherwise.
        ///
        /// @tparam OtherTimeType The time type of the value to check.
        ///
        /// @param value The time value to check.
        ///
        /// @return \c true if the value is contained within the interval, \c false otherwise.
        template <typename OtherTimeType>
            requires std::is_arithmetic_v<OtherTimeType>
        [[nodiscard]] bool Contains(OtherTimeType value) const noexcept
        {
            return value >= GetStart() && value <= GetEnd();
        }

        /// @brief Checks whether this interval fully contains another interval.
        ///
        /// Returns \c true if the entire \p other interval lies within the bounds
        /// of this interval (i.e., its start is not before this start, and its end is not after this end).
        ///
        /// @tparam OtherTimeType The arithmetic type of the other interval's time values.
        ///
        /// @param other The interval to check for containment.
        ///
        /// @return \c true if this interval fully contains the \p other interval, \c false otherwise.
        template <typename OtherTimeType>
            requires std::is_arithmetic_v<OtherTimeType>
        [[nodiscard]] constexpr bool Contains(const TimeInterval<OtherTimeType>& other) const noexcept
        {
            return Contains(other.GetStart()) && Contains(other.GetEnd());
        }

        /// @brief Checks whether this time interval intersects with another time interval.
        ///
        /// @tparam OtherTimeType The type of the other time interval.
        /// @param other The other time interval to check for intersection.
        ///
        /// @return \c true if the intervals intersect, \c false otherwise.
        template <typename OtherTimeType>
            requires std::is_arithmetic_v<OtherTimeType>
        [[nodiscard]] constexpr bool Intersects(const TimeInterval<OtherTimeType>& other) const noexcept
        {
            return !(GetEnd() < other.GetStart() || other.GetEnd() < GetStart());
        }

        /// @brief Returns the intersection of this \c TimeInterval with another \c TimeInterval.
        ///
        /// @tparam OtherTimeType The type of the other \c TimeInterval.
        ///
        /// @param other The other \c TimeInterval to find the intersection with.
        ///
        /// @note If the intervals do not intersect, this function returns an empty \c std::optional.
        ///
        /// @return \c std::optional<TimeInterval> containing the intersection interval, or empty if they do not intersect.
        template <typename OtherTimeType>
            requires std::is_arithmetic_v<OtherTimeType>
        [[nodiscard]] constexpr std::optional<TimeInterval> Intersection(
            const TimeInterval<OtherTimeType>& other) const noexcept
        {
            if (!Intersects(other))
            {
                return {};
            }

            TimeType s = std::max(GetStart(), static_cast<TimeType>(other.GetStart()));
            TimeType e = std::min(GetEnd(), static_cast<TimeType>(other.GetEnd()));
            return TimeInterval(s, e);
        }

        /// @brief Returns a new \c TimeInterval shifted by a specified value.
        ///
        /// @tparam OtherTimeType The type of the shift value.
        ///
        /// @param delta The value to shift the \c TimeInterval by.
        ///
        /// @return A new shifted \c TimeInterval object.
        template <typename OtherTimeType>
            requires std::is_arithmetic_v<OtherTimeType>
        [[nodiscard]] constexpr TimeInterval<decltype(TimeType{} + OtherTimeType{})> ShiftBy(
            OtherTimeType delta) const noexcept
        {
            using R = decltype(TimeType{} + OtherTimeType{});
            return TimeInterval<R>(GetStart() + delta, GetEnd() + delta);
        }

        /// @brief Clamps the \c TimeInterval to fit within a specified boundary.
        ///
        /// @tparam OtherTimeType The type of the boundary \c TimeInterval.
        ///
        /// @param boundary The boundary \c TimeInterval to clamp to.
        ///
        /// @note This function returns \c std::optional<TimeInterval> to indicate whether the clamping was successful.
        ///
        /// @return \c std::optional<TimeInterval> if the clamped interval if successful, or an empty optional if failed.
        template <typename OtherTimeType>
            requires std::is_arithmetic_v<OtherTimeType>
        [[nodiscard]] constexpr std::optional<TimeInterval> Clamp(
            const TimeInterval<OtherTimeType>& boundary) const noexcept
        {
            const TimeType clamped_start = std::max(GetStart(), static_cast<TimeType>(boundary.GetStart()));
            const TimeType clamped_end = std::min(GetEnd(), static_cast<TimeType>(boundary.GetEnd()));

            if (clamped_start > clamped_end)
            {
                return {};
            }

            return TimeInterval(clamped_start, clamped_end);
        }

        /// @brief Hash function for \c absl::flat_hash_* containers.
        ///
        /// @tparam H The Abseil hash state.
        /// @param h The initial hash state.
        /// @param time_interval The \c TimeInterval object to hash.
        ///
        /// @return The updated hash state.
        template <typename H>
        friend constexpr H AbslHashValue(H h, const TimeInterval& time_interval) noexcept
        {
            return H::combine(std::move(h), time_interval.GetStart(), time_interval.GetEnd());
        }

        /// @brief Equality operator.
        ///
        /// Compares two \c TimeInterval objects for equality.
        /// Two intervals are considered equal if their start and end times are the same.
        ///
        /// @param lhs The left-hand side \c TimeInterval object.
        /// @param rhs The right-hand side \c TimeInterval object.
        ///
        /// @return \c true if the intervals are equal, \c false otherwise.
        template <typename OtherTimeType>
            requires std::is_arithmetic_v<OtherTimeType>
        friend bool operator==(const TimeInterval& lhs, const TimeInterval<OtherTimeType>& rhs) noexcept
        {
            return lhs.GetStart() == rhs.GetStart() && lhs.GetEnd() == rhs.GetEnd();
        }

        /// @brief Inequality operator.
        ///
        /// Compares two \c TimeInterval objects for inequality.
        /// Two intervals are considered unequal if their start or end times differ.
        ///
        /// @param lhs The left-hand side \c TimeInterval object.
        /// @param rhs The right-hand side \c TimeInterval object.
        ///
        /// @return \c true if the intervals are not equal, \c false otherwise.
        template <typename OtherTimeType>
            requires std::is_arithmetic_v<OtherTimeType>
        friend bool operator!=(const TimeInterval& lhs, const TimeInterval<OtherTimeType>& rhs) noexcept
        {
            return !(lhs == rhs);
        }

        /// @brief Absl::Format function for stringification.
        ///
        /// This function allows the \c TimeInterval object to be formatted as a string using
        /// the \c absl::Format function.
        ///
        /// @param sink The sink to which the formatted string will be written.
        /// @param interval The \c TimeInterval object to format.
        template <typename Sink>
        friend void AbslStringify(Sink& sink, const TimeInterval& interval) noexcept
        {
            absl::Format(&sink, "[%v, %v]", interval.start_, interval.end_);
        }

        // Delete copy and move assignment operators to prevent reassigning the interval.
        // We want to keep the class immutable after construction.

        TimeInterval& operator=(const TimeInterval& other) noexcept = delete;
        TimeInterval& operator=(TimeInterval&& other) noexcept = delete;

    private:
        TimeType start_;
        TimeType end_;
    };

    /// @brief Comparator for sorting time intervals by their start time.
    ///
    /// This struct provides a comparison operator that can be used to sort \c TimeInterval objects
    /// based on their start times. It is useful for algorithms that require ordering of time intervals.
    ///
    /// @tparam LhsTimeType The time type of the left-hand side interval.
    /// @tparam RhsTimeType The time type of the right-hand side interval.
    ///
    /// @author Felix Kahle (felix.kahle21@gmail.com)
    template <typename LhsTimeType, typename RhsTimeType>
        requires std::is_arithmetic_v<LhsTimeType> && std::is_arithmetic_v<RhsTimeType>
    struct CompareTimeIntervalByStart
    {
        /// @brief Invokes the comparison operator.
        ///
        /// This function compares two \c TimeInterval objects based on their start times.
        ///
        /// @param lhs The left-hand side \c TimeInterval object.
        /// @param rhs The right-hand side \c TimeInterval object.
        ///
        /// @return \c true if the start time of \p lhs is less than that of \p rhs, \c false otherwise.
        [[nodiscard]] constexpr bool operator()(const TimeInterval<LhsTimeType>& lhs,
                                                const TimeInterval<RhsTimeType>& rhs) const
        {
            return lhs.GetStart() < rhs.GetStart();
        }
    };
}

#endif
