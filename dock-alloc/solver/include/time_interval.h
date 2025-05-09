// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_TIME_INTERVAL_H_
#define DOCK_ALLOC_SOLVER_TIME_INTERVAL_H_

#include <type_traits>
#include <concepts>
#include <algorithm>
#include <optional>
#include "absl/strings/str_format.h"

namespace dockalloc::solver
{
    /// @brief A class representing a half-open time interval.
    ///
    /// This class represents a half-open time interval [start, end), where the start time is inclusive
    /// and the end time is exclusive. It provides methods to create intervals, check for containment,
    /// compute the midpoint, duration, and intersection with other intervals.
    ///
    /// @tparam TimeType The type of the time values. It must be an unsigned integral type.
    ///
    /// @author Felix Kahle (felix.kahle21@gmail.com)
    /// @date May 09, 2025
    template <typename TimeType>
        requires std::unsigned_integral<TimeType>
    class TimeInterval
    {
    public:
        /// @brief Copy constructor.
        ///
        /// Constructs the interval by copying another \c TimeInterval.
        ///
        /// @param other The \c TimeInterval to copy.
        constexpr TimeInterval(const TimeInterval& other) = default;

        /// @brief Move constructor.
        ///
        /// Constructs the interval by moving another \c TimeInterval.
        ///
        /// @param other The \c TimeInterval to move.
        constexpr TimeInterval(TimeInterval&& other) = default;

        /// @brief Constructor.
        ///
        /// Constructs the interval with the given start and end times.
        /// The start time is inclusive, and the end time is exclusive, and the
        /// constructor ensures that the start time is less than or equal to the end time.
        /// If the start time is greater than the end time, they are swapped.
        ///
        /// @param inclusive_start The start time of the interval (inclusive).
        /// @param exclusive_end The end time of the interval (exclusive).
        constexpr explicit TimeInterval(const TimeType inclusive_start, const TimeType exclusive_end)
            : start_time_inclusive_(std::min<TimeType>(inclusive_start, exclusive_end)),
              end_time_exclusive_(std::max<TimeType>(inclusive_start, exclusive_end))
        {
        }

        /// @brief Getter for the start time.
        ///
        /// Returns the inclusive start time of the interval.
        ///
        ///@return The inclusive start time of the interval.
        [[nodiscard]] constexpr TimeType GetStart() const noexcept
        {
            return start_time_inclusive_;
        }

        /// @brief Getter for the end time.
        ///
        /// Returns the exclusive end time of the interval.
        ///
        ///@return The exclusive end time of the interval.
        [[nodiscard]] constexpr TimeType GetEnd() const noexcept
        {
            return end_time_exclusive_;
        }

        /// @brief Computes the midpoint of the interval.
        ///
        /// Returns the midpoint of the interval, which is the average of the start and end times.
        ///
        /// @tparam ReturnTimeType The type of the return value. It must be an arithmetic type.
        ///
        /// @return The midpoint of the interval.
        template <typename ReturnTimeType = TimeType>
            requires std::is_arithmetic_v<ReturnTimeType>
        [[nodiscard]] constexpr ReturnTimeType Midpoint() const noexcept
        {
            // Floating point types cannot overflow, so we can safely use the average.
            // It will yield more accurate results than the alternative formula
            // midpoint = start + (end - start) / 2 used for integral types.
            if constexpr (std::is_floating_point_v<ReturnTimeType>)
            {
                return (static_cast<ReturnTimeType>(start_time_inclusive_) +
                    static_cast<ReturnTimeType>(end_time_exclusive_)) / ReturnTimeType{2};
            }

            // To guard against overflow, we use the following formula:
            // midpoint = start + (end - start) / 2
            return static_cast<ReturnTimeType>(start_time_inclusive_) +
                (static_cast<ReturnTimeType>(end_time_exclusive_ - start_time_inclusive_) / ReturnTimeType{2});
        }

        /// @brief Checks if the interval is empty.
        ///
        /// An interval is considered empty if its inclusive start time is equal to its exclusive end time,
        /// meaning it spans zero units of time.
        ///
        /// @return \c true if the interval is empty, \c false otherwise.
        [[nodiscard]] constexpr bool IsEmpty() const noexcept
        {
            return start_time_inclusive_ == end_time_exclusive_;
        }

        /// @brief Computes the duration of the interval.
        ///
        /// Returns the duration of the interval as the difference between the exclusive end
        /// and the inclusive start. For a half-open interval \c [start, end), the result is
        /// guaranteed to be non-negative.
        ///
        /// @return The duration of the interval.
        [[nodiscard]] constexpr TimeType Duration() const noexcept
        {
            return end_time_exclusive_ - start_time_inclusive_;
        }

        /// @brief Checks if a given time value is contained within the interval.
        ///
        /// Returns \c true if the specified time value is within the interval (inclusive start, exclusive end),
        /// \c false otherwise.
        ///
        /// @tparam OtherTimeType The time type of the value to check.
        ///
        /// @param value The time value to check.
        ///
        /// @return \c true if the value is contained within the interval, \c false otherwise.
        template <typename OtherTimeType>
            requires std::convertible_to<OtherTimeType, TimeType>
        [[nodiscard]] bool Contains(OtherTimeType value) const noexcept
        {
            return value >= start_time_inclusive_ && value < end_time_exclusive_;
        }

        /// @brief Checks if another interval is fully contained within this interval.
        ///
        /// For half-open intervals [start, end), this method returns \c true if the other interval's
        /// start is greater than or equal to this interval's start, and its end is less than or equal to this interval's end.
        ///
        /// @tparam OtherTimeType The time type of the other interval.
        /// @param other The interval to check for containment.
        ///
        /// @return \c true if \p other is fully contained within this interval, \c false otherwise.
        template <typename OtherTimeType>
            requires std::unsigned_integral<OtherTimeType>
        [[nodiscard]] constexpr bool ContainsInterval(const TimeInterval<OtherTimeType>& other) const noexcept
        {
            return other.start_time_inclusive_ >= start_time_inclusive_
                && other.end_time_exclusive_ <= end_time_exclusive_;
        }

        /// @brief Checks whether this time interval intersects with another time interval.
        ///
        /// @tparam OtherTimeType The type of the other time interval.
        /// @param other The other time interval to check for intersection.
        ///
        /// @return \c true if the intervals intersect, \c false otherwise.
        template <typename OtherTimeType>
            requires std::unsigned_integral<OtherTimeType>
        [[nodiscard]] constexpr bool Intersects(const TimeInterval<OtherTimeType>& other) const noexcept
        {
            return std::max(start_time_inclusive_, static_cast<TimeType>(other.GetStart())) <
                std::min(end_time_exclusive_, static_cast<TimeType>(other.GetEnd()));
        }

        /// @brief Returns the intersection of this \c TimeInterval with another \c TimeInterval.
        ///
        /// @tparam OtherTimeType The type of the other \c TimeInterval.
        /// @tparam ReturnTimeType The type of the return value. Must be an unsigned integral type.
        ///
        /// @param other The other \c TimeInterval to find the intersection with.
        ///
        /// @note If the intervals do not intersect, this function returns an empty \c std::optional.
        ///
        /// @return \c std::optional<TimeInterval> with the intersection interval, or empty if they do not intersect.
        template <typename OtherTimeType, typename ReturnTimeType = TimeType>
            requires std::unsigned_integral<OtherTimeType>
        [[nodiscard]] constexpr std::optional<TimeInterval<ReturnTimeType>> Intersection(
            const TimeInterval<OtherTimeType>& other) const noexcept
        {
            const ReturnTimeType start = std::max(static_cast<ReturnTimeType>(start_time_inclusive_),
                                                  static_cast<ReturnTimeType>(other.GetStart()));
            const ReturnTimeType end = std::min(static_cast<ReturnTimeType>(end_time_exclusive_),
                                                static_cast<ReturnTimeType>(other.GetEnd()));

            if (start >= end)
            {
                return std::nullopt;
            }

            return TimeInterval<ReturnTimeType>(start, end);
        }

        /// @brief Clamps the \c TimeInterval to fit within a specified boundary.
        ///
        /// The resulting interval is the intersection of this interval with the boundary.
        /// If there is no overlap, returns \c std::nullopt.
        ///
        /// @tparam OtherTimeType The type of the boundary \c TimeInterval.
        ///
        /// @return \c std::optional<TimeInterval> if overlap exists, or std::nullopt otherwise.
        template <typename OtherTimeType>
            requires std::unsigned_integral<OtherTimeType>
        [[nodiscard]] constexpr std::optional<TimeInterval<TimeType>> Clamp(
            const TimeInterval<OtherTimeType>& boundary) const noexcept
        {
            const TimeType clamped_start = std::max(start_time_inclusive_, static_cast<TimeType>(boundary.GetStart()));
            const TimeType clamped_end = std::min(end_time_exclusive_, static_cast<TimeType>(boundary.GetEnd()));

            if (clamped_start >= clamped_end)
            {
                return std::nullopt;
            }

            return TimeInterval(clamped_start, clamped_end);
        }


        /// @brief Compares two intervals for equality.
        ///
        /// Compares the start and end times of two intervals to determine if they are equal.
        /// Two intervals are considered equal if their start and end times are the same.
        ///
        /// @param lhs The left-hand side interval.
        /// @param rhs The right-hand side interval.
        ///
        /// @return \c true if the intervals are equal, \c false otherwise.
        template <typename OtherTimeType>
            requires std::unsigned_integral<OtherTimeType>
        friend constexpr bool operator ==(const TimeInterval& lhs, const TimeInterval<OtherTimeType>& rhs) noexcept
        {
            return lhs.GetStart() == rhs.GetStart()
                && lhs.GetEnd() == rhs.GetEnd();
        }

        /// @brief Compares two intervals for inequality.
        ///
        /// Compares the start and end times of two intervals to determine if they are not equal.
        /// Two intervals are considered not equal if their start or end times are different.
        ///
        /// @param lhs The left-hand side interval.
        /// @param rhs The right-hand side interval.
        ///
        /// @return \c true if the intervals are not equal, \c false otherwise.
        template <typename OtherTimeType>
            requires std::unsigned_integral<OtherTimeType>
        friend constexpr bool operator !=(const TimeInterval& lhs, const TimeInterval<OtherTimeType>& rhs) noexcept
        {
            return !(lhs == rhs);
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
            return H::combine(std::move(h), time_interval.start_time_inclusive_, time_interval.end_time_exclusive_);
        }

        // TimeInterval is designed to be non-copyable and non-movable
        // to meet an immutable design.

        TimeInterval& operator=(const TimeInterval&) = delete;
        TimeInterval& operator=(TimeInterval&&) = delete;

        /// @brief Absl::Format function for stringification.
        ///
        /// This function allows the \c TimeInterval object to be formatted as a string using
        /// the \c absl::Format function. Formats the interval as "[start, end)".
        ///
        /// @param sink The sink to which the formatted string will be written.
        /// @param interval The \c TimeInterval object to format.
        template <typename Sink>
        friend void AbslStringify(Sink& sink, const TimeInterval& interval) noexcept
        {
            absl::Format(&sink, "[%v, %v)", interval.start_time_inclusive_, interval.end_time_exclusive_);
        }

    private:
        TimeType start_time_inclusive_;
        TimeType end_time_exclusive_;
    };
}

#endif
