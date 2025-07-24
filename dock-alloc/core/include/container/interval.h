// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_CONTAINER_INTERVAL_H_
#define DOCK_ALLOC_CORE_CONTAINER_INTERVAL_H_

#include <algorithm>
#include <type_traits>
#include "absl/strings/str_format.h"

namespace dockalloc::core
{
    /// @brief Represents a closed interval [start, end) for arithmetic types.
    ///
    /// This class is designed to handle intervals for arithmetic types such as integers and floating-point numbers.
    ///
    /// @tparam T The type of the interval's endpoints. Must be an arithmetic type.
    template <typename T>
        requires std::is_arithmetic_v<T>
    class Interval
    {
    public:
        /// @brief Type alias for the value type of the interval.
        ///
        /// This type alias is used to refer to the type of the interval's endpoints.
        using ValueType = T;

        /// @brief Constructs an interval with the given start and end values.
        ///
        /// This constructor initializes the interval with the specified start and end values.
        ///
        /// @note The constructor ensures that the start value is always less than or equal to the end value.
        ///
        /// @param start_inclusive The inclusive start of the interval.
        /// @param end_inclusive The inclusive end of the interval.
        constexpr Interval(const T start_inclusive, const T end_inclusive) noexcept
            : start_inclusive_(std::min<T>(start_inclusive, end_inclusive)),
              end_exclusive_(std::max<T>(start_inclusive, end_inclusive))
        {
        }

        /// @brief Gets the inclusive start of the interval.
        ///
        /// This method returns the inclusive start of the interval.
        ///
        /// @return The inclusive start of the interval.
        [[nodiscard]] constexpr T GetStart() const noexcept
        {
            return start_inclusive_;
        }

        /// @brief Gets the exclusive end of the interval.
        ///
        /// This method returns the exclusive end of the interval.
        ///
        /// @return The exclusive end of the interval.
        [[nodiscard]] constexpr T GetEnd() const noexcept
        {
            return end_exclusive_;
        }

        /// @brief Computes the midpoint of the interval.
        ///
        /// This method calculates the midpoint of the interval, which is the average of the start and end values.
        ///
        /// @tparam ReturnTimeType The type of the return value. Defaults to the type of the interval's endpoints.
        ///
        /// @return The midpoint of the interval as an arithmetic type.
        template <typename ReturnTimeType = T>
            requires std::is_arithmetic_v<ReturnTimeType>
        [[nodiscard]] constexpr ReturnTimeType Midpoint() const noexcept
        {
            // Floating point types cannot overflow, so we can safely use the average.
            // It will yield more accurate results than the alternative formula
            // midpoint = start + (end - start) / 2 used for integral types.
            if constexpr (std::is_floating_point_v<ReturnTimeType>)
            {
                return (static_cast<ReturnTimeType>(start_inclusive_) +
                    static_cast<ReturnTimeType>(end_exclusive_)) / ReturnTimeType{2};
            }

            // To guard against overflow, we use the following formula:
            // midpoint = start + (end - start) / 2
            return static_cast<ReturnTimeType>(start_inclusive_) +
                static_cast<ReturnTimeType>(end_exclusive_ - start_inclusive_) / ReturnTimeType{2};
        }

        /// @brief Checks if the interval is empty.
        ///
        /// This method checks if the interval has no length, which occurs when the start and end values are equal.
        ///
        /// @return \c true if the interval is empty, \c false otherwise.
        [[nodiscard]] constexpr bool IsEmpty() const noexcept
        {
            return start_inclusive_ == end_exclusive_;
        }

        /// @brief Gets the length of the interval.
        ///
        /// This method calculates the length of the interval, which is the difference between the end and start values.
        ///
        /// @return The length of the interval as an arithmetic type.
        [[nodiscard]] constexpr T Length() const noexcept
        {
            return end_exclusive_ - start_inclusive_;
        }

        /// @brief Checks if the interval contains the given value.
        ///
        /// This method checks if the specified value is within the interval, including the start but excluding the end.
        ///
        /// @tparam OtherType The type of the value to check. Must be convertible to the interval's type.
        /// @param value The value to check for containment in the interval.
        ///
        /// @return \c true if the value is within the interval, \c false otherwise.
        template <typename OtherType>
            requires std::convertible_to<OtherType, T>
        [[nodiscard]] constexpr bool Contains(OtherType value) const noexcept
        {
            return value >= start_inclusive_ && value < end_exclusive_;
        }

        /// @brief Checks if the interval contains another interval.
        ///
        /// This method checks if the current interval fully contains another interval,
        /// meaning the start of the other interval is greater than or equal to the start of this interval,
        /// and the end of the other interval is less than or equal to the end of this interval.
        ///
        /// @tparam OtherType The type of the other interval's endpoints. Must be an arithmetic type.
        /// @param other The other interval to check for containment.
        ///
        /// @return \c true if the current interval contains the other interval, \c false otherwise.
        template <typename OtherType>
            requires std::is_arithmetic_v<T>
        [[nodiscard]] constexpr bool ContainsInterval(const Interval<OtherType>& other) const noexcept
        {
            return other.start_inclusive_ >= start_inclusive_
                && other.end_exclusive_ <= end_exclusive_;
        }

        /// @brief Checks if the current interval intersects with another interval.
        ///
        /// This method checks if the current interval overlaps with another interval,
        /// meaning there is at least one point that is contained in both intervals.
        ///
        /// @tparam OtherType The type of the other interval's endpoints. Must be an arithmetic type.
        /// @param other The other interval to check for intersection.
        ///
        /// @return \c true if the intervals intersect, \c false otherwise.
        template <typename OtherType>
            requires std::is_arithmetic_v<T>
        [[nodiscard]] constexpr bool Intersects(const Interval<OtherType>& other) const noexcept
        {
            return std::max(start_inclusive_, static_cast<T>(other.GetStart())) <
                std::min(end_exclusive_, static_cast<T>(other.GetEnd()));
        }

        /// @brief Computes the intersection of the current interval with another interval.
        ///
        /// This method calculates the overlapping part of the current interval and another interval.
        /// If there is no intersection, it returns an empty optional.
        ///
        /// @tparam OtherType The type of the other interval's endpoints. Must be an arithmetic type.
        /// @tparam ReturnTimeType The type of the return value. Defaults to the type of the interval's endpoints.
        /// @param other The other interval to compute the intersection with.
        ///
        /// @return An optional containing the intersection interval if it exists,
        /// or an empty optional if there is no intersection.
        template <typename OtherType, typename ReturnTimeType = T>
            requires std::is_arithmetic_v<T>
        [[nodiscard]] constexpr std::optional<Interval<ReturnTimeType>> Intersection(
            const Interval<OtherType>& other) const noexcept
        {
            const ReturnTimeType start = std::max(static_cast<ReturnTimeType>(start_inclusive_),
                                                  static_cast<ReturnTimeType>(other.GetStart()));
            const ReturnTimeType end = std::min(static_cast<ReturnTimeType>(end_exclusive_),
                                                static_cast<ReturnTimeType>(other.GetEnd()));

            if (start >= end)
            {
                return std::nullopt;
            }

            return Interval<ReturnTimeType>(start, end);
        }

        /// @brief Clamps the current interval to fit within another interval.
        ///
        /// This method restricts the current interval to the boundaries defined by another interval.
        /// If the current interval does not overlap with the boundary interval, it returns an empty optional.
        ///
        /// @tparam OtherType The type of the boundary interval's endpoints. Must be an arithmetic type.
        ///
        /// @return An optional \c std::optional containing the clamped interval if it exists,
        template <typename OtherType>
            requires std::is_arithmetic_v<T>
        [[nodiscard]] constexpr std::optional<Interval<T>> Clamp(
            const Interval<OtherType>& boundary) const noexcept
        {
            const T clamped_start = std::max(start_inclusive_, static_cast<T>(boundary.GetStart()));
            const T clamped_end = std::min(end_exclusive_, static_cast<T>(boundary.GetEnd()));

            if (clamped_start >= clamped_end)
            {
                return std::nullopt;
            }

            return Interval(clamped_start, clamped_end);
        }

        /// @brief Compares two intervals for equality.
        ///
        /// This method checks if the start and end values of two intervals are equal.
        ///
        /// @tparam OtherType The type of the other interval's endpoints. Must be an arithmetic type.
        /// @param lhs The left-hand side interval to compare.
        /// @param rhs The other interval to compare with.
        ///
        /// @return \c true if the intervals are equal, \c false otherwise.
        template <typename OtherType>
            requires std::is_arithmetic_v<OtherType>
        friend constexpr bool operator==(const Interval& lhs, const Interval<OtherType>& rhs) noexcept
        {
            return lhs.GetStart() == rhs.GetStart() && lhs.GetEnd() == rhs.GetEnd();
        }

        /// @brief Compares two intervals for inequality.
        ///
        /// This method checks if two intervals are not equal by negating the result of the equality operator.
        ///
        /// @tparam OtherType The type of the other interval's endpoints. Must be an arithmetic type.
        /// @param lhs The left-hand side interval to compare.
        /// @param rhs The other interval to compare with.
        ///
        /// @return \c true if the intervals are not equal, \c false otherwise.
        template <typename OtherType>
            requires std::is_arithmetic_v<OtherType>
        friend constexpr bool operator!=(const Interval& lhs, const Interval<OtherType>& rhs) noexcept
        {
            return !(lhs == rhs);
        }

        /// @brief Absl hash function for the \c Interval class.
        ///
        /// This function computes a hash value for the interval by combining the hashes of its start and end values.
        ///
        /// @tparam H The hash type used by Absl.
        /// @param h The initial hash value.
        /// @param interval The interval for which to compute the hash.
        ///
        /// @return The combined hash value.
        template <typename H>
        friend constexpr H AbslHashValue(H h, const Interval& interval) noexcept
        {
            return H::combine(std::move(h), interval.GetStart(), interval.GetEnd());
        }

        /// @brief Formats the interval as a string using Absl's formatting.
        ///
        /// This function formats the interval in the form
        /// "[start, end)" where "start" is inclusive and "end" is exclusive.
        ///
        /// @tparam Sink The type of the sink used for formatting.
        /// @param sink The sink to which the formatted string will be written.
        /// @param interval The interval to format.
        template <typename Sink>
        friend void AbslStringify(Sink& sink, const Interval& interval) noexcept
        {
            absl::Format(&sink, "[%v, %v)", interval.GetStart(), interval.GetEnd());
        }

    private:
        T start_inclusive_;
        T end_exclusive_;
    };
}

#endif
