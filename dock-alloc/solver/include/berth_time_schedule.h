// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_INCLUDE_BERTH_SCHEDULE_H_
#define DOCK_ALLOC_SOLVER_INCLUDE_BERTH_SCHEDULE_H_

#include <type_traits>
#include "dockalloc/solver/time_interval.h"

namespace dockalloc::solver
{
    /// @brief Describes a contiguous free window in a berth’s time schedule.
    ///
    /// A gap begins at \c start and extends up to \c end (inclusive).
    /// If \c end is \c std::nullopt, the window is unbounded (i.e., extends to infinity).
    ///
    /// @tparam TimeType An arithmetic type for time values (e.g., \c int, \c float, \c double).
    ///
    /// @author Felix Kahle (felix.kahle21@gmail.com)
    template <typename TimeType>
        requires std::is_arithmetic_v<TimeType>
    class BerthTimeScheduleGap
    {
    public:
        /// @brief Copy constructor.
        ///
        /// Initializes a new instance as a copy of the provided instance.
        ///
        /// @param other The instance to copy.
        BerthTimeScheduleGap(const BerthTimeScheduleGap<TimeType>& other) noexcept = default;

        /// @brief Move constructor.
        ///
        /// Initializes a new instance by transferring ownership from the provided instance.
        ///
        /// @param other The instance to move from.
        BerthTimeScheduleGap(BerthTimeScheduleGap<TimeType>&& other) noexcept = default;

        /// @brief Constructor.
        ///
        /// Initializes a new instance with the specified start and end times.
        /// If \c end is less than \c start, the constructor will swap them.
        ///
        /// @param start The start time of the gap.
        /// @param end The end time of the gap (optional).
        explicit BerthTimeScheduleGap(TimeType start, std::optional<TimeType> end) noexcept
            : start_((end && *end < start) ? *end : start),
              end_((end && *end < start) ? std::optional<TimeType>(start) : end)
        {
        }

        /// @brief Getter for the start time.
        ///
        /// Returns the start time of the gap.
        ///
        /// @return The start time.
        [[nodiscard]] TimeType GetStart() const noexcept
        {
            return start_;
        }

        /// @brief Getter for the end time.
        ///
        /// Returns the end time of the gap.
        ///
        /// @return The end time, or \c std::nullopt if the gap is unbounded.
        [[nodiscard]] std::optional<TimeType> GetEnd() const noexcept
        {
            return end_;
        }

        /// @brief Compares two instances for equality.
        ///
        /// This operator checks if two instances have the same start and end times.
        ///
        /// @tparam OtherTimeType The type of the other instance.
        ///
        /// @param lhs The left-hand side instance.
        /// @param rhs The right-hand side instance.
        ///
        /// @return \c true if the instances are equal; \c false otherwise.
        template <typename OtherTimeType>
            requires std::is_arithmetic_v<OtherTimeType>
        friend bool operator==(const BerthTimeScheduleGap& lhs, const BerthTimeScheduleGap<OtherTimeType>& rhs) noexcept
        {
            return lhs.start_ == rhs.start_ && lhs.end_ == rhs.end_;
        }

        /// @brief Compares two instances for inequality.
        ///
        /// This operator checks if two instances have different start or end times.
        ///
        /// @tparam OtherTimeType The type of the other instance.
        ///
        /// @param lhs The left-hand side instance.
        /// @param rhs The right-hand side instance.
        ///
        /// @return \c true if the instances are not equal; \c false otherwise.
        template <typename OtherTimeType>
            requires std::is_arithmetic_v<OtherTimeType>
        friend bool operator!=(const BerthTimeScheduleGap& lhs, const BerthTimeScheduleGap<OtherTimeType>& rhs) noexcept
        {
            return !(lhs == rhs);
        }

        // Delete copy and move assignment operators to prevent assignment.
        // The class is designed to be immutable after construction.

        BerthTimeScheduleGap& operator=(const BerthTimeScheduleGap<TimeType>& other) noexcept = delete;
        BerthTimeScheduleGap& operator=(BerthTimeScheduleGap<TimeType>&& other) noexcept = delete;

    private:
        TimeType start_;
        std::optional<TimeType> end_;
    };

    /// @brief Abstract interface for managing time-based berth occupation.
    ///
    /// This class defines the minimal interface required to manage berth availability
    /// in models involving time-based scheduling. Specific policies (e.g., exclusive,
    /// shared, continuous-time) should be implemented by concrete subclasses.
    ///
    /// @note: The exact scheduling semantics are defined by the implementing subclass.
    ///
    /// @tparam TimeType A scalar arithmetic type representing time values (e.g., \c int, \c float, \c double).
    ///
    /// @author Felix Kahle (felix.kahle21@gmail.com)
    template <typename TimeType>
        requires std::is_arithmetic_v<TimeType>
    class BerthTimeSchedule
    {
    public:
        /// @brief Type alias for a function that selects a gap from the schedule.
        typedef std::function<TimeType(BerthTimeScheduleGap<TimeType>)> GapChooser;

        /// @brief Virtual destructor.
        ///
        /// Ensures derived classes are properly cleaned up when deleted via a base pointer.
        virtual ~BerthTimeSchedule() = default;

        /// @brief Checks whether a given time interval can be scheduled.
        ///
        /// @param interval The time interval to query.
        ///
        /// @return \c true if the interval can be allocated; \c false otherwise.
        virtual bool IsFree(const TimeInterval<TimeType>& interval) const noexcept = 0;

        /// @brief Attempts to allocate the specified time interval.
        ///
        /// @param interval The interval to allocate.
        ///
        /// @return \c true if the interval was accepted into the schedule; \c false otherwise.
        virtual bool Occupy(const TimeInterval<TimeType>& interval) noexcept = 0;

        /// @brief Releases a previously allocated time interval.
        ///
        /// @param interval The time interval to release.
        virtual void Free(const TimeInterval<TimeType>& interval) noexcept = 0;

        /// @brief Clears all scheduled intervals.
        ///
        /// This method removes all intervals from the schedule, effectively resetting it.
        virtual void Clear() noexcept = 0;

        virtual BerthTimeScheduleGap<TimeType> FindGap(TimeType earliest_start, TimeType length) const noexcept = 0;
    };
}

#endif
