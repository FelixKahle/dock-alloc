// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_INCLUDE_BERTH_SCHEDULE_H_
#define DOCK_ALLOC_SOLVER_INCLUDE_BERTH_SCHEDULE_H_

#include <type_traits>
#include "dockalloc/solver/time_interval.h"

namespace dockalloc::solver
{
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
    class BerthSchedule
    {
    public:
        /// @brief Virtual destructor.
        ///
        /// Ensures derived classes are properly cleaned up when deleted via a base pointer.
        virtual ~BerthSchedule() = default;

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
    };
}

#endif
