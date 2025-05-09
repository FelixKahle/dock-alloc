// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_SOLVER_DISJOINT_BERTH_SCHEDULE_H_
#define DOCK_ALLOC_SOLVER_DISJOINT_BERTH_SCHEDULE_H_

#include <type_traits>

#include "berth_time_schedule.h"
#include "absl/container/btree_set.h"
#include "dockalloc/solver/berth_time_schedule.h"
#include "dockalloc/solver/time_interval.h"

namespace dockalloc::solver
{
    /// @brief Comparator that defines a strict order based on non-overlapping intervals.
    ///
    /// Returns `true` if the left interval ends strictly before the right interval starts.
    /// In all other cases—including overlapping or touching intervals—returns `false`.
    ///
    /// @tparam LhsTimeType A scalar arithmetic type representing time values (e.g., \c int, \c float, \c double).
    /// @tparam RhsTimeType A scalar arithmetic type representing time values (e.g., \c int, \c float, \c double).
    ///
    /// @author Felix Kahle (felix.kahle21@gmail.com)
    template <typename LhsTimeType, typename RhsTimeType = LhsTimeType>
        requires std::is_arithmetic_v<LhsTimeType> && std::is_arithmetic_v<RhsTimeType>
    struct IsNonOverlappingLessComparator
    {
        [[nodiscard]] constexpr bool operator()(const TimeInterval<LhsTimeType>& lhs,
                                                const TimeInterval<RhsTimeType>& rhs) const noexcept
        {
            return lhs.GetEnd() < rhs.GetStart();
        }
    };

    /// @brief A schedule model that enforces non-overlapping, exclusive berth assignments.
    ///
    /// The \c DisjointBerthTimeSchedule represents a berth schedule where no two time intervals
    /// are allowed to overlap or touch. It guarantees exclusivity by storing time intervals
    /// in a sorted container (\c absl::btree_set) using a comparator that enforces strict
    /// non-overlapping semantics.
    ///
    /// Key characteristics:
    /// - Only one ship can occupy the berth at any point in time.
    /// - Insertion of overlapping or adjacent intervals is rejected.
    /// - Interval lookup and insertion are performed in logarithmic time.
    ///
    /// This class is ideal for modeling berth allocation in scenarios where complete
    /// exclusivity is required (i.e., no time-sharing or splitting is allowed).
    ///
    /// @tparam TimeType A scalar arithmetic type representing time values (e.g., \c int, \c float, \c double).
    ///
    /// @see BerthSchedule for the base interface.
    /// @see IsNonOverlappingLessComparator for the interval ordering logic.
    ///
    /// @author Felix Kahle (felix.kahle21@gmail.com)
    template <typename TimeType>
        requires std::is_arithmetic_v<TimeType>
    class DisjointBerthTimeSchedule final : public BerthTimeSchedule<TimeType>
    {
    public:
        explicit DisjointBerthTimeSchedule() noexcept = default;

        /// @brief Copy constructor.
        ///
        /// This constructor creates a new instance of the \c DisjointBerthTimeSchedule class
        /// by copying the contents of another instance.
        ///
        /// @param other The \c DisjointBerthTimeSchedule instance to copy from.
        DisjointBerthTimeSchedule(const DisjointBerthTimeSchedule& other) = default;

        /// @brief Move constructor.
        ///
        /// This constructor creates a new instance of the \c DisjointBerthTimeSchedule class
        /// by transferring ownership of the contents from another instance.
        ///
        /// @param other The \c DisjointBerthTimeSchedule instance to move from.
        DisjointBerthTimeSchedule(DisjointBerthTimeSchedule&& other) noexcept = default;

        /// @brief Checks whether a given time interval is entirely free (unoccupied).
        ///
        /// This method determines whether the specified interval does not overlap with
        /// any of the currently occupied intervals stored in the schedule.
        ///
        /// Internally, it performs a binary search to locate the first interval with a start time
        /// greater than the queried interval, then inspects adjacent intervals for any overlaps.
        ///
        /// @param interval The time interval to check for availability.
        ///
        /// @return \c true if the interval does not intersect with any occupied interval; \c false otherwise.
        [[nodiscard]] bool IsFree(const TimeInterval<TimeType>& interval) const noexcept override
        {
            return occupied_.find(interval) == occupied_.end();
        }

        /// @brief Tries to occupy a given time interval.
        ///
        /// This method attempts to add the specified interval to the schedule.
        /// If the interval overlaps with any already occupied intervals,
        /// it will not be added, and the method will return \c false.
        ///
        /// @param interval The time interval to occupy.
        ///
        /// @return \c true if the interval was successfully added; \c false if it overlaps with an existing interval.
        [[nodiscard]] bool Occupy(const TimeInterval<TimeType>& interval) noexcept override
        {
            auto [it, inserted] = occupied_.insert(interval);
            return inserted;
        }

        /// @brief Frees a previously occupied time interval.
        ///
        /// Removes the exact interval from the schedule if it exists. The operation is
        /// a no-op if no matching interval (with identical start and end times) is found.
        ///
        /// @param interval The time interval to free.
        void Free(const TimeInterval<TimeType>& interval) noexcept override
        {
            occupied_.erase(interval);
        }

        /// @brief Clears all occupied intervals from the schedule.
        ///
        /// This method removes all intervals from the schedule, effectively resetting it.
        void Clear() noexcept override
        {
            occupied_.clear();
        }

        [[nodiscard]] BerthTimeScheduleGap<TimeType>
        FindGap(TimeType earliest_start, TimeType length) const noexcept override
        {
            const TimeInterval<TimeType> probe{earliest_start, earliest_start};
            auto it = occupied_.lower_bound(probe);

            TimeType cursor = earliest_start;
            if (it != occupied_.end() && it->GetStart() <= cursor && cursor <= it->GetEnd())
            {
                cursor = it->GetEnd() + 1;
                it = std::next(it);
            }

            for (; it != occupied_.end(); ++it)
            {
                TimeType gap_start = cursor;
                TimeType next_occ_start = it->GetStart();

                if (next_occ_start - gap_start >= length)
                {
                    TimeType gap_end = next_occ_start - 1;
                    return BerthTimeScheduleGap<TimeType>(gap_start, gap_end);
                }
                cursor = std::max(cursor, it->GetEnd() + 1);
            }

            return BerthTimeScheduleGap<TimeType>(cursor, std::nullopt);
        }

    private:
        absl::btree_set<TimeInterval<TimeType>, IsNonOverlappingLessComparator<TimeType>> occupied_;
    };
}

#endif
