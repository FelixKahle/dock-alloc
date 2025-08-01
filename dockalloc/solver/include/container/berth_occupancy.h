// Copyright (c) 2025 Felix Kahle.
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to
// the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
// LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
// WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#ifndef DOCK_ALLOC_SOLVER_CONTAINER_BERTH_OCCUPANCY_H_
#define DOCK_ALLOC_SOLVER_CONTAINER_BERTH_OCCUPANCY_H_

#include <concepts>
#include "absl/container/btree_map.h"
#include "dockalloc/core/miscellaneous/core_types.h"
#include "dockalloc/solver/container/bit_vector.h"

namespace dockalloc::solver
{
    /// @brief Manages the occupancy of a berth over time, divided into discrete segments.
    ///
    /// This class provides an efficient way to represent and query a 2D space-time grid
    /// (quay segments vs. time). It uses a sparse representation where the state of all
    /// segments (stored in a \c BitVector) is only recorded at time points where the state
    /// changes. This makes it highly memory and computationally efficient for scenarios
    /// where the occupancy state is constant for long periods.
    ///
    /// @tparam TimeType The unsigned integral type for time points.
    /// @tparam PositionType The unsigned integral type for segment positions.
    /// @tparam WordType The underlying unsigned integral type used by the \c BitVector.
    template <typename TimeType, typename PositionType, typename WordType>
        requires std::unsigned_integral<TimeType> && std::unsigned_integral<PositionType> && std::unsigned_integral<
            WordType>
    class BerthOccupancy
    {
    public:
        /// @brief Constructs a new Berth Occupancy instance.
        ///
        /// @note The berth is initialized as entirely free for all segments at all times.
        ///
        /// @param num_segments The total number of discrete segments the berth is divided into.
        explicit DOCK_ALLOC_FORCE_INLINE BerthOccupancy(const size_t num_segments)
            : number_quay_segments_(num_segments)
        {
            timeline_.emplace(TimeType{0}, BitVector<WordType>(number_quay_segments_, true));
        }

        /// @brief Gets the total number of quay segments this container manages.
        ///
        /// @return The total number of configured segments.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t GetQuaySegmentCount() const noexcept
        {
            return number_quay_segments_;
        }

        /// @brief Gets the number of time events (distinct time points) recorded in the timeline.
        ///
        /// This function returns the count of unique time points at which the occupancy state changes.
        ///
        /// @return The number of distinct time events in the timeline.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t GetTimeEventCount() const noexcept
        {
            return timeline_.size();
        }

        /// @brief Marks a given range of segments as occupied for a specific time interval.
        ///
        /// This operation modifies the timeline to reflect that the specified segments are
        /// unavailable during the given time interval.
        ///
        /// @param time_interval The time interval [start, end) during which the segments are occupied.
        /// @param segment_range The range of segments [start, end) to mark as occupied.
        void Occupy(const core::TimeInterval<TimeType>& time_interval,
                    const core::SegmentRange<PositionType>& segment_range) noexcept
        {
            if (time_interval.IsEmpty() || segment_range.IsEmpty())
            {
                return;
            }

            SplitAt(time_interval.GetStart());
            SplitAt(time_interval.GetEnd());

            const size_t end_segment = std::min(static_cast<size_t>(segment_range.GetEnd()), number_quay_segments_);
            const size_t start_segment = std::min(static_cast<size_t>(segment_range.GetStart()), end_segment);

            for (auto it = timeline_.lower_bound(time_interval.GetStart());
                 it != timeline_.end() && it->first < time_interval.GetEnd(); ++it)
            {
                it->second.ClearBits(start_segment, end_segment);
            }

            CoalesceAt(time_interval.GetStart());
            CoalesceAt(time_interval.GetEnd());
        }

        /// @brief Marks a given range of segments as free for a specific time interval.
        ///
        /// This operation modifies the timeline to reflect that the specified segments are
        /// available during the given time interval.
        ///
        /// @param time_interval The time interval [start, end) during which the segments are freed.
        /// @param segment_range The range of segments [start, end) to mark as free.
        void Free(const core::TimeInterval<TimeType>& time_interval,
                  const core::SegmentRange<PositionType>& segment_range) noexcept
        {
            if (time_interval.IsEmpty() || segment_range.IsEmpty())
            {
                return;
            }

            SplitAt(time_interval.GetStart());
            SplitAt(time_interval.GetEnd());

            const size_t end_segment = std::min(static_cast<size_t>(segment_range.GetEnd()), number_quay_segments_);
            const size_t start_segment = std::min(static_cast<size_t>(segment_range.GetStart()), end_segment);

            for (auto it = timeline_.lower_bound(time_interval.GetStart());
                 it != timeline_.end() && it->first < time_interval.GetEnd(); ++it)
            {
                it->second.SetBits(start_segment, end_segment);
            }

            CoalesceAt(time_interval.GetStart());
            CoalesceAt(time_interval.GetEnd());
        }

        /// @brief Checks if a given range of segments is entirely free for the entire duration of a time interval.
        ///
        /// @note An empty time interval or segment range is considered trivially free.
        ///
        /// @param time_interval The time interval [start, end) to check.
        /// @param segment_range The range of segments [start, end) to check.
        ///
        /// @return \c true if all specified segments are free for the entire time interval, \c false otherwise.
        [[nodiscard]] bool IsFree(const core::TimeInterval<TimeType>& time_interval,
                                  const core::SegmentRange<PositionType>& segment_range) const noexcept
        {
            if (time_interval.IsEmpty() || segment_range.IsEmpty())
            {
                return true;
            }

            const size_t end_segment = std::min(static_cast<size_t>(segment_range.GetEnd()), number_quay_segments_);
            const size_t start_segment = std::min(static_cast<size_t>(segment_range.GetStart()), end_segment);

            if (start_segment >= end_segment)
            {
                return true;
            }

            auto it = timeline_.upper_bound(time_interval.GetStart());
            if (it != timeline_.begin()) --it;

            for (; it != timeline_.end() && it->first < time_interval.GetEnd(); ++it)
            {
                if (!it->second.AreBitsSet(start_segment, end_segment))
                {
                    return false;
                }
            }
            return true;
        }

        /// @brief Checks if any part of a given segment range is occupied at any point within a time interval.
        ///
        /// @param time_interval The time interval [start, end) to check.
        /// @param segment_range The range of segments [start, end) to check.
        ///
        /// @return \c true if any specified segment is occupied at any point during the time interval, \c false otherwise.
        [[nodiscard]] bool IsOccupied(const core::TimeInterval<TimeType>& time_interval,
                                      const core::SegmentRange<PositionType>& segment_range) const noexcept
        {
            return !IsFree(time_interval, segment_range);
        }

    private:
        /// @brief Ensures a specific time point exists as a key in the timeline.
        ///
        /// If the time point \c time_point does not exist as a key, it is created by copying the
        /// state from the immediately preceding interval. This prepares the timeline for
        /// a state change beginning at \c time_point without affecting prior states.
        ///
        /// @param time_point The time point to split at.
        void DOCK_ALLOC_FORCE_INLINE SplitAt(const TimeType time_point) noexcept
        {
            auto it = timeline_.upper_bound(time_point);
            if (it == timeline_.begin())
            {
                return;
            }
            --it;
            if (it->first == time_point)
            {
                return;
            }
            timeline_.emplace(time_point, it->second);
        }

        /// @brief Merges redundant timeline entries around a specific time point.
        ///
        /// After a state modification, this function checks if the state at \c time_point is now
        /// identical to its preceding or succeeding states. If so, it removes the
        /// redundant entry to keep the timeline representation minimal.
        ///
        /// @param time_point The time point to coalesce around.
        void DOCK_ALLOC_FORCE_INLINE CoalesceAt(const TimeType time_point) noexcept
        {
            auto it = timeline_.find(time_point);
            if (it == timeline_.end())
            {
                return;
            }

            if (auto nxt = std::next(it); nxt != timeline_.end() && nxt->second == it->second)
            {
                timeline_.erase(nxt);
            }
            if (it != timeline_.begin())
            {
                if (auto prv = std::prev(it); prv->second == it->second)
                {
                    timeline_.erase(it);
                }
            }
        }

        size_t number_quay_segments_;
        absl::btree_map<TimeType, BitVector<WordType>> timeline_;
    };
}

#endif
