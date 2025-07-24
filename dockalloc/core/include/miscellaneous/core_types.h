// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_CORE_TYPES_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_CORE_TYPES_H_

#include <concepts>
#include "dockalloc/core/container/interval.h"

namespace dockalloc::core
{
    /// @brief A type alias for a time interval.
    ///
    /// This type alias represents a time interval, which is a range of time defined by a start and end time.
    ///
    /// @tparam TimeType The unsigned integral type used for the start and end times of the interval.
    template <typename TimeType>
        requires std::unsigned_integral<TimeType>
    using TimeInterval = Interval<TimeType>;
}

#endif
