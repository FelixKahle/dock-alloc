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

    template <typename PositionType>
        requires std::unsigned_integral<PositionType>
    using SegmentRange = Interval<PositionType>;
}

#endif
