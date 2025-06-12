// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_ALGORITHM_ABS_H_
#define DOCK_ALLOC_CORE_ALGORITHM_ABS_H_

#include "dockalloc/core/type_traits/concepts.h"

namespace dockalloc::core
{
    /// @brief Computes the absolute value of an arithmetic type.
    ///
    /// This function returns the absolute value of the given arithmetic type.
    ///
    /// @tparam T The type of the value to compute the absolute value for.
    /// @param x The value for which to compute the absolute value.
    ///
    /// @return The absolute value of the input.
    template <typename T>
        requires core::IsArithmetic<T>
    [[nodiscard]] constexpr T Abs(const T x) noexcept
    {
        if constexpr (std::is_unsigned_v<T>)
        {
            return x;
        }
        else if constexpr (std::is_floating_point_v<T>)
        {
            return std::fabs(x);
        }
        else
        {
            return x < T{0} ? -x : x;
        }
    }
}

#endif
