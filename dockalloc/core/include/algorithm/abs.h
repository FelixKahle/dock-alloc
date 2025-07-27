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

#ifndef DOCK_ALLOC_CORE_ALGORITHM_ABS_H_
#define DOCK_ALLOC_CORE_ALGORITHM_ABS_H_

#include <type_traits>
#include <cmath>
#include "dockalloc/core/miscellaneous/core_defines.h"

namespace dockalloc::core
{
    /// @brief Computes the absolute value of an arithmetic type.
    ///
    /// This function returns the absolute value of the given arithmetic type.
    ///
    /// @tparam T The type of the value to compute the absolute value for.
    /// @param x The value for which to compute the absolute value.
    ///
    /// @note The introduction of this function is to provide a consistent way to compute absolute values
    /// for all arithmetic types, including both signed and unsigned integers, as well as floating-point types.
    /// The standard library provides `std::abs` for integers and `std::fabs` for floating-point types,
    /// but this function unifies the behavior across all arithmetic types.
    ///
    /// @return The absolute value of the input.
    template <typename T>
        requires std::is_arithmetic_v<T>
    [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE T Abs(const T x) noexcept
    {
        if constexpr (std::is_unsigned_v<T>)
        {
            // Unsigned types are always non-negative, so we can return them directly.
            return x;
        }
        else if constexpr (std::is_floating_point_v<T>)
        {
            // Use std::fabs for floating-point types.
            return std::fabs(x);
        }
        else
        {
            // For signed integral types, we check if the value is negative,
            // and if so, return its negation.
            return x < T{0} ? -x : x;
        }
    }
}

#endif
