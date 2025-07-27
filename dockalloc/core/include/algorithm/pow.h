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

#ifndef DOCK_ALLOC_CORE_POW_H_
#define DOCK_ALLOC_CORE_POW_H_

#include <type_traits>
#include <concepts>
#include <limits>
#include "dockalloc/core/include/miscellaneous/core_defines.h"

namespace dockalloc::core
{
    /// @brief Computes the next power of two greater than or equal to the given value.
    ///
    /// This function calculates the smallest power of two that is greater than or equal to the specified value.
    ///
    /// @tparam T The type of the value. Must be an integral type.
    /// @tparam Output The type of the output value. Defaults to the unsigned version of \p T.
    /// @param value The value for which to compute the next power of two.
    ///
    /// @return The next power of two greater than or equal to the specified value.
    template <typename T, typename Output = std::make_unsigned_t<T>>
        requires std::integral<T> &&
        std::unsigned_integral<Output> &&
        (std::numeric_limits<Output>::digits >= std::numeric_limits<T>::digits)
    constexpr DOCK_ALLOC_FORCE_INLINE Output NextPowerOfTwo(const T value) noexcept
    {
        // Special case for zero and one, that both evaluate to 1.
        if (value <= 1)
        {
            return 1;
        }

        // Work in the unsigned domain.
        Output x = static_cast<Output>(value) - 1;

        // Determine the number of bits in the type Output.
        constexpr size_t bits = std::numeric_limits<Output>::digits;

        // “Smear” the topmost set bit down through all lower bits.
        // After this loop, x will look like 0b0…0111…111
        // (all 1’s from bit 0 up to the highest original bit).
        for (size_t shift = 1; shift < bits; shift <<= 1)
        {
            x |= (x >> shift);
        }

        // Finally, add 1 to get exactly a single 1 in the next higher bit position.
        // This is the next power of two ≥ original `value`.
        return x + 1;
    }

    /// @brief Checks if the given value is a power of two.
    ///
    /// This function checks whether the specified value is a power of two.
    ///
    /// @tparam T The type of the value. Must be an integral type.
    /// @param value The value to check.
    ///
    /// @return True if the value is a power of two, false otherwise.
    template <typename T>
        requires std::integral<T>
    [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE bool IsPowerOfTwo(const T value) noexcept
    {
        return value > 0 && (value & (value - 1)) == 0;
    }
}

#endif
