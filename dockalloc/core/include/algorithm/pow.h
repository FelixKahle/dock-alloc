// Copyright 2025 Felix Kahle. All rights reserved.

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
}

#endif
