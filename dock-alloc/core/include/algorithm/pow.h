// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_POW_H_
#define DOCK_ALLOC_CORE_POW_H_

#include <type_traits>
#include <concepts>
#include <limits>

namespace dockalloc::core
{
    /// @brief Computes the next power of two greater than or equal to the given value.
    ///
    /// This function calculates the smallest power of two that is greater than or equal to the specified value.
    ///
    /// @tparam T The type of the value. Must be an integral type.
    /// @param value The value for which to compute the next power of two.
    ///
    /// @return The next power of two greater than or equal to the specified value.
    template <typename T>
        requires std::integral<T>
    constexpr T NextPowerOfTwo(const T value) noexcept
    {
        if (value <= 1)
        {
            return 1;
        }

        using UnsignedType = std::make_unsigned_t<T>;
        UnsignedType x = static_cast<UnsignedType>(value) - 1;
        constexpr size_t bits = std::numeric_limits<T>::digits;

        for (size_t shift = 1; shift < bits; shift <<= 1)
        {
            x |= (x >> shift);
        }

        return static_cast<T>(x + 1);
    }
}

#endif
