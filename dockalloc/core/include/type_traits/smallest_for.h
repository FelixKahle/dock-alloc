// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_TYPE_TRAITS_SMALLEST_UNSIGNED_FOR_H_
#define DOCK_ALLOC_CORE_TYPE_TRAITS_SMALLEST_UNSIGNED_FOR_H_

#include <type_traits>
#include <cstdint>
#include <limits>

namespace dockalloc::core
{
    /// @brief A type trait to determine the smallest signed integral type that can hold a given value N.
    ///
    /// This trait provides a type alias \c Type that resolves to the smallest signed integral type
    /// that can represent the value N. It checks against the limits of common unsigned types
    /// (int8_t, int16_t, int32_t, int64_t) and falls back to \c int64_t if N exceeds the limits of these types.
    ///
    /// @tparam N The value for which to determine the smallest unsigned type.
    // @formatter:off
    template <int64_t N>
    struct SmallestSignedFor
    {
        using Type = std::conditional_t<N >= std::numeric_limits<int8_t>::min() && N <= std::numeric_limits<int8_t>::max(), int8_t,
                        std::conditional_t<N >= std::numeric_limits<int16_t>::min() && N <= std::numeric_limits<int16_t>::max(), int16_t,
                            std::conditional_t<N >= std::numeric_limits<int32_t>::min() && N <= std::numeric_limits<int32_t>::max(), int32_t, int64_t>>>;
    };
    // @formatter:on

    /// @brief A convenience alias for the smallest signed type for a given value N.
    ///
    /// This alias resolves to the type determined by \c SmallestSignedFor<N>::Type.
    ///
    /// @tparam N The value for which to determine the smallest signed type.
    template <int64_t N>
    using SmallestSignedFor_t = typename SmallestSignedFor<N>::Type;

    /// @brief A type trait to determine the smallest unsigned integral type that can hold a given value N.
    ///
    /// This trait provides a type alias \c Type that resolves to the smallest unsigned integral type
    /// that can represent the value N. It checks against the limits of common unsigned types
    /// (uint8_t, uint16_t, uint32_t, uint64_t) and falls back to \c size_t if N exceeds the limits of these types.
    ///
    /// @tparam N The value for which to determine the smallest unsigned type.
    template <std::size_t N>
    struct SmallestUnsignedFor
    {
        // @formatter:off
        /// @brief The smallest unsigned type that can hold the value N.
        ///
        /// This type is determined based on the value of N, checking against the limits of
        /// common unsigned types (uint8_t, uint16_t, uint32_t, uint64_t)
        /// and falling back to size_t if N exceeds these limits.
        using Type = std::conditional_t<N <= std::numeric_limits<uint8_t>::max(), uint8_t,
                        std::conditional_t<N <= std::numeric_limits<uint16_t>::max(), uint16_t,
                            std::conditional_t<N <= std::numeric_limits<uint32_t>::max(), uint32_t, uint64_t>>>;
        // @formatter:on
    };

    /// @brief A convenience alias for the smallest unsigned type for a given value N.
    ///
    /// This alias resolves to the type determined by \c SmallestUnsignedFor<N>::Type.
    ///
    /// @tparam N The value for which to determine the smallest unsigned type.
    template <std::size_t N>
    using SmallestUnsignedFor_t = typename SmallestUnsignedFor<N>::Type;
}

#endif
