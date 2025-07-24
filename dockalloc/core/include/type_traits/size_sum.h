// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_TYPE_TRAITS_SIZE_SUM_H_
#define DOCK_ALLOC_CORE_TYPE_TRAITS_SIZE_SUM_H_

namespace dockalloc::core
{
    /// @brief Computes the sum of the sizes of multiple types.
    ///
    /// @tparam Ts The types to compute the size sum for.
    template <typename... Ts>
    struct SizeSum
    {
        enum
        {
            /// @brief The sum of the sizes of the types.
            Value = (0 + ... + sizeof(Ts))
        };
    };

    /// @brief A helper variable template to compute the size sum of multiple types.
    ///
    /// @tparam Ts The types to compute the size sum for.
    template <typename... Ts>
    inline constexpr int SizeSum_v = SizeSum<Ts...>::Value;
}

#endif
