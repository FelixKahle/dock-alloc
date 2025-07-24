// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_TYPE_TRAITS_MAX_ALIGN_H_
#define DOCK_ALLOC_CORE_TYPE_TRAITS_MAX_ALIGN_H_

#include <algorithm>

namespace dockalloc::core
{
    /// @brief Computes the maximum alignment of multiple types.
    ///
    /// @tparam T The first type to consider.
    /// @tparam Ts Additional types to consider.
    template <typename T, typename... Ts>
    struct MaxAlign
    {
        enum
        {
            /// @brief The maximum alignment of the types.
            Value = std::max({(alignof(T)), (alignof(Ts))...})
        };
    };

    /// @brief Computes the maximum alignment of multiple types.
    ///
    /// This is a shortcut for using the \c MaxAlign struct.
    ///
    /// @tparam T The first type to consider.
    /// @tparam Ts Additional types to consider.
    template <typename T, typename... Ts>
    inline constexpr size_t MaxAlign_v = MaxAlign<T, Ts...>::Value;
}

#endif
