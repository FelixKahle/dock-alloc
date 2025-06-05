// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_TYPE_TRAITS_BIGGER_H_
#define DOCK_ALLOC_CORE_TYPE_TRAITS_BIGGER_H_
#include <type_traits>

namespace dockalloc::core
{
    template <typename A, typename B>
    struct Bigger
    {
        enum
        {
            Value = sizeof(A) > sizeof(B)
        };
    };

    template <typename A, typename B>
    inline constexpr bool Bigger_v = Bigger<A, B>::Value;
}

#endif
