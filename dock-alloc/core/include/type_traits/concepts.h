// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_TYPE_TRAITS_CONCEPTS_H_
#define DOCK_ALLOC_CORE_TYPE_TRAITS_CONCEPTS_H_

#include <type_traits>

namespace dockalloc::core
{
    template <typename T>
    concept IsArithmetic = std::is_arithmetic_v<T>;
}

#endif
