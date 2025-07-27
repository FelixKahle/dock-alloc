// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_COMPILER_CHECK_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_COMPILER_CHECK_H_

// This file checks if the compiler supports the necessary features for dock-alloc
// to compile successfully.
// In general, a C++20 compliant compiler is required, as dock-alloc uses
// concepts and `constexpr` features extensively.

#include "dockalloc/core/miscellaneous/compiler.h"

#if !DOCK_ALLOC_COMPILER_IS_CXX
#error "dock-alloc requires a C++ compiler."
#endif

#if !DOCK_ALLOC_COMPILER_SUPPORTS_CONSTEXPR
#error "dock-alloc requires compiler support for 'constexpr'."
#endif

#if !DOCK_ALLOC_COMPILER_SUPPORTS_CONCEPTS
#error "dock-alloc requires compiler support for concepts."
#endif

#if !DOCK_ALLOC_COMPILER_IS_CPP20
#error "dock-alloc requires a C++20 compliant compiler."
#endif

#if DOCK_ALLOC_EXCEPTIONS_ENABLED
#error "dock-alloc does not support exceptions. Please disable exceptions in your compiler settings."
#endif

#endif
