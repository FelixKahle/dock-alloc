// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_COMPILER_CHECK_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_COMPILER_CHECK_H_

#include "dockalloc/core/miscellaneous/compiler.h"

#if !DOCK_ALLOC_COMPILER_SUPPORTS_CONSTEXPR
#error "dock-alloc requires compiler support for 'constexpr'."
#endif

#endif
