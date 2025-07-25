// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_COMPILER_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_COMPILER_H_

#ifdef __cplusplus
#define DOCK_ALLOC_COMPILER_IS_CXX 1
#else
#define DOCK_ALLOC_COMPILER_IS_CXX 0
#endif

#ifdef __cpp_constexpr
#define DOCK_ALLOC_COMPILER_SUPPORTS_CONSTEXPR 1
#else
#define DOCK_ALLOC_COMPILER_SUPPORTS_CONSTEXPR 0
#endif

#ifdef __cpp_guaranteed_copy_elision
#define DOCK_ALLOC_COMPILER_SUPPORTS_GUARANTEED_COPY_ELISION 1
#else
#define DOCK_ALLOC_COMPILER_SUPPORTS_GUARANTEED_COPY_ELISION 0
#endif

#endif
