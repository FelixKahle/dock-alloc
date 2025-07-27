// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_COMPILER_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_COMPILER_H_

// Compiler C++ version checks.

#ifdef __cplusplus
#define DOCK_ALLOC_COMPILER_IS_CXX 1

#if __cplusplus >= 202002L
#define DOCK_ALLOC_COMPILER_IS_CPP20 1
#else
#define DOCK_ALLOC_COMPILER_IS_CPP20 0
#endif

#if __cplusplus >= 202302L
#define DOCK_ALLOC_COMPILER_IS_CPP23 1
#else
#define DOCK_ALLOC_COMPILER_IS_CPP23 0
#endif

#else
#define DOCK_ALLOC_COMPILER_IS_CXX 0
#endif

// Compiler feature checks.

#ifdef __cpp_constexpr
#define DOCK_ALLOC_COMPILER_SUPPORTS_CONSTEXPR 1
#else
#define DOCK_ALLOC_COMPILER_SUPPORTS_CONSTEXPR 0
#endif

#ifdef __cpp_concepts
#define DOCK_ALLOC_COMPILER_SUPPORTS_CONCEPTS 1
#else
#define DOCK_ALLOC_COMPILER_SUPPORTS_CONCEPTS 0
#endif

#ifdef __cpp_guaranteed_copy_elision
#define DOCK_ALLOC_COMPILER_SUPPORTS_GUARANTEED_COPY_ELISION 1
#else
#define DOCK_ALLOC_COMPILER_SUPPORTS_GUARANTEED_COPY_ELISION 0
#endif

# if defined(__EXCEPTIONS)
#define DOCK_ALLOC_EXCEPTIONS_ENABLED 1
# elif defined(_CPPUNWIND)
#define DOCK_ALLOC_EXCEPTIONS_ENABLED 1
# else
#define DOCK_ALLOC_EXCEPTIONS_ENABLED 0
# endif


#endif
