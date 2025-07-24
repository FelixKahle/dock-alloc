// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_INLINE_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_INLINE_H_

#if defined(_MSC_VER) || defined(__INTEL_COMPILER) || defined(__INTEL_LLVM_COMPILER)
#define DOCK_ALLOC_FORCE_INLINE __forceinline
#elif defined(__GNUC__) || defined(__clang__) || defined(__IBMCPP__) || defined(__SUNPRO_CC)
#define DOCK_ALLOC_FORCE_INLINE inline __attribute__((always_inline))
#else
#define DOCK_ALLOC_FORCE_INLINE inline
#endif

#endif
