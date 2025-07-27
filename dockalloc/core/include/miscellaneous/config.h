// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_CONFIG_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_CONFIG_H_

// This file is intended to include defines for configuration options.

/// @brief Whether to allow the use of \c DOCK_ALLOC_FORCE_INLINE.
///
/// If this is set to \c 0, the \c DOCK_ALLOC_FORCE_INLINE macro will be defined as \c inline only.
/// While force inlining might improve performance in some cases, it can also lead to code bloat and longer compile
/// times as well as larger binary sizes. Sometimes it is better to let the compiler decide whether to inline a function
/// or not. \c inline functions are still inlined by the compiler if it deems it appropriate, even if this is
/// set to \c 0.
#define DOCK_ALLOC_ALLOW_FORCE_INLINE 1

#endif
