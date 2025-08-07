// Copyright (c) 2025 Felix Kahle.
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to
// the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
// LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
// WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_INLINE_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_INLINE_H_

#include "dockalloc/core/miscellaneous/config.h"

#ifndef DOCK_ALLOC_ALLOW_FORCE_INLINE
#define DOCK_ALLOC_ALLOW_FORCE_INLINE 0
#endif

#if DOCK_ALLOC_ALLOW_FORCE_INLINE
#if defined(_MSC_VER) || defined(__INTEL_COMPILER) || defined(__INTEL_LLVM_COMPILER)
#define DOCK_ALLOC_FORCE_INLINE __forceinline
#elif defined(__GNUC__) || defined(__clang__) || defined(__IBMCPP__) || defined(__SUNPRO_CC)
#define DOCK_ALLOC_FORCE_INLINE inline __attribute__((always_inline))
#else
#define DOCK_ALLOC_FORCE_INLINE inline
#endif
#else
#define DOCK_ALLOC_FORCE_INLINE inline
#endif

#endif
