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

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_COMPILER_CHECK_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_COMPILER_CHECK_H_

// This file checks if the compiler supports the necessary features for dock-alloc
// to compile successfully.
// In general, a C++20 compliant compiler is required, as dock-alloc uses
// concepts and `constexpr` features extensively.

#include "dockalloc/core/miscellaneous/platform.h"

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

// Exceptions are shit. Really!
// dock‑alloc disables C++ exceptions to maintain maximum performance and minimal code size.
// Enabling exceptions incurs additional compiler overhead (unwind tables, hidden branches),
// increases binary size and complexity, and can inhibit optimizations such as inlining
// and effective branch prediction. I do not allow compiling dock-alloc with exceptions enabled,
// to never allow these bad practices.
#if DOCK_ALLOC_EXCEPTIONS_ENABLED
#error "dock-alloc does not support exceptions. Please disable exceptions in your compiler settings."
#endif

#endif
