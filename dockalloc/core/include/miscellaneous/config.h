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
