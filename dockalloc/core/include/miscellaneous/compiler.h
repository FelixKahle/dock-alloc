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
