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

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_PLATFORM_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_PLATFORM_H_

#if defined(__linux__)
#define DOCK_ALLOC_PLATFORM_LINUX 1
#if defined(__ANDROID__)
#define DOCK_ALLOC_PLATFORM_ANDROID 1
#endif
#elif defined(_WIN32)
#define DOCK_ALLOC_PLATFORM_WINDOWS 1
#if defined(WINAPI_FAMILY)
#include <winapifamily.h>
#if WINAPI_FAMILY_PARTITION(WINAPI_PARTITION_PHONE_APP)
#define DOCK_ALLOC_PLATFORM_WINDOWS_PHONE 1
#endif
#endif
#elif defined(__APPLE__)
#include <TargetConditionals.h>
#if TARGET_OS_IPHONE
#define DOCK_ALLOC_PLATFORM_IOS 1
#elif TARGET_OS_MAC
#define DOCK_ALLOC_PLATFORM_MAC 1
#endif
#elif defined(__EMSCRIPTEN__)
#define DOCK_ALLOC_PLATFORM_EMSCRIPTEN 1
#elif defined(__FreeBSD__)
#define DOCK_ALLOC_PLATFORM_FREEBSD 1
#else
#error "Unable to determine operating system"
#endif

// Detect compilers and CPU architectures
// Note: clang also defines __GNUC__ since it aims to be compatible with GCC.
// Therefore, we need to check for __clang__ or __llvm__ first.
#if defined(__clang__) || defined(__llvm__)
#define DOCK_ALLOC_PLATFORM_CLANG 1
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE 1
#if defined(__i386__) || defined(__x86_64__)
#define DOCK_ALLOC_PLATFORM_X86 1
#define DOCK_ALLOC_PLATFORM_CLANG_X86 1
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_X86 1
#elif defined(__arm__) || defined(__arm64__) || defined(__aarch64__)
#define DOCK_ALLOC_PLATFORM_ARM 1
#define DOCK_ALLOC_PLATFORM_CLANG_ARM 1
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_ARM 1
#elif defined(__mips__)
#define DOCK_ALLOC_PLATFORM_MIPS 1
#define DOCK_ALLOC_PLATFORM_CLANG_MIPS 1
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_MIPS 1
#elif defined(__asmjs__)
#define DOCK_ALLOC_PLATFORM_ASMJS 1
#define DOCK_ALLOC_PLATFORM_CLANG_ASMJS 1
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_ASMJS 1
#endif
#elif defined(__GNUC__)
#define DOCK_ALLOC_PLATFORM_GCC 1
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE 1
#if defined(__i386__) || defined(__x86_64__)
#define DOCK_ALLOC_PLATFORM_X86 1
#define DOCK_ALLOC_PLATFORM_GCC_X86 1
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_X86 1
#elif defined(__arm__) || defined(__arm64__) || defined(__aarch64__)
#define DOCK_ALLOC_PLATFORM_ARM 1
#define DOCK_ALLOC_PLATFORM_GCC_ARM 1
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_ARM 1
#elif defined(__mips__)
#define DOCK_ALLOC_PLATFORM_MIPS 1
#define DOCK_ALLOC_PLATFORM_GCC_MIPS 1
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_MIPS 1
#endif
#elif defined(_MSC_VER)
#define DOCK_ALLOC_PLATFORM_MSVC 1
#if defined(_M_IX86) || defined(_M_X64)
#define DOCK_ALLOC_PLATFORM_X86 1
#define DOCK_ALLOC_PLATFORM_MSVC_X86 1
#elif defined(_M_ARM) || defined(_M_ARMT)
#define DOCK_ALLOC_PLATFORM_ARM 1
#define DOCK_ALLOC_PLATFORM_MSVC_ARM 1
#endif
#else
#error "Unable to determine compiler"
#endif

// Define macros for supported CPU instruction sets
#if defined(DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE)
#if defined(__MMX__)
#define DOCK_ALLOC_PLATFORM_MMX 1
#endif
#if defined(__SSE__)
#define DOCK_ALLOC_PLATFORM_SSE 1
#endif
#if defined(__SSE2__)
#define DOCK_ALLOC_PLATFORM_SSE2 1
#endif
#if defined(__SSE3__)
#define DOCK_ALLOC_PLATFORM_SSE3 1
#endif
#if defined(__SSSE3__)
#define DOCK_ALLOC_PLATFORM_SSSE3 1
#endif
#if defined(__SSE4_1__)
#define DOCK_ALLOC_PLATFORM_SSE41 1
#endif
#if defined(__SSE4_2__)
#define DOCK_ALLOC_PLATFORM_SSE42 1
#endif
#if defined(__PCLMUL__)
#define DOCK_ALLOC_PLATFORM_PCLMUL 1
#endif
#if defined(__AVX__)
#define DOCK_ALLOC_PLATFORM_AVX 1
#endif
#if defined(__AVX2__)
#define DOCK_ALLOC_PLATFORM_AVX2 1
#endif
#if defined(__ARM_NEON__) || defined(__ARM_NEON)
#define DOCK_ALLOC_PLATFORM_NEON 1
#endif
// First, check the PLATFORM_WINDOWS_PHONE define, because
// the X86 instructions sets are not supported on the Windows Phone emulator
#elif defined(DOCK_ALLOC_PLATFORM_WINDOWS_PHONE)
#if defined(DOCK_ALLOC_PLATFORM_MSVC_ARM)
// NEON introduced in VS2012
#if (_MSC_VER >= 1700)
#define DOCK_ALLOC_PLATFORM_NEON 1
#endif
#endif
#elif defined(DOCK_ALLOC_PLATFORM_MSVC_X86)
// MMX, SSE and SSE2 introduced in VS2003
#if (_MSC_VER >= 1310)
#define DOCK_ALLOC_PLATFORM_MMX 1
#define DOCK_ALLOC_PLATFORM_SSE 1
#define DOCK_ALLOC_PLATFORM_SSE2 1
#endif
// SSE3 introduced in VS2005
#if (_MSC_VER >= 1400)
#define DOCK_ALLOC_PLATFORM_SSE3 1
#endif
// SSSE3, SSE4.1, SSE4.2, PCLMUL introduced in VS2008
#if (_MSC_VER >= 1500)
#define DOCK_ALLOC_PLATFORM_SSSE3 1
#define DOCK_ALLOC_PLATFORM_SSE41 1
#define DOCK_ALLOC_PLATFORM_SSE42 1
#define DOCK_ALLOC_PLATFORM_PCLMUL 1
#endif
// AVX and AVX2 introduced in VS2012
#if (_MSC_VER >= 1700)
#define DOCK_ALLOC_PLATFORM_AVX 1
#define DOCK_ALLOC_PLATFORM_AVX2 1
#endif
#endif

#ifndef DOCK_ALLOC_PLATFORM_LINUX
#define DOCK_ALLOC_PLATFORM_LINUX 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_ANDROID
#define DOCK_ALLOC_PLATFORM_ANDROID 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_WINDOWS
#define DOCK_ALLOC_PLATFORM_WINDOWS 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_WINDOWS_PHONE
#define DOCK_ALLOC_PLATFORM_WINDOWS_PHONE 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_IOS
#define DOCK_ALLOC_PLATFORM_IOS 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_MAC
#define DOCK_ALLOC_PLATFORM_MAC 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_EMSCRIPTEN
#define DOCK_ALLOC_PLATFORM_EMSCRIPTEN 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_FREEBSD
#define DOCK_ALLOC_PLATFORM_FREEBSD 0
#endif

#ifndef DOCK_ALLOC_PLATFORM_CLANG
#define DOCK_ALLOC_PLATFORM_CLANG 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_GCC
#define DOCK_ALLOC_PLATFORM_GCC 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_MSVC
#define DOCK_ALLOC_PLATFORM_MSVC 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_X86
#define DOCK_ALLOC_PLATFORM_X86 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_ARM
#define DOCK_ALLOC_PLATFORM_ARM 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_MIPS
#define DOCK_ALLOC_PLATFORM_MIPS 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_ASMJS
#define DOCK_ALLOC_PLATFORM_ASMJS 0
#endif

#ifndef DOCK_ALLOC_PLATFORM_CLANG_X86
#define DOCK_ALLOC_PLATFORM_CLANG_X86 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_CLANG_ARM
#define DOCK_ALLOC_PLATFORM_CLANG_ARM 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_CLANG_MIPS
#define DOCK_ALLOC_PLATFORM_CLANG_MIPS 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_CLANG_ASMJS
#define DOCK_ALLOC_PLATFORM_CLANG_ASMJS 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_GCC_X86
#define DOCK_ALLOC_PLATFORM_GCC_X86 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_GCC_MIPS
#define DOCK_ALLOC_PLATFORM_GCC_MIPS 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_MSVC_X86
#define DOCK_ALLOC_PLATFORM_MSVC_X86 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_MSVC_ARM
#define DOCK_ALLOC_PLATFORM_MSVC_ARM 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_X86
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_X86 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_ARM
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_ARM 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_MIPS
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_MIPS 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_ASMJS
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_ASMJS 0
#endif

#ifndef DOCK_ALLOC_PLATFORM_ARM
#define DOCK_ALLOC_PLATFORM_ARM 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_GCC_ARM
#define DOCK_ALLOC_PLATFORM_GCC_ARM 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_ARM
#define DOCK_ALLOC_PLATFORM_GCC_COMPATIBLE_ARM 0
#endif

#ifndef DOCK_ALLOC_PLATFORM_MMX
#define DOCK_ALLOC_PLATFORM_MMX 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_SSE
#define DOCK_ALLOC_PLATFORM_SSE 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_SSE2
#define DOCK_ALLOC_PLATFORM_SSE2 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_SSE3
#define DOCK_ALLOC_PLATFORM_SSE3 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_SSSE3
#define DOCK_ALLOC_PLATFORM_SSSE3 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_SSE41
#define DOCK_ALLOC_PLATFORM_SSE41 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_SSE42
#define DOCK_ALLOC_PLATFORM_SSE42 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_PCLMUL
#define DOCK_ALLOC_PLATFORM_PCLMUL 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_AVX
#define DOCK_ALLOC_PLATFORM_AVX 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_AVX2
#define DOCK_ALLOC_PLATFORM_AVX2 0
#endif
#ifndef DOCK_ALLOC_PLATFORM_NEON
#define DOCK_ALLOC_PLATFORM_NEON 0
#endif

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

#endif
