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

// When building for Android __linux__ is defined, but we want to distinguish between
// Android and other Linux platforms. Therefore, we check for __ANDROID__ first.
#ifdef __ANDROID__
#define DOCK_ALLOC_PLATFORM_ANDROID 1
#define DOCK_ALLOC_PLATFORM_LINUX 0
#else
#define DOCK_ALLOC_PLATFORM_ANDROID 0
#ifdef __linux__
#define DOCK_ALLOC_PLATFORM_LINUX 1
#else
#define DOCK_ALLOC_PLATFORM_LINUX 0
#endif
#endif

#ifdef _WIN32
#define DOCK_ALLOC_PLATFORM_WINDOWS 1
#else
#define DOCK_ALLOC_PLATFORM_WINDOWS 0
#endif

#ifdef WINAPI_FAMILY
#include <winapifamily.h>
#if WINAPI_FAMILY_PARTITION(WINAPI_PARTITION_PHONE_APP)
#define DOCK_ALLOC_PLATFORM_WINDOWS_PHONE 1
#else
#define DOCK_ALLOC_PLATFORM_WINDOWS_PHONE 0
#endif
#else
#define DOCK_ALLOC_PLATFORM_WINDOWS_PHONE 0
#endif

#ifdef __APPLE__
#include <TargetConditionals.h>
#if TARGET_OS_IPHONE
#define DOCK_ALLOC_PLATFORM_IOS 1
#else
#define DOCK_ALLOC_PLATFORM_IOS 0
#endif
#if TARGET_OS_MAC
#define DOCK_ALLOC_PLATFORM_MAC 1
#else
#define DOCK_ALLOC_PLATFORM_MAC 0
#endif
#else
#define DOCK_ALLOC_PLATFORM_IOS 0
#define DOCK_ALLOC_PLATFORM_MAC 0
#endif

#ifdef __EMSCRIPTEN__
#define DOCK_ALLOC_PLATFORM_EMSCRIPTEN 1
#else
#define DOCK_ALLOC_PLATFORM_EMSCRIPTEN 0
#endif

#ifdef __FreeBSD__
#define DOCK_ALLOC_PLATFORM_FREEBSD 1
#else
#define DOCK_ALLOC_PLATFORM_FREEBSD 0
#endif

#if (DOCK_ALLOC_PLATFORM_LINUX \
    + DOCK_ALLOC_PLATFORM_ANDROID \
    + DOCK_ALLOC_PLATFORM_WINDOWS \
    + DOCK_ALLOC_PLATFORM_WINDOWS_PHONE \
    + DOCK_ALLOC_PLATFORM_IOS \
    + DOCK_ALLOC_PLATFORM_MAC \
    + DOCK_ALLOC_PLATFORM_EMSCRIPTEN \
    + DOCK_ALLOC_PLATFORM_FREEBSD) != 1
#error "Unable to determine operating system or multiple platforms detected"
#endif

#endif
