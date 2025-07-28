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

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_CORE_DEFINES_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_CORE_DEFINES_H_

// config.h must be included first
#include "dockalloc/core/miscellaneous/config.h"
#include "dockalloc/core/miscellaneous/platform.h"
#include "dockalloc/core/miscellaneous/inline.h"
#include "dockalloc/core/miscellaneous/compiler_check.h"

#define DOCK_ALLOC_DEFAULT_CONSTRUCT(Type) Type() = default;
#define DOCK_ALLOC_DEFAULT_COPY(Type) Type(const Type&) = default;
#define DOCK_ALLOC_DEFAULT_MOVE(Type) Type(Type&&) = default;
#define DOCK_ALLOC_DEFAULT_COPY_ASSIGN(Type) Type& operator=(const Type&) = default;
#define DOCK_ALLOC_DEFAULT_MOVE_ASSIGN(Type) Type& operator=(Type&&)      = default;

#define DOCK_ALLOC_DELETE_CONSTRUCT(Type) Type() = delete;
#define DOCK_ALLOC_DELETE_COPY(Type) Type(const Type&) = delete;
#define DOCK_ALLOC_DELETE_MOVE(Type) Type(Type&&) = delete;
#define DOCK_ALLOC_DELETE_COPY_ASSIGN(Type) Type& operator=(const Type&) = delete;
#define DOCK_ALLOC_DELETE_MOVE_ASSIGN(Type) Type& operator=(Type&&) = delete;

#define DOCK_ALLOC_NON_COPYABLE(Type) \
    DOCK_ALLOC_DELETE_COPY(Type) \
    DOCK_ALLOC_DELETE_COPY_ASSIGN(Type)

#define DOCK_ALLOC_NON_MOVABLE(Type) \
    DOCK_ALLOC_DELETE_MOVE(Type) \
    DOCK_ALLOC_DELETE_MOVE_ASSIGN(Type)

#define DOCK_ALLOC_NON_ASSIGNABLE(Type) \
    DOCK_ALLOC_DELETE_COPY_ASSIGN(Type) \
    DOCK_ALLOC_DELETE_MOVE_ASSIGN(Type)

#define DOCK_ALLOC_RULE_OF_ZERO(Type) \
    DOCK_ALLOC_DEFAULT_CONSTRUCT(Type) \
    DOCK_ALLOC_DEFAULT_COPY(Type) \
    DOCK_ALLOC_DEFAULT_MOVE(Type) \
    DOCK_ALLOC_DEFAULT_COPY_ASSIGN(Type) \
    DOCK_ALLOC_DEFAULT_MOVE_ASSIGN(Type)

#define DOCK_ALLOC_RULE_OF_FIVE(Type) \
    DOCK_ALLOC_DEFAULT_CONSTRUCT(Type) \
    DOCK_ALLOC_DEFAULT_COPY(Type) \
    DOCK_ALLOC_DEFAULT_MOVE(Type) \
    DOCK_ALLOC_DEFAULT_COPY_ASSIGN(Type) \
    DOCK_ALLOC_DEFAULT_MOVE_ASSIGN(Type)

#define DOCK_ALLOC_COPY_ONLY(Type) \
    DOCK_ALLOC_DEFAULT_COPY(Type) \
    DOCK_ALLOC_DELETE_MOVE(Type) \
    DOCK_ALLOC_DELETE_COPY_ASSIGN(Type) \
    DOCK_ALLOC_DELETE_MOVE_ASSIGN(Type)

#define DOCK_ALLOC_MOVE_ONLY(Type) \
    DOCK_ALLOC_DEFAULT_MOVE(Type) \
    DOCK_ALLOC_DELETE_COPY(Type) \
    DOCK_ALLOC_DELETE_COPY_ASSIGN(Type) \
    DOCK_ALLOC_DELETE_MOVE_ASSIGN(Type)

#define DOCK_ALLOC_IMMOVABLE(Type) \
    DOCK_ALLOC_DELETE_MOVE(Type) \
    DOCK_ALLOC_DELETE_MOVE_ASSIGN(Type)

#endif
