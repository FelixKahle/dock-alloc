// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_MISCELLANEOUS_CORE_DEFINES_H_
#define DOCK_ALLOC_CORE_MISCELLANEOUS_CORE_DEFINES_H_

#include "dockalloc/core/miscellaneous/config.h"
#include "dockalloc/core/miscellaneous/inline.h"
#include "dockalloc/core/miscellaneous/compiler.h"
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
