// Copyright 2025 Felix Kahle. All rights reserved.

#include <type_traits>
#include "dockalloc/core/type_traits/smallest_unsigned_for.h"

namespace dockalloc::core::test
{
    static_assert(std::is_same_v<SmallestUnsignedFor<42>::Type, uint8_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<255>::Type, uint8_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<256>::Type, uint16_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<65535>::Type, uint16_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<65536>::Type, uint32_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<4294967295ULL>::Type, uint32_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<4294967296ULL>::Type, uint64_t>);
}
