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

#include <type_traits>
#include "dockalloc/core/type_traits/smallest_for.h"

namespace dockalloc::core::test
{
    static_assert(std::is_same_v<SmallestSignedFor_t<-120>, int8_t>);
    static_assert(std::is_same_v<SmallestSignedFor_t<32'000>, int16_t>);
    static_assert(std::is_same_v<SmallestSignedFor_t<-1'000'000>, int32_t>);
    static_assert(std::is_same_v<SmallestSignedFor_t<5'000'000'000>, int64_t>);

    static_assert(std::is_same_v<SmallestUnsignedFor<42>::Type, uint8_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<255>::Type, uint8_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<256>::Type, uint16_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<65535>::Type, uint16_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<65536>::Type, uint32_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<4294967295ULL>::Type, uint32_t>);
    static_assert(std::is_same_v<SmallestUnsignedFor<4294967296ULL>::Type, uint64_t>);
}
