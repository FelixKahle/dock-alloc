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

#ifndef DOCK_ALLOC_CORE_ALGORITHM_POW_H_
#define DOCK_ALLOC_CORE_ALGORITHM_POW_H_

#include <type_traits>
#include <concepts>
#include <limits>
#include "dockalloc/core/include/miscellaneous/core_defines.h"

namespace dockalloc::core
{
    /// @brief Checks if the given value is a power of two.
    ///
    /// This function checks whether the specified value is a power of two.
    ///
    /// @note Negative values are *NOT* considered powers of two, and zero is also *NOT* a power of two.
    ///
    /// @tparam T The type of the value. Must be an integral type.
    /// @param value The value to check.
    ///
    /// @return True if the value is a power of two, false otherwise.
    template <typename T>
        requires std::integral<T>
    [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE bool IsPowerOfTwo(const T value) noexcept
    {
        return value > 0 && (value & (value - 1)) == 0;
    }
}

#endif
