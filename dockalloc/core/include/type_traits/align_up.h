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

#ifndef DOCK_ALLOC_CORE_TYPE_TRAITS_ALIGN_UP_H_
#define DOCK_ALLOC_CORE_TYPE_TRAITS_ALIGN_UP_H_

namespace dockalloc::core
{
    /// @brief Aligns a size up to the next multiple of \p Align.
    ///
    /// This is useful for ensuring that memory allocations are aligned to a specific boundary.
    ///
    /// @tparam N The size to align.
    /// @tparam Align The alignment boundary. Must be greater than \c 0.
    template <size_t N, size_t Align>
        requires (Align > 0)
    struct AlignUp
    {
        enum
        {
            /// @brief The aligned size.
            Value = ((N + Align - 1) / Align) * Align
        };
    };

    /// @brief Aligns a size up to the next multiple of \p Align.
    ///
    /// This is useful for ensuring that memory allocations are aligned to a specific boundary.
    /// Shortcut for using the \c AlignUp struct.
    ///
    /// @tparam N The size to align.
    /// @tparam Align The alignment boundary. Must be greater than \c 0.
    template <size_t N, size_t Align>
    inline constexpr size_t AlignUp_v = AlignUp<N, Align>::Value;
}

#endif
