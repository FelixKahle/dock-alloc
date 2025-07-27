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

#ifndef DOCK_ALLOC_CORE_TYPE_TRAITS_BIGGER_SIZE_H_
#define DOCK_ALLOC_CORE_TYPE_TRAITS_BIGGER_SIZE_H_

namespace dockalloc::core
{
    /// @brief A type trait to determine if the size of type \p A is greater than that of type \p B.
    ///
    /// This trait can be used to compare the size of \p A is greater than the size of \p B.
    ///
    /// @tparam A The first type to compare.
    /// @tparam B The second type to compare.
    template <typename A, typename B>
    struct BiggerSize
    {
        enum
        {
            /// @brief The value is \c true if the size of type \p A is greater than that of type \p B.
            ///
            /// This is \c true if \c sizeof(A) is greater than \c sizeof(B).
            /// So in detail, this evaluates to \c true if \code sizeof(A) > sizeof(B)\endcode.
            Value = sizeof(A) > sizeof(B)
        };
    };

    /// @brief A helper variable template to simplify usage of the \c BiggerSize type trait.
    ///
    /// This variable template can be used to check if the size of type \p A is greater than that of type \p B.
    /// It is equivalent to \c BiggerSize<A, B>::Value, but provides a more concise syntax.
    /// This is \c true if \c sizeof(A) is greater than \c sizeof(B).
    /// So in detail, this evaluates to \c true if \code sizeof(A) > sizeof(B)\endcode.
    template <typename A, typename B>
    inline constexpr bool BiggerSize_v = BiggerSize<A, B>::Value;
}

#endif
