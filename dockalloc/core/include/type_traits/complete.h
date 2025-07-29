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

#ifndef DOCK_ALLOC_CORE_TYPE_TRAITS_COMPLETE_H_
#define DOCK_ALLOC_CORE_TYPE_TRAITS_COMPLETE_H_

namespace dockalloc::core
{
    /// @brief A type trait to check if a type is complete.
    ///
    /// This trait can be used to determine if a type is complete, meaning that its size can be determined.
    /// A type is considered complete if it has a defined size, which is the case for
    /// all types except for incomplete types like forward declarations of classes or structs.
    template <typename T>
    struct IsComplete
    {
        enum
        {
            /// @brief The value is \c true if the type \p T is complete, and \c false if it is incomplete.
            Value = requires { sizeof(T); }
        };
    };

    /// @brief A helper variable template to simplify usage of the \c IsComplete type trait.
    ///
    /// This variable template can be used to check if a type is complete.
    /// It is equivalent to \c IsComplete<T>::Value, but provides a more concise
    /// syntax.
    template <typename T>
    constexpr inline bool IsComplete_v = IsComplete<T>::Value;
}

#endif
