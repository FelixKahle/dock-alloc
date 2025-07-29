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

#ifndef DOCK_ALLOC_CORE_TYPE_TRAITS_CONCEPTS_H_
#define DOCK_ALLOC_CORE_TYPE_TRAITS_CONCEPTS_H_

#include <cstddef>
#include <utility>
#include <type_traits>
#include "absl/strings/string_view.h"
#include "absl/hash/hash.h"
#include "absl/strings/str_format.h"

namespace dockalloc::core
{
    /// @brief A concept that checks if a type \p H has a static method \c combine that can be used for hashing.
    ///
    /// This concept is designed to ensure that a type \p H can be used with Absl's hashing utilities.
    /// It requires that the type has a static method \c combine that takes an instance of
    /// \p H and a variable number of arguments, returning an instance of \p H.
    ///
    /// @tparam H The type to check for the \c combine method.
    /// @tparam Args The types of the arguments that can be passed to the \c
    template <typename H, typename... Args>
    concept AbslHasher = requires(H h, Args&&... args)
    {
        { H::combine(std::move(h), args...) } -> std::same_as<H>;
    };

    /// @brief A concept that checks if a type \p T can be hashed using Absl's hashing utilities.
    ///
    /// This concept ensures that a type \p T can be hashed by Absl's hashing utilities,
    /// specifically that it can be passed to an instance of \c absl::Hash<T>() and that the result
    /// is convertible to \c std::size_t.
    ///
    /// @tparam T The type to check for hash compatibility.
    template <typename T>
    concept AbslHashable = requires(T t)
    {
        { absl::Hash<T>()(t) } -> std::convertible_to<std::size_t>;
    };

    /// @brief A concept that checks if a type \p Sink can be used as a sink for Absl string formatting.
    ///
    /// This concept ensures that a type \p Sink has methods for appending strings and characters,
    /// which are required for Absl's string formatting utilities.
    ///
    /// @tparam Sink The type to check for string formatting capabilities.
    template <typename Sink>
    concept AbslStringifySink = requires(Sink& sink, absl::string_view sv, const char* c_str, std::size_t n, char c)
    {
        { sink.Append(sv) };
        { sink.Append(c_str) };
        { sink.Append(n, c) };
    };

    /// @brief A concept that checks if a type \p T can be stringified using Absl's formatting utilities.
    ///
    /// This concept ensures that a type \p T can be formatted using Absl's string formatting utilities,
    /// specifically that it can be passed to \c absl::Format() with a string
    /// view, a C-style string, or a character and size.
    ///
    /// @tparam T The type to check for stringification capabilities.
    template <typename T>
    concept AbslFormattable = requires(const T& x)
    {
        { absl::StrFormat("%v", x) } -> std::same_as<std::string>;
    };
}

#endif
