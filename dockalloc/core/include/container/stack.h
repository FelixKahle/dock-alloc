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

#ifndef DOCK_ALLOC_CORE_CONTAINER_STACK_H_
#define DOCK_ALLOC_CORE_CONTAINER_STACK_H_

#include <vector>
#include <stack>
#include "dockalloc/core/miscellaneous/core_defines.h"

namespace dockalloc::core
{
    /// @brief A drop in replacement for \c std::stack that allows reserving space in the underlying container
    /// and clearing it.
    ///
    /// This class extends \c std::stack to provide additional functionality for reserving space
    /// in the underlying container and clearing, so that all elements are removed but the internal
    /// buffer is not deallocated.
    /// This might be useful in scenarios where you want to reuse the stack without
    /// deallocating the memory, such as in performance-critical applications or when using or when you know the
    /// amount of elements that will be pushed onto the stack in advance.
    ///
    /// @tparam T The type of elements stored in the stack.
    /// @tparam Container The underlying container type, defaults to \c std::deque<T
    template <typename T, typename Container = std::vector<T>>
    class reservable_stack : public std::stack<T, Container>
    {
        // Note:
        // \c c is from \c std::stack<T, Container> and is the underlying container.
        // you can read more about it here:
        // https://en.cppreference.com/w/cpp/container/stack
    public:
        /// @brief Reserves space for at least \c n elements in the underlying container.
        ///
        /// This function allows you to reserve space in the underlying container
        /// to avoid multiple allocations when pushing elements onto the stack.
        ///
        /// @param n The number of elements to reserve space for.
        DOCK_ALLOC_FORCE_INLINE void reserve(const size_t n) noexcept
        {
            this->c.reserve(n);
        }

        /// @brief Clears the stack, removing all elements but not deallocating the underlying container.
        ///
        /// This function clears the stack by removing all elements from it,
        /// but it does not deallocate the memory used by the underlying container.
        DOCK_ALLOC_FORCE_INLINE void clear() noexcept
        {
            this->c.clear();
        }

        /// @brief Returns the capacity of the underlying container.
        ///
        /// This function returns the number of elements that can be stored in the underlying container
        /// without requiring a reallocation.
        ///
        /// @return The capacity of the underlying container as a \c size_t.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_t capacity() const noexcept
        {
            return this->c.capacity();
        }

        /// @brief Shrinks the underlying container to fit its current size.
        ///
        /// This function reduces the capacity of the underlying container to fit its current size,
        /// effectively deallocating any excess memory.
        DOCK_ALLOC_FORCE_INLINE void shrink_to_fit() noexcept
        {
            this->c.shrink_to_fit();
        }
    };
}

#endif
