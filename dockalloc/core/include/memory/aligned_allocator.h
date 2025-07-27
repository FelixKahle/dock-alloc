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

#ifndef DOCK_ALLOC_CORE_MEMORY_ALIGNED_ALLOCATOR_H_
#define DOCK_ALLOC_CORE_MEMORY_ALIGNED_ALLOCATOR_H_

#include <limits>
#include <cstdint>
#include <cstdlib>
#include <memory>
#include <new>
#include <type_traits>
#include <cstddef>
#include <cassert>
#include "absl/log/check.h"
#include "dockalloc/core/miscellaneous/core_defines.h"

namespace dockalloc::core
{
    /// @brief Allocator that provides memory allocation with a specified alignment.
    ///
    /// This allocator can be used with standard containers to ensure that
    /// the allocated memory is aligned to a specified boundary, which is useful
    /// for performance optimizations or hardware requirements.
    ///
    /// @tparam T The type of objects to allocate.
    /// @tparam Alignment The alignment boundary in bytes. Must be a power of two and
    /// at least as large as the size of a pointer.
    template <typename T, size_t Alignment>
        requires ((Alignment & (Alignment - 1)) == 0) && (Alignment >= sizeof(void*))
    class AlignedAllocator
    {
    public:
        using value_type = T;
        using pointer = T*;
        using const_pointer = const T*;
        using size_type = size_t;
        using difference_type = std::ptrdiff_t;

        template <typename U>
        struct rebind
        {
            using other = AlignedAllocator<U, Alignment>;
        };

        constexpr AlignedAllocator() noexcept = default;

        template <typename U>
        explicit constexpr AlignedAllocator(const AlignedAllocator<U, Alignment>&) noexcept
        {
        }

        // ReSharper disable once CppMemberFunctionMayBeStatic
        /// @brief Allocates memory for n objects of type T.
        ///
        /// @param n The number of objects to allocate.
        ///
        /// @pre n > 0
        ///
        /// @return A pointer to the allocated memory. If n is 0, returns nullptr.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE T* allocate(const size_type n) noexcept
        {
            [[unlikely]] if (n == 0)
            {
                return nullptr;
            }

            const size_type size = n * sizeof(T);
            const size_type padded_size = ((size + Alignment - 1) / Alignment) * Alignment;

            void* ptr = std::aligned_alloc(Alignment, padded_size);
            DCHECK_NE(ptr, nullptr) << "Memory allocation failed for size: " << padded_size;

            return static_cast<T*>(ptr);
        }

        /// @brief Deallocates memory previously allocated for n objects of type T.
        ///
        /// @param p Pointer to the memory to deallocate.
        //ReSharper disable once CppMemberFunctionMayBeStatic
        DOCK_ALLOC_FORCE_INLINE void deallocate(T* p, size_type) noexcept
        {
            std::free(p);
        }

        /// @brief Returns the maximum number of objects of type T that can be allocated.
        ///
        /// @return The maximum number of objects that can be allocated without exceeding
        // ReSharper disable once CppMemberFunctionMayBeStatic
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE size_type max_size() const noexcept
        {
            return std::numeric_limits<size_type>::max() / sizeof(T);
        }

        using is_always_equal = std::true_type;
        using propagate_on_container_copy_assignment = std::true_type;
        using propagate_on_container_move_assignment = std::true_type;
        using propagate_on_container_swap = std::true_type;
    };

    /// @brief Comparison operator for AlignedAllocator.
    ///
    /// This operator checks if two allocators are equal based on their alignment.
    ///
    /// @tparam T1 The type of the first allocator.
    /// @tparam A1 The alignment of the first allocator.
    /// @tparam T2 The type of the second allocator.
    /// @tparam A2 The alignment of the second allocator.
    ///
    /// @return \c true if both allocators have the same alignment, \c false otherwise.
    template <typename T1, size_t A1, typename T2, size_t A2>
    constexpr DOCK_ALLOC_FORCE_INLINE bool operator==(const AlignedAllocator<T1, A1>&,
                                                      const AlignedAllocator<T2, A2>&) noexcept
    {
        return A1 == A2;
    }

    /// @brief Inequality operator for AlignedAllocator.
    ///
    /// This operator checks if two allocators are not equal based on their alignment.
    ///
    /// @tparam T1 The type of the first allocator.
    /// @tparam A1 The alignment of the first allocator.
    /// @tparam T2 The type of the second allocator.
    /// @tparam A2 The alignment of the second allocator.
    ///
    /// @return \c true if the allocators have different alignments, \c false otherwise.
    template <typename T1, size_t A1, typename T2, size_t A2>
    constexpr DOCK_ALLOC_FORCE_INLINE bool operator!=(const AlignedAllocator<T1, A1>&,
                                                      const AlignedAllocator<T2, A2>&) noexcept
    {
        return A1 != A2;
    }
}

#endif
