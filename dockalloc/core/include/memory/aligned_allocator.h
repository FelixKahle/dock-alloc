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

#include <memory>
#include <type_traits>
#include <concepts>
#include <cassert>
#if DOCK_ALLOC_PLATFORM_WINDOWS
#include <malloc.h>
#else
#include <cstdlib>
#endif
#include "absl/log/check.h"
#include "dockalloc/core/miscellaneous/core_defines.h"
#include "dockalloc/core/type_traits/type_traits.h"

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
        requires IsPowerOfTwo_v<Alignment> && (Alignment >= sizeof(void*))
    class AlignedAllocator
    {
    public:
        using value_type = T;
        using size_type = size_t;
        using difference_type = ptrdiff_t;

        /// @brief Rebind structure for \c AlignedAllocator.
        ///
        /// This structure allows the allocator to be used with different types
        /// while maintaining the same alignment.
        template <typename U>
        struct rebind
        {
            using other = AlignedAllocator<U, Alignment>;
        };

        /// @brief The alignment of the allocator.
        static constexpr size_t kAlignment = Alignment;

        /// @brief Default constructor for AlignedAllocator.
        ///
        /// This constructor initializes an instance of AlignedAllocator.
        constexpr AlignedAllocator() noexcept = default;

        /// @brief Copy constructor for AlignedAllocator.
        ///
        /// This constructor creates a new instance of AlignedAllocator by copying
        /// another instance of AlignedAllocator.
        ///
        /// @param other The instance to copy from.
        constexpr AlignedAllocator(const AlignedAllocator& other) noexcept = default;

        /// @brief Copy constructor for AlignedAllocator with a different type.
        ///
        /// This constructor allows creating an instance of AlignedAllocator
        /// from another instance of AlignedAllocator with a different type but the same alignment.
        ///
        /// @tparam U The type of the other allocator.
        /// @param other The instance to copy from.
        template <typename U>
        explicit constexpr DOCK_ALLOC_FORCE_INLINE AlignedAllocator(
            [[maybe_unused]] const AlignedAllocator<U, Alignment>& other) noexcept
        {
        }

        /// @brief Destructor for AlignedAllocator.
        constexpr DOCK_ALLOC_FORCE_INLINE ~AlignedAllocator() = default;

        // ReSharper disable once CppMemberFunctionMayBeStatic
        /// @brief Allocates memory for n objects of type T.
        ///
        /// @note Any errors during allocation will result in an assertion failure
        /// and thus in a crash of the program. This is intended behavior - allocation failure
        /// creates security issues and should be avoided at all costs.
        ///
        /// @param n The number of objects to allocate.
        ///
        /// @pre n > 0
        /// @pre n <= max_size()
        ///
        /// @return A pointer to the allocated memory. If n is 0, returns nullptr.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE T* allocate(const size_type n) noexcept
        {
            // ReSharper disable once CppUnsignedZeroComparison
            static_assert(IsComplete_v<T>, "cannot allocate memory for an incomplete type"); // NOLINT(*-sizeof-expression)

            [[unlikely]] if (n == 0)
            {
                return nullptr;
            }
            CHECK_LE(n, std::allocator_traits<AlignedAllocator>::max_size(*this)) <<
                "Requested allocation for " << n << " elements exceeds maximum size.";
            const size_type size = n * sizeof(T);

#if DOCK_ALLOC_PLATFORM_WINDOWS
            void* ptr = _aligned_malloc(size, Alignment);
#else
            void* ptr = nullptr;
            if (posix_memalign(&ptr, Alignment, size) != 0)
            {
                ptr = nullptr;
            }
#endif
            CHECK_NE(ptr, nullptr) << "Memory allocation failed for size: " << size;

            return static_cast<T*>(ptr);
        }

        /// @brief Deallocates memory previously allocated for n objects of type T.
        ///
        /// @param p Pointer to the memory to deallocate.
        /// @param n number of objects earlier passed to allocate(),
        /// or a number between requested and actually allocated number of objects via allocate_at_least()
        /// (maybe equal to either bound)
        //ReSharper disable once CppMemberFunctionMayBeStatic
        DOCK_ALLOC_FORCE_INLINE void deallocate(T* p, [[maybe_unused]] size_type n) noexcept
        {
            // ReSharper disable once CppUnsignedZeroComparison
            static_assert(IsComplete_v<T>, "cannot deallocate memory for an incomplete type"); // NOLINT(*-sizeof-expression)

#if DOCK_ALLOC_PLATFORM_WINDOWS
            _aligned_free(p);
#else
            free(p);
#endif
        }

        using is_always_equal = std::true_type;
        using propagate_on_container_move_assignment = std::true_type;
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
    /// @param left The first allocator to compare.
    /// @param right The second allocator to compare.
    ///
    /// @return \c true if both allocators have the same alignment, \c false otherwise.
    template <typename T1, size_t A1, typename T2, size_t A2>
    constexpr DOCK_ALLOC_FORCE_INLINE bool operator==([[maybe_unused]] const AlignedAllocator<T1, A1>& left,
                                                      [[maybe_unused]] const AlignedAllocator<T2, A2>& right) noexcept
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
    /// @param left The first allocator to compare.
    /// @param right The second allocator to compare.
    ///
    /// @return \c true if the allocators have different alignments, \c false otherwise.
    template <typename T1, size_t A1, typename T2, size_t A2>
    constexpr DOCK_ALLOC_FORCE_INLINE bool operator!=([[maybe_unused]] const AlignedAllocator<T1, A1>& left,
                                                      [[maybe_unused]] const AlignedAllocator<T2, A2>& right) noexcept
    {
        return A1 != A2;
    }
}

#endif
