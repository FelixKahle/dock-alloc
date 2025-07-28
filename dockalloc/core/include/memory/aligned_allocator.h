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
#include <memory>
#include <new>
#include <type_traits>
#include <cstddef>
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
        using pointer = T*;
        using const_pointer = const T*;
        using reference = T&;
        using const_reference = const T&;
        using size_type = size_t;
        using difference_type = ptrdiff_t;

        /// @brief The alignment of the allocator.
        static constexpr size_t kAlignment = Alignment;

        template <class U>
        struct rebind
        {
            using other = AlignedAllocator<U, Alignment>;
        };


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
        explicit constexpr AlignedAllocator(const AlignedAllocator<U, Alignment>& other) noexcept
        {
        }

        /// @brief Destructor for AlignedAllocator.
        constexpr DOCK_ALLOC_FORCE_INLINE ~AlignedAllocator() = default;

        // ReSharper disable once CppMemberFunctionMayBeStatic
        /// @brief Allocates memory for n objects of type T.
        ///
        /// @param n The number of objects to allocate.
        ///
        /// @pre n > 0
        /// @pre n <= max_size()
        ///
        /// @return A pointer to the allocated memory. If n is 0, returns nullptr.
        [[nodiscard]] DOCK_ALLOC_FORCE_INLINE T* allocate(const size_type n) noexcept
        {
            [[unlikely]] if (n == 0)
            {
                return nullptr;
            }
            CHECK_LE(n, max_size()) << "Requested allocation for " << n << " elements exceeds maximum size.";
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

        /// @brief Allocates memory for n objects of type T with a hint.
        ///
        /// This function is similar to the allocate function but allows passing a hint
        /// for the allocation. The hint is ignored in this implementation.
        ///
        /// @param n The number of objects to allocate.
        /// @param hint A pointer to a memory location that can be used as a hint for allocation.
        ///
        /// @pre n > 0
        /// @pre n <= max_size()
        ///
        /// @return A pointer to the allocated memory. If n is 0, returns nullptr.
        DOCK_ALLOC_FORCE_INLINE T* allocate(const size_type n, const void* hint) noexcept
        {
            return allocate(n);
        }

        /// @brief Deallocates memory previously allocated for n objects of type T.
        ///
        /// @param p Pointer to the memory to deallocate.
        //ReSharper disable once CppMemberFunctionMayBeStatic
        DOCK_ALLOC_FORCE_INLINE void deallocate(T* p, size_type) noexcept
        {
#if DOCK_ALLOC_PLATFORM_WINDOWS
            _aligned_free(p);
#else
            free(p);
#endif
        }

        /// @brief Returns the maximum number of objects of type T that can be allocated.
        ///
        /// @return The maximum number of objects that can be allocated without exceeding
        // ReSharper disable once CppMemberFunctionMayBeStatic
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE size_type max_size() const noexcept
        {
            return std::numeric_limits<size_type>::max() / sizeof(T);
        }

        /// @brief Constructs an object of type U in the allocated memory.
        ///
        /// This function constructs an object of type U at the specified memory location
        ///
        /// @tparam U The type of the object to construct.
        /// @tparam Args The types of the arguments to pass to the constructor of U.
        ///
        /// @param p Pointer to the memory location where the object should be constructed.
        /// @param args The arguments to pass to the constructor of U.
        ///
        /// @pre p != nullptr
        template <class U, class... Args>
            requires std::constructible_from<U, Args...>
        DOCK_ALLOC_FORCE_INLINE void construct(U* p, Args&&... args) noexcept
        {
            DCHECK_NE(p, nullptr);
            new(static_cast<void*>(p)) U(std::forward<Args>(args)...);
        }

        // ReSharper disable once CppMemberFunctionMayBeStatic
        /// @brief Destroys an object of type U at the specified memory location.
        ///
        /// This function calls the destructor of the object at the specified memory location.
        ///
        /// @tparam U The type of the object to destroy.
        ///
        /// @param p Pointer to the memory location where the object is located.
        template <class U>
        DOCK_ALLOC_FORCE_INLINE void destroy(U* p) noexcept
        {
            DCHECK_NE(p, nullptr);
            p->~U();
        }

        // ReSharper disable once CppMemberFunctionMayBeStatic
        /// @brief Returns the address of the object referenced by r.
        ///
        /// This function returns the address of the object referenced by r.
        ///
        /// @param r The reference to the object.
        ///
        /// @return A pointer to the object referenced by r.
        [[deprecated(
            "The 'address' member is obsolete (deprecated in C++17, removed in C++20). Please use std::to_address() instead."
        )]]
        DOCK_ALLOC_FORCE_INLINE auto address(reference r) noexcept -> pointer
        {
            return &r;
        }

        // ReSharper disable once CppMemberFunctionMayBeStatic
        /// @brief Returns the address of the object referenced by r (const version).
        ///
        /// This function returns the address of the object referenced by r.
        ///
        /// @param r The const reference to the object.
        ///
        /// @return A const pointer to the object referenced by r.
        [[deprecated(
            "The 'address' member is obsolete (deprecated in C++17, removed in C++20). Please use std::to_address() instead."
        )]]
        DOCK_ALLOC_FORCE_INLINE auto address(const_reference r) const noexcept -> const_pointer
        {
            return &r;
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
