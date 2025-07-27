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

#ifndef DOCK_ALLOC_CORE_MEMORY_ALIGNED_STORAGE_H_
#define DOCK_ALLOC_CORE_MEMORY_ALIGNED_STORAGE_H_

#include "dockalloc/core/miscellaneous/core_defines.h"

namespace dockalloc::core
{
    /// @brief A class that wraps a pointer to aligned storage.
    ///
    /// This class believes that the pointer it wraps is aligned to a specified alignment,
    /// it does not enforce alignment. The user must ensure that the pointer is correctly aligned
    /// according to the specified alignment. This class does not own the memory it points to,
    /// the user is responsible for managing the lifetime of the data.
    ///
    /// @tparam T The type of the data stored in the aligned storage.
    /// @tparam Alignment The alignment in bytes. Must be a power of two and at least as large as the size of a pointer.
    template <typename T, size_t Alignment>
        requires ((Alignment & (Alignment - 1)) == 0) && (Alignment >= sizeof(void*))
    class AlignedStorage
    {
    public:
        /// @brief Tge alignment in bytes.
        ///
        /// This number specifies the alignment of the storage.
        static constexpr size_t kAlignment = Alignment;

        /// @brief The type of the data stored in the aligned storage.
        ///
        /// This type is used to access the data stored in the aligned storage.
        using Type = T;

        /// @brief The value type of the aligned storage.
        ///
        /// Same as \c Type, but used for compatibility with standard containers and algorithms.
        using value_type = T;

        /// @brief Constructs an \c AlignedStorage with a given pointer.
        ///
        /// This constructor initializes the storage with a pointer to data of type \c T.
        ///
        /// @param data Pointer to the data of type \c T.
        explicit constexpr DOCK_ALLOC_FORCE_INLINE AlignedStorage(T* data) noexcept
            : data_(data)
        {
        }

        /// @brief Returns a pointer to the stored data.
        ///
        /// This function returns a pointer to the data stored in the aligned storage.
        ///
        /// @return A pointer to the data of type \c T.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE const T* Get() const noexcept
        {
            return data_;
        }

        /// @brief Returns a pointer to the stored data.
        ///
        /// This function returns a pointer to the data stored in the aligned storage.
        ///
        /// @return A pointer to the data of type \c T.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE T* Get() noexcept
        {
            return data_;
        }

        /// @brief Sets the pointer to the stored data.
        ///
        /// This function sets the pointer to the data stored in the aligned storage.
        ///
        /// @param data Pointer to the data of type \c T.
        constexpr DOCK_ALLOC_FORCE_INLINE void Set(T* data) noexcept
        {
            data_ = data;
        }

    private:
        T* data_;
    };

    /// @brief Concept that checks if a type is an aligned storage view.
    ///
    /// This concept checks if a type \c S is an aligned storage view, which means it has a \c Type member,
    /// a \c value_type member that is the same as \c Type, a static constant \c kAlignment that is convertible
    /// to \c size_t and provides \c Get() and \c Set() member functions.
    ///
    /// @tparam S The type to check.
    template <typename S>
    concept AlignedStorageView =
        std::same_as<typename S::Type, typename S::value_type> && requires(S s, typename S::Type* p)
        {
            { S::kAlignment } -> std::convertible_to<size_t>;
            { s.Get() } -> std::same_as<typename S::Type*>;
            { std::as_const(s).Get() } -> std::same_as<typename S::Type const*>;
            { s.Set(p) } -> std::same_as<void>;
        };
}

#endif
