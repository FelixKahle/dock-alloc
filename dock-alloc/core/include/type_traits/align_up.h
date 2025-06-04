// Copyright 2025 Felix Kahle. All rights reserved.

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
