// Copyright 2025 Felix Kahle. All rights reserved.

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
