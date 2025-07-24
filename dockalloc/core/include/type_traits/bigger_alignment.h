// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_TYPE_TRAITS_BIGGER_ALIGNMENT_H_
#define DOCK_ALLOC_CORE_TYPE_TRAITS_BIGGER_ALIGNMENT_H_

namespace dockalloc::core
{
    /// @brief A type trait to determine if the alignment of type \p A is greater than that of type \p B.
    ///
    /// This trait can be used to compare the alignment of \p A is greater than the alignment of \p B.
    ///
    /// @tparam A The first type to compare.
    /// @tparam B The second type to compare.
    template <typename A, typename B>
    struct BiggerAlignment
    {
        enum
        {
            /// @brief The value is \c true if the alignment of type \p A is greater than that of type \p B.
            ///
            /// This is \c true if \c alignof(A) is greater than \c alignof(B).
            /// So in detail, this evaluates to \c true if \code alignof(A) > alignof(B)\endcode.
            Value = alignof(A) > alignof(B)
        };
    };

    /// @brief A helper variable template to simplify usage of the \c BiggerAlignment type trait.
    ///
    /// This variable template can be used to check if the alignment of type \p A is greater than that of type \p B.
    /// It is equivalent to \c BiggerAlignment<A, B>::Value, but provides a more concise syntax.
    /// This is \c true if \c alignof(A) is greater than \c alignof(B).
    /// So in detail, this evaluates to \c true if \code alignof(A) > alignof(B)\endcode.
    ///
    /// @tparam A The first type to compare.
    /// @tparam B The second type to compare.
    template <typename A, typename B>
    inline constexpr bool BiggerAlignment_v = BiggerAlignment<A, B>::Value;
}

#endif
