// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_CORE_ALGORITHM_ALMOST_EQUAL_H_
#define DOCK_ALLOC_CORE_ALGORITHM_ALMOST_EQUAL_H_

#include <limits>
#include <type_traits>
#include "dockalloc/core/miscellaneous/core_defines.h"
#include "dockalloc/core/algorithm/abs.h"

namespace dockalloc::core
{
    /// @brief Checks if two arithmetic values are approximately equal within a given epsilon.
    ///
    /// This function compares two arithmetic values and determines if they are
    /// approximately equal within a specified epsilon value.
    ///
    /// @tparam LeftType The type of the left-hand side value.
    /// @tparam RightType The type of the right-hand side value (default is the same as LeftType).
    /// @tparam EpsilonType The type of the epsilon value (default is the common type of LeftType and RightType).
    /// @param left The left-hand side value to compare.
    /// @param right The right-hand side value to compare.
    /// @param epsilon The epsilon value to use for the comparison
    /// (default is the machine epsilon for the common type of LeftType and RightType).
    ///
    /// @note For integer types, the default epsilon is zero, meaning the values must be exactly equal.
    /// This behavior can be overridden by providing a non-zero epsilon value, but comparing integers for equality
    /// should rely on a zero epsilon tolerance.
    ///
    /// @return \c true if the values are approximately equal, \c false otherwise.
    template <typename LeftType, typename RightType = LeftType, typename EpsilonType = std::common_type_t<
                  LeftType, RightType>>
        requires std::is_arithmetic_v<LeftType> && std::is_arithmetic_v<RightType> && std::is_arithmetic_v<EpsilonType>
        && std::convertible_to<EpsilonType, std::common_type_t<LeftType, RightType>>
    [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE bool AlmostEqual(const LeftType left, const RightType right,
                                                                     const EpsilonType epsilon = std::numeric_limits<
                                                                         std::common_type_t<
                                                                             LeftType, RightType>>::epsilon()) noexcept
    {
        using CommonType = std::common_type_t<LeftType, RightType>;

        if constexpr (std::is_floating_point_v<CommonType>)
        {
            CommonType diff = core::Abs<CommonType>(static_cast<CommonType>(left) - static_cast<CommonType>(right));
            return diff <= static_cast<CommonType>(epsilon);
        }
        else
        {
            // To prevent overflow, we use the following formula:
            CommonType diff = (left > right) ? (left - right) : (right - left);
            return diff <= epsilon;
        }
    }
}

#endif
