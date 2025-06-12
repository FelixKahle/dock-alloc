// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/core/algorithm/almost_equal.h"

namespace dockalloc::core
{
    TEST(AlmostEqualTest, SameValueReturnsTrue)
    {
        EXPECT_TRUE(AlmostEqual(1.0, 1.0));
    }

    TEST(AlmostEqualTest, DifferentValuesWithinEpsilonReturnsTrue)
    {
        constexpr double kEpsilon = std::numeric_limits<double>::epsilon();

        EXPECT_TRUE(AlmostEqual(1.0, 1.0 + kEpsilon * 0.5));
        EXPECT_TRUE(AlmostEqual(1.0, 1.0 - kEpsilon * 0.5));
    }
}
