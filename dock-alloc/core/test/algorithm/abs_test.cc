// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/core/algorithm/abs.h"

namespace dockalloc::core
{
    TEST(AbsTest, PositiveValueReturnsSame)
    {
        EXPECT_EQ(Abs(5), 5);
        EXPECT_EQ(Abs(3.14), 3.14);
    }

    TEST(AbsTest, NegativeValueReturnsPositive)
    {
        EXPECT_EQ(Abs(-5), 5);
        EXPECT_EQ(Abs(-3.14), 3.14);
    }
}
