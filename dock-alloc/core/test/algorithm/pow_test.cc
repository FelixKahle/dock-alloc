// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/core/algorithm/pow.h"

namespace dockalloc::core
{
    static_assert(NextPowerOfTwo(0) == 1, "NextPowerOfTwo(0) should be 1");
    static_assert(NextPowerOfTwo(1) == 1, "NextPowerOfTwo(1) should be 1");
    static_assert(NextPowerOfTwo(3) == 4, "NextPowerOfTwo(3) should be 4");
    static_assert(NextPowerOfTwo(4) == 4, "NextPowerOfTwo(4) should be 4");
    static_assert(NextPowerOfTwo(5) == 8, "NextPowerOfTwo(5) should be 8");
    static_assert(NextPowerOfTwo(6) == 8, "NextPowerOfTwo(6) should be 8");
    static_assert(NextPowerOfTwo(7) == 8, "NextPowerOfTwo(7) should be 8");
    static_assert(NextPowerOfTwo(8) == 8, "NextPowerOfTwo(8) should be 8");

    TEST(PowTest, NextPowerOfTwoWorks)
    {
        EXPECT_EQ(NextPowerOfTwo(0), 1);
        EXPECT_EQ(NextPowerOfTwo(1), 1);
        EXPECT_EQ(NextPowerOfTwo(2), 2);
        EXPECT_EQ(NextPowerOfTwo(3), 4);
        EXPECT_EQ(NextPowerOfTwo(4), 4);
        EXPECT_EQ(NextPowerOfTwo(5), 8);
        EXPECT_EQ(NextPowerOfTwo(6), 8);
        EXPECT_EQ(NextPowerOfTwo(7), 8);
        EXPECT_EQ(NextPowerOfTwo(8), 8);
    }
}
