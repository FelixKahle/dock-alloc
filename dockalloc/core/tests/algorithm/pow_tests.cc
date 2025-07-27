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
