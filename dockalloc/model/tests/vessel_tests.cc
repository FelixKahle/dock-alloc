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
#include "dockalloc/model/vessel.h"

namespace dockalloc::model
{
    TEST(VesselTest, ConstructionAndProperties)
    {
        constexpr Vessel vessel(100, 20, 5);

        EXPECT_EQ(vessel.GetLength(), 100);
        EXPECT_EQ(vessel.GetWidth(), 20);
        EXPECT_EQ(vessel.GetDraft(), 5);
    }

    TEST(VesselTest, EqualityAndInequality)
    {
        constexpr Vessel vessel1(100, 20, 5);
        constexpr Vessel vessel2(100, 20, 5);
        constexpr Vessel vessel3(120, 20, 5);

        EXPECT_EQ(vessel1, vessel2);
        EXPECT_NE(vessel1, vessel3);
    }

    TEST(VesselScenarioTest, ConstructionAndProperties)
    {
        constexpr VesselScenario<uint32_t, uint32_t, double> scenario(0.8, 10, 20, 5, 1, 2, 3);

        EXPECT_EQ(scenario.GetProbability(), 0.8);
        EXPECT_EQ(scenario.GetArrivalTime(), 10);
        EXPECT_EQ(scenario.GetPlannedDepartureTime(), 20);
        EXPECT_EQ(scenario.GetProcessingTime(), 5);
        EXPECT_EQ(scenario.GetCostDelayPerUnit(), 1);
        EXPECT_EQ(scenario.GetCostLateDeparture(), 2);
        EXPECT_EQ(scenario.GetCostBerthOffset(), 3);
    }

    TEST(VesselScenarioTest, EqualityAndInequality)
    {
        constexpr VesselScenario<uint32_t, uint32_t, double> scenario1(0.8, 10, 20, 5, 1, 2, 3);
        constexpr VesselScenario<uint32_t, uint32_t, double> scenario2(0.8, 10, 20, 5, 1, 2, 3);
        constexpr VesselScenario<uint32_t, uint32_t, double> scenario3(0.9, 15, 25, 6, 2, 3, 4);

        EXPECT_EQ(scenario1, scenario2);
        EXPECT_NE(scenario1, scenario3);
    }
}
