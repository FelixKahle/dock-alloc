// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/time_interval_tree_node_layout.h"

namespace dockalloc::solver
{
    // Check that my layout machinery is able to detect the best layout for various types and sizes.
    // I use a static_assert to ensure that the correct layout is chosen for some chosen types and sizes.

    static_assert(
        std::is_same_v<internal::LayoutImpl<uint32_t, void*, 16>::Base, internal::TimeIntervalTreeNodeFieldLayout<
                           uint32_t, void*, 16, internal::TimeIntervalTreeNodeFieldLayoutOrder::PointerTimeIndex>>,
        "Incorrect layout chosen for uint32_t, void*, 16: Expected PointerTimeIndex order");

    static_assert(
        std::is_same_v<internal::LayoutImpl<uint64_t, void*, 16>::Base, internal::TimeIntervalTreeNodeFieldLayout<
                           uint64_t, void*, 16, internal::TimeIntervalTreeNodeFieldLayoutOrder::TimePointerIndex>>,
        "Incorrect layout chosen for uint64_t, void*, 16: Expected TimePointerIndex order");

    static_assert(
        std::is_same_v<internal::LayoutImpl<uint8_t, void*, 120000>::Base, internal::TimeIntervalTreeNodeFieldLayout<
                           uint8_t, void*, 120000, internal::TimeIntervalTreeNodeFieldLayoutOrder::PointerIndexTime>>,
        "Incorrect layout chosen for uint8_t, void*, 120000: Expected PointerIndexTime order");


    TEST(IntervalStorageTest, ConstructorWithInterval)
    {
        constexpr core::TimeInterval<uint32_t> interval{10, 20};

        internal::IntervalStorage<uint32_t> storage(interval);
        EXPECT_EQ(storage.Get(), interval);
    }

    TEST(IntervalStorageTest, SetAndGet)
    {
        constexpr core::TimeInterval<uint32_t> interval{10, 20};

        internal::IntervalStorage<uint32_t> storage;
        storage.Set(interval);
        EXPECT_EQ(storage.Get(), interval);
    }
}
