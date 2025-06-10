// Copyright 2025 Felix Kahle. All rights reserved.

#include "gtest/gtest.h"
#include "dockalloc/solver/time_interval_tree_node_layout.h"

namespace dockalloc::solver
{
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
