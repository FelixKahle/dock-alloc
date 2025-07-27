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
#include "dockalloc/core/memory/aligned_allocator.h"

namespace dockalloc::core
{
    template <typename T>
    DOCK_ALLOC_FORCE_INLINE bool is_aligned(T* ptr, const size_t alignment)
    {
        const auto int_ptr = reinterpret_cast<std::uintptr_t>(ptr);
        return (int_ptr % alignment) == 0;
    }

    TEST(AlignedAllocatorTest, AllocationAndDeallocation)
    {
        // Define an allocator for integers with 64-byte alignment.
        AlignedAllocator<int, 64> alloc;

        // Allocate space for 10 integers.
        int* ptr = alloc.allocate(10);

        // Assert that the allocation was successful.
        ASSERT_NE(ptr, nullptr);

        // Deallocate the memory. The test passes if this doesn't cause a runtime error.
        alloc.deallocate(ptr, 10);
    }

    TEST(AlignedAllocatorTest, IsMemoryCorrectlyAligned)
    {
        // Define an allocator for doubles with 128-byte alignment.
        constexpr size_t alignment = 128;
        AlignedAllocator<double, alignment> alloc;

        // Allocate space for 100 doubles.
        double* ptr = alloc.allocate(100);
        ASSERT_NE(ptr, nullptr);

        // Check if the returned pointer is aligned to 128 bytes.
        EXPECT_TRUE(is_aligned(ptr, alignment)) << "Pointer " << ptr << " is not aligned to " << alignment;

        alloc.deallocate(ptr, 100);
    }

    TEST(AlignedAllocatorTest, WorksWithVariousAlignments)
    {
        {
            constexpr size_t alignment = 16;
            AlignedAllocator<float, alignment> alloc;
            float* ptr = alloc.allocate(10);
            ASSERT_NE(ptr, nullptr);
            EXPECT_TRUE(is_aligned(ptr, alignment));
            alloc.deallocate(ptr, 10);
        }
        {
            constexpr size_t alignment = 32;
            AlignedAllocator<char, alignment> alloc;
            char* ptr = alloc.allocate(50);
            ASSERT_NE(ptr, nullptr);
            EXPECT_TRUE(is_aligned(ptr, alignment));
            alloc.deallocate(ptr, 50);
        }
    }

    TEST(AlignedAllocatorTest, AllocateZeroReturnsNullptr)
    {
        AlignedAllocator<int, 64> alloc;

        // Allocating zero elements should return a nullptr as per the implementation.
        const int* ptr = alloc.allocate(0);
        EXPECT_EQ(ptr, nullptr);
    }

    TEST(AlignedAllocatorTest, Rebind)
    {
        constexpr size_t alignment = 64;
        using AllocatorInt = AlignedAllocator<int, alignment>;

        // Rebind the allocator from `int` to `char`.
        using AllocatorChar = AllocatorInt::rebind<char>::other;

        // Check that the rebound type is what we expect.
        static_assert(std::is_same_v<AllocatorChar, AlignedAllocator<char, alignment>>,
                      "Rebind failed to produce the correct type.");

        AllocatorChar alloc_char;
        char* ptr = alloc_char.allocate(100);
        ASSERT_NE(ptr, nullptr);

        // Verify that the alignment characteristic is preserved after rebinding.
        EXPECT_TRUE(is_aligned(ptr, alignment));

        alloc_char.deallocate(ptr, 100);
    }

    TEST(AlignedAllocatorTest, WorksWithStdVector)
    {
        // Define a struct to use with the vector.
        struct MyData
        {
            double a;
            int b;
            char c[7];
        };

        constexpr size_t alignment = 128;
        using AllocatorMyData = AlignedAllocator<MyData, alignment>;

        // Create a vector that uses our aligned allocator.
        std::vector<MyData, AllocatorMyData> vec;

        // Add elements to the vector. This will trigger allocations.
        vec.reserve(50);
        for (int i = 0; i < 50; ++i)
        {
            vec.push_back({static_cast<double>(i), i, "test"});
        }

        // Check if the vector's internal data buffer is correctly aligned.
        // This is a strong indicator that the allocator is working correctly with the container.
        if (!vec.empty())
        {
            MyData* data_ptr = vec.data();
            EXPECT_TRUE(is_aligned(data_ptr, alignment))
                << "Vector data pointer " << data_ptr << " is not aligned to " << alignment;
        }
    }

    TEST(AlignedAllocatorTest, EqualityOperators)
    {
        // Allocators are stateless, so they should compare equal if their alignment is the same,
        // regardless of the value type.

        // Same type, same alignment.
        constexpr AlignedAllocator<int, 64> alloc1;
        constexpr AlignedAllocator<int, 64> alloc2;
        EXPECT_TRUE(alloc1 == alloc2);
        EXPECT_FALSE(alloc1 != alloc2);

        // Different type, same alignment.
        constexpr AlignedAllocator<double, 64> alloc3;
        EXPECT_TRUE(alloc1 == alloc3);
        EXPECT_FALSE(alloc1 != alloc3);

        // Same type, different alignment.
        constexpr AlignedAllocator<int, 32> alloc4;
        EXPECT_FALSE(alloc1 == alloc4);
        EXPECT_TRUE(alloc1 != alloc4);
    }

    // Test case for the `max_size` method.
    TEST(AlignedAllocatorTest, MaxSize)
    {
        constexpr AlignedAllocator<int, 16> alloc;

        // The max_size should be the maximum value of size_t divided by the size of the element type.
        constexpr auto expected_max_size = std::numeric_limits<size_t>::max() / sizeof(int);
        EXPECT_EQ(alloc.max_size(), expected_max_size);
    }
}
