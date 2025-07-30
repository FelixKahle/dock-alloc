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

#ifndef DOCK_ALLOC_SOLVER_CONTAINER_FREE_INTERVAL_H_
#define DOCK_ALLOC_SOLVER_CONTAINER_FREE_INTERVAL_H_

#include "absl/hash/hash.h"
#include "absl/strings/str_format.h"
#include "dockalloc/core/miscellaneous/core_defines.h"
#include "dockalloc/core/include/type_traits/concepts.h"

namespace dockalloc::solver
{
    /// @brief Represents a free run on a quay with a start and a length.
    ///
    /// This allows to compress the information about free spaces on a quay into two unsigned integers.
    ///
    /// @tparam T The type of the start and length of the free interval. Must be an unsigned integral type.
    template <typename T>
        requires std::unsigned_integral<T>
    class FreeInterval
    {
    public:
        /// @brief Default constructor for FreeInterval.
        ///
        /// This destructor initializes the FreeInterval with default values (0 for start and length).
        constexpr DOCK_ALLOC_FORCE_INLINE FreeInterval() noexcept = default;

        /// @brief Constructs a FreeInterval with the specified start and length.
        ///
        /// This constructor initializes the FreeInterval with the given start and length values.
        ///
        /// @param start The starting point of the free interval.
        /// @param length The length of the free interval.
        explicit constexpr DOCK_ALLOC_FORCE_INLINE FreeInterval(const T start, const T length) noexcept
            : start_(start), length_(length)
        {
        }

        /// @brief Returns the start of the free interval.
        ///
        /// This method retrieves the starting point of the free interval.
        ///
        /// @return The start of the free interval.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE T GetStart() const noexcept
        {
            return start_;
        }

        /// @brief Returns the length of the free interval.
        ///
        /// This method retrieves the length of the free interval.
        ///
        /// @return The length of the free interval.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE T GetLength() const noexcept
        {
            return length_;
        }

        /// @brief Returns the end of the free interval.
        ///
        /// This method calculates the end of the free interval by adding the start and length.
        ///
        /// @return The end of the free interval, which is the sum of start and length.
        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE T End() const noexcept
        {
            return start_ + length_;
        }

        [[nodiscard]] constexpr DOCK_ALLOC_FORCE_INLINE bool IsEmpty() const noexcept
        {
            return length_ == 0;
        }

        /// @brief Compares two FreeInterval objects for equality.
        ///
        /// This method checks if the start and length of two FreeInterval objects are equal.
        ///
        /// @tparam U The type of the other FreeInterval's start and length. Must be an unsigned integral type.
        ///
        /// @param left The left-hand side FreeInterval to compare.
        /// @param right The right-hand side FreeInterval to compare.
        ///
        /// @return \c true if the start and length of both FreeInterval objects are equal, \c false otherwise.
        template <typename U>
            requires std::unsigned_integral<U>
        friend constexpr DOCK_ALLOC_FORCE_INLINE bool operator==(FreeInterval const& left,
                                                                 FreeInterval<U> const& right) noexcept
        {
            return left.GetStart() == right.GetStart() && left.GetLength() == right.GetLength();
        }

        /// @brief Compares two FreeInterval objects for inequality.
        ///
        /// This method checks if the start and length of two FreeInterval objects are not equal.
        ///
        /// @tparam U The type of the other FreeInterval's start and length. Must be an unsigned integral type.
        ///
        /// @param left The left-hand side FreeInterval to compare.
        /// @param right The right-hand side FreeInterval to compare.
        ///
        /// @return \c true if the start or length of the FreeInterval objects are not equal, \c false otherwise.
        template <typename U>
            requires std::unsigned_integral<U>
        friend constexpr DOCK_ALLOC_FORCE_INLINE bool operator!=(FreeInterval const& left,
                                                                 FreeInterval<U> const& right) noexcept
        {
            return !(left == right);
        }

        /// @brief Compares two FreeInterval objects for less-than relation.
        ///
        /// This method checks if the start of the left FreeInterval is less than the start of the right FreeInterval,
        /// or if the starts are equal, whether the length of the left FreeInterval is less
        /// than the length of the right FreeInterval.
        ///
        /// @tparam U The type of the other FreeInterval's start and length. Must be an unsigned integral type.
        ///
        /// @param left The left-hand side FreeInterval to compare.
        /// @param right The right-hand side FreeInterval to compare.
        ///
        /// @return \c true if the left FreeInterval is less than the right FreeInterval, \c false otherwise.
        template <typename U>
            requires std::unsigned_integral<U>
        friend constexpr DOCK_ALLOC_FORCE_INLINE bool operator<(FreeInterval const& left,
                                                                FreeInterval<U>& right) noexcept
        {
            return left.GetStart() < right.GetStart() || (left.GetStart() == right.GetStart() && left.GetLength() <
                right.GetLength());
        }

        /// @brief Abseil hash function for the FreeInterval class.
        ///
        /// This function computes a hash value for the FreeInterval by combining the hashes of its start and length.
        ///
        /// @tparam H The hash type used by Absl.
        ///
        /// @param h The initial hash value.
        /// @param interval The FreeInterval for which to compute the hash.
        ///
        /// @return The combined hash value.
        template <typename H>
            requires core::AbslHasher<H>
        friend constexpr DOCK_ALLOC_FORCE_INLINE H AbslHashValue(H h, const FreeInterval& interval) noexcept
        {
            return H::combine(std::move(h), interval.GetStart(), interval.GetLength());
        }

        /// @brief Formats the FreeInterval as a string using Absl's formatting.
        ///
        /// This function formats the FreeInterval as a string in the format "[start, end)".
        ///
        /// @tparam Sink The type of the sink to which the formatted string will be written.
        ///
        /// @param sink The sink to which the formatted string will be written.
        /// @param interval The FreeInterval to format.
        template <typename Sink>
            requires core::AbslStringifySink<Sink>
        friend DOCK_ALLOC_FORCE_INLINE void AbslStringify(Sink& sink, const FreeInterval& interval) noexcept
        {
            absl::Format(&sink, "[%v, %v)", interval.GetStart(), interval.End());
        }

    private:
        T start_;
        T length_;
    };
}

#endif
