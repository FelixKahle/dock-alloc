// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_MODEL_SHIP_H_
#define DOCK_ALLOC_MODEL_SHIP_H_

#include <cstdint>
#include <algorithm>
#include "dockalloc/model/types.h"

namespace dockalloc::model
{
    /// @brief A class representing a ship in the dock allocation model.
    ///
    /// This class encapsulates the properties of a ship, including its unique identifier,
    /// length, draft, arrival time, and importance.
    ///
    /// @tparam IdType The type of the ship's unique identifier. Defaults to \c Id.
    /// @tparam LengthType The type used for the ship's length and draft. Defaults to \c uint32_t.
    /// @tparam TimeType The type used for the ship's arrival time. Defaults to \c uint32_t.
    /// @tparam ImportanceType The type used for the ship's importance. Defaults to \c uint8_t.
    template <typename IdType = Id, typename LengthType = uint32_t, typename TimeType = uint32_t, typename
              ImportanceType = uint8_t>
    class Ship
    {
    public:
        /// @brief Copy constructor.
        ///
        /// This constructor creates a new \c Ship object as a copy of another \c Ship.
        ///
        /// @param other The \c Ship object to copy.
        Ship(Ship& other) noexcept = default;

        /// @brief Move constructor.
        ///
        /// This constructor creates a new \c Ship object by moving another \c Ship.
        ///
        /// @param other The \c Ship object to move.
        Ship(Ship&& other) noexcept = default;

        /// @brief Constructor.
        ///
        /// This constructor initializes a \c Ship object with the specified properties.
        ///
        /// @param id The unique identifier of the ship.
        /// @param length The length of the ship.
        /// @param draft The draft of the ship.
        /// @param time The arrival time of the ship.
        /// @param importance The importance of the ship, defaults to \c 1.
        ///
        /// @pre importance > 0
        explicit Ship(IdType id, LengthType length, LengthType draft, TimeType time,
                      ImportanceType importance = 1) noexcept
            : id_(id), length_(length), draft_(draft), arrival_time_(time),
              importance_(std::max<ImportanceType>(1, importance))
        {
        }

        /// @brief Gets the unique identifier of the ship.
        ///
        /// This function returns the unique identifier of the ship.
        ///
        /// @return The unique identifier of the ship.
        [[nodiscard]] IdType GetId() const noexcept
        {
            return id_;
        }

        /// @brief Gets the length of the ship.
        ///
        /// This function returns the length of the ship.
        ///
        /// @return The length of the ship.
        [[nodiscard]] LengthType GetLength() const noexcept
        {
            return length_;
        }

        /// @brief Gets the draft of the ship.
        ///
        /// This function returns the draft of the ship.
        ///
        /// @return The draft of the ship.
        [[nodiscard]] LengthType GetDraft() const noexcept
        {
            return draft_;
        }

        /// @brief Gets the arrival time of the ship.
        ///
        /// This function returns the arrival time of the ship.
        ///
        /// @return The arrival time of the ship.
        [[nodiscard]] TimeType GetArrivalTime() const noexcept
        {
            return arrival_time_;
        }

        /// @brief Gets the importance of the ship.
        ///
        /// This function returns the importance of the ship.
        ///
        /// @return The importance of the ship.
        [[nodiscard]] ImportanceType GetImportance() const noexcept
        {
            return importance_;
        }

        // Deleted copy and move assignment operators to prevent copying

        Ship& operator=(const Ship& other) noexcept = default;
        Ship& operator=(Ship&& other) noexcept = default;

    private:
        IdType id_;
        LengthType length_;
        LengthType draft_;
        TimeType arrival_time_;
        ImportanceType importance_ = 0;
    };
}

#endif
