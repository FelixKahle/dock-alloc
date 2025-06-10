// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_MODEL_VESSEL_H_
#define DOCK_ALLOC_MODEL_VESSEL_H_

#include <concepts>
#include "dockalloc/model/types.h"

namespace dockalloc::model
{
    /// @brief Represents a vessel in the dock allocation model.
    ///
    /// This class encapsulates the properties of a vessel, including its dimensions, desired berth position,
    /// arrival and departure times, and associated costs. It provides methods to access these properties.
    ///
    /// @tparam IdType The type of the unique identifier for the vessel.
    /// @tparam DistanceType The type of the distance measurements for the vessel's dimensions and berth position.
    /// @tparam TimeType The type of the time measurements for the vessel's arrival, handling time, and departure.
    /// @tparam CostType The type of the cost measurements for delays, late departures, and berth offsets.
    template <typename IdType = Id, typename DistanceType = uint32_t, typename TimeType = uint32_t, typename CostType =
              uint32_t>
        requires std::unsigned_integral<IdType> && std::is_arithmetic_v<DistanceType> && std::unsigned_integral<
            TimeType> && std::is_arithmetic_v<CostType>
    class Vessel
    {
    public:
        /// @brief Copy constructor.
        ///
        /// Constructs a new \c Vessel object as a copy of another \c Vessel object.
        ///
        /// @param other The \c Vessel object to copy.
        Vessel(Vessel& other) noexcept = default;

        /// @brief Move constructor.
        ///
        /// Constructs a new \c Vessel object by transferring ownership of resources from another \c Vessel object.
        ///
        /// @param other The \c Vessel object to move.
        Vessel(Vessel&& other) noexcept = default;

        /// @brief Constructor with parameters.
        ///
        /// Constructs a new \c Vessel object with the specified parameters.
        ///
        /// @param id The unique identifier for the vessel.
        /// @param length The length of the vessel.
        /// @param width The width of the vessel.
        /// @param height The height of the vessel.
        /// @param draft The draft of the vessel.
        /// @param desired_berth_position The desired berth position for the vessel.
        /// @param nominal_arrival The nominal arrival time of the vessel.
        /// @param nominal_handling_time The nominal handling time for the vessel.
        /// @param desired_departure The desired departure time of the vessel.
        /// @param cost_delay_per_unit The cost incurred per unit of delay.
        /// @param cost_late_departure The cost incurred for a late departure.
        /// @param cost_berth_offset The cost incurred for a berth offset.
        [[nodiscard]] explicit Vessel(const IdType id, const DistanceType length, const DistanceType width,
                                      const DistanceType height, const DistanceType draft,
                                      const DistanceType desired_berth_position,
                                      const TimeType nominal_arrival, const TimeType nominal_handling_time,
                                      const TimeType desired_departure,
                                      const CostType cost_delay_per_unit, const CostType cost_late_departure,
                                      const CostType cost_berth_offset)
            : id_(id),
              length_(length),
              width_(width),
              height_(height),
              draft_(draft),
              desired_berth_position_(desired_berth_position),
              nominal_arrival_(nominal_arrival),
              nominal_handling_time_(nominal_handling_time),
              desired_departure_(desired_departure),
              cost_delay_per_unit_(cost_delay_per_unit),
              cost_late_departure(cost_late_departure),
              cost_berth_offset_(cost_berth_offset)
        {
        }

        /// @brief Gets the unique identifier of the vessel.
        ///
        /// This function returns the unique identifier of the vessel.
        ///
        /// @return The unique identifier of the vessel.
        [[nodiscard]] IdType GetId() const noexcept
        {
            return id_;
        }

        /// @brief Gets the length of the vessel.
        ///
        /// This function returns the length of the vessel.
        ///
        /// @return The length of the vessel.
        [[nodiscard]] DistanceType GetLength() const noexcept
        {
            return length_;
        }

        /// @brief Gets the width of the vessel.
        ///
        /// This function returns the width of the vessel.
        ///
        /// @return The width of the vessel.
        [[nodiscard]] DistanceType GetWidth() const noexcept
        {
            return width_;
        }

        /// @brief Gets the height of the vessel.
        ///
        /// This function returns the height of the vessel.
        ///
        /// @return The height of the vessel.
        [[nodiscard]] DistanceType GetHeight() const noexcept
        {
            return height_;
        }

        /// @brief Gets the draft of the vessel.
        ///
        /// This function returns the draft of the vessel.
        ///
        /// @return The draft of the vessel.
        [[nodiscard]] DistanceType GetDraft() const noexcept
        {
            return draft_;
        }

        /// @brief Gets the desired berth position of the vessel.
        ///
        /// This function returns the desired berth position of the vessel.
        ///
        /// @return The desired berth position of the vessel.
        [[nodiscard]] DistanceType GetDesiredBerthPosition() const noexcept
        {
            return desired_berth_position_;
        }

        /// @brief Gets the nominal arrival time of the vessel.
        ///
        /// This function returns the nominal arrival time of the vessel.
        ///
        /// @return The nominal arrival time of the vessel.
        [[nodiscard]] TimeType GetNominalArrival() const noexcept
        {
            return nominal_arrival_;
        }

        /// @brief Gets the nominal handling time of the vessel.
        ///
        /// This function returns the nominal handling time of the vessel.
        ///
        /// @return The nominal handling time of the vessel.
        [[nodiscard]] TimeType GetNominalHandlingTime() const noexcept
        {
            return nominal_handling_time_;
        }

        /// @brief Gets the desired departure time of the vessel.
        ///
        /// This function returns the desired departure time of the vessel.
        ///
        /// @return The desired departure time of the vessel.
        [[nodiscard]] TimeType GetDesiredDeparture() const noexcept
        {
            return desired_departure_;
        }

        /// @brief Gets the cost incurred per unit of delay.
        ///
        /// This function returns the cost incurred per unit of delay for the vessel.
        ///
        /// @return The cost incurred per unit of delay.
        [[nodiscard]] CostType GetCostDelayPerUnit() const noexcept
        {
            return cost_delay_per_unit_;
        }

        /// @brief Gets the cost incurred for a late departure.
        ///
        /// This function returns the cost incurred for a late departure of the vessel.
        ///
        /// @return The cost incurred for a late departure.
        [[nodiscard]] CostType GetCostLateDeparture() const noexcept
        {
            return cost_late_departure;
        }

        /// @brief Gets the cost incurred for a berth offset.
        ///
        /// This function returns the cost incurred for a berth offset of the vessel.
        ///
        /// @return The cost incurred for a berth offset.
        [[nodiscard]] CostType GetCostBerthOffset() const noexcept
        {
            return cost_berth_offset_;
        }

        // Delete copy and move assignment operators

        Vessel& operator=(const Vessel&) noexcept = delete;
        Vessel& operator=(Vessel&&) noexcept = delete;

    private:
        IdType id_;

        DistanceType length_;
        DistanceType width_;
        DistanceType height_;
        DistanceType draft_;
        DistanceType desired_berth_position_;

        TimeType nominal_arrival_;
        TimeType nominal_handling_time_;
        TimeType desired_departure_;

        CostType cost_delay_per_unit_;
        CostType cost_late_departure;
        CostType cost_berth_offset_;
    };
}

#endif
