// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_MODEL_VESSEL_H_
#define DOCK_ALLOC_MODEL_VESSEL_H_

#include <concepts>
#include <utility>
#include "dockalloc/model/types.h"

namespace dockalloc::model
{
    /// @brief Represents a vessel with length, width, and draft.
    ///
    /// This class encapsulates the properties of a vessel, including its length, width, and draft.
    ///
    /// @tparam DistanceType The type used for the distance measurements of the vessel.
    template <typename DistanceType>
        requires std::unsigned_integral<DistanceType>
    class Vessel
    {
    public:
        /// @brief Copy constructor.
        ///
        /// This constructor creates a copy of another Vessel object.
        ///
        /// @param other The Vessel object to copy.
        constexpr Vessel(const Vessel& other) noexcept = default;

        /// @brief Move constructor.
        ///
        /// This constructor transfers ownership of resources from another Vessel object to this one.
        ///
        /// @param other The Vessel object to move.
        constexpr Vessel(Vessel&& other) noexcept = default;

        /// @brief Constructs a Vessel with the given values.
        ///
        /// This constructor initializes a Vessel object with the specified length, width, and draft.
        ///
        /// @param length The length of the vessel.
        /// @param width The width of the vessel.
        /// @param draft The draft of the vessel.
        [[nodiscard]] constexpr explicit Vessel(const DistanceType length, const DistanceType width,
                                                const DistanceType draft) noexcept
            : length_(length),
              width_(width),
              draft_(draft)
        {
        }

        /// @brief Gets the length of the vessel.
        ///
        /// This function returns the length of the vessel.
        ///
        /// @return The length of the vessel.
        [[nodiscard]] constexpr DistanceType GetLength() const noexcept
        {
            return length_;
        }

        /// @brief Gets the width of the vessel.
        ///
        /// This function returns the width of the vessel.
        ///
        /// @return The width of the vessel.
        [[nodiscard]] constexpr DistanceType GetWidth() const noexcept
        {
            return width_;
        }

        /// @brief Gets the draft of the vessel.
        ///
        /// This function returns the draft of the vessel.
        ///
        /// @return The draft of the vessel.
        [[nodiscard]] constexpr DistanceType GetDraft() const noexcept
        {
            return draft_;
        }

        /// @brief Compares two Vessel objects for equality.
        ///
        /// This function checks if two Vessel objects have the same length, width, and draft.
        ///
        /// @tparam OtherDistanceType The type of the other Vessel's distance measurements.
        /// @param left The left-hand side Vessel object.
        /// @param right The right-hand side Vessel object.
        ///
        /// @return \c true if the vessels are equal, \c false otherwise.
        template <typename OtherDistanceType>
            requires std::unsigned_integral<OtherDistanceType>
        [[nodiscard]] friend constexpr bool operator==(const Vessel& left, const Vessel& right) noexcept
        {
            return left.GetLength() == right.GetLength() && left.GetWidth() == right.GetWidth() && left.GetDraft() ==
                right.GetDraft();
        }

        /// @brief Compares two Vessel objects for inequality.
        ///
        /// This function checks if two Vessel objects do not have the same length, width, and draft.
        ///
        /// @tparam OtherDistanceType The type of the other Vessel's distance measurements.
        /// @param left The left-hand side Vessel object.
        /// @param right The right-hand side Vessel object.
        ///
        /// @return \c true if the vessels are not equal, \c false otherwise.
        template <typename OtherDistanceType>
            requires std::unsigned_integral<OtherDistanceType>
        [[nodiscard]] friend constexpr bool operator!=(const Vessel& left, const Vessel& right) noexcept
        {
            return !(left == right);
        }

        /// @brief Hash function for \c absl::flat_hash_* containers.
        ///
        /// This function computes a hash value for the Vessel object, combining its length, width, and draft.
        ///
        /// @tparam H The hash type, typically \c absl::Hash or similar.
        /// @param h The initial hash state.
        /// @param vessel The Vessel object to hash.
        ///
        /// @return The updated hash state after combining the vessel's properties.
        template <typename H>
        friend constexpr H AbslHashValue(H h, const Vessel& vessel) noexcept
        {
            return H::combine(std::move(h), vessel.length_, vessel.width_, vessel.draft_);
        }

        // Delete copy and move assignment operators to prevent copying or moving and make the class immutable.

        constexpr Vessel& operator=(const Vessel&) = delete;
        constexpr Vessel& operator=(Vessel&&) = delete;

    private:
        DistanceType length_;
        DistanceType width_;
        DistanceType draft_;
    };

    /// @brief Represents a vessel plan with time, distance, and cost parameters.
    ///
    /// This class encapsulates the planning parameters for a vessel, including its nominal arrival time,
    /// nominal handling time, desired departure time, desired berth position,
    /// cost per unit delay, cost for late departure, and cost for berth offset.
    ///
    /// @tparam TimeType The type used for the time measurements of the vessel plan.
    /// @tparam DistanceType The type used for the distance measurements of the vessel plan.
    /// @tparam CostType The type used for the cost measurements of the vessel plan.
    template <typename TimeType, typename DistanceType, typename CostType>
        requires std::unsigned_integral<TimeType> && std::unsigned_integral<DistanceType> && std::is_arithmetic_v<
            CostType>
    class VesselPlan
    {
    public:
        /// @brief Copy constructor.
        ///
        /// This constructor creates a copy of another \c VesselPlan object.
        ///
        /// @param other The \c VesselPlan object to copy.
        constexpr VesselPlan(const VesselPlan& other) noexcept = default;

        /// @brief Move constructor.
        ///
        /// This constructor transfers ownership of resources from another \c VesselPlan object to this one.
        ///
        /// @param other The \c VesselPlan object to move.
        constexpr VesselPlan(VesselPlan&& other) noexcept = default;

        /// @brief Constructs a \c VesselPlan with the given values.
        ///
        /// This constructor initializes a \c VesselPlan object with the specified nominal arrival time,
        /// nominal handling time, desired departure time, desired berth position,
        /// cost per unit delay, cost for late departure, and cost for berth offset.
        ///
        /// @param nominal_arrival The nominal arrival time of the vessel.
        /// @param nominal_handling The nominal handling time of the vessel.
        /// @param desired_departure The desired departure time of the vessel.
        /// @param desired_berth_position The desired berth position of the vessel.
        /// @param cost_delay_per_unit The cost per unit delay for the vessel.
        /// @param cost_late_departure The cost for late departure of the vessel.
        /// @param cost_berth_offset The cost for berth offset of the vessel.
        [[nodiscard]] constexpr explicit VesselPlan(const TimeType nominal_arrival, const TimeType nominal_handling,
                                                    const TimeType desired_departure,
                                                    const DistanceType desired_berth_position,
                                                    const CostType cost_delay_per_unit,
                                                    const CostType cost_late_departure,
                                                    const CostType cost_berth_offset) noexcept
            : nominal_arrival_(nominal_arrival),
              nominal_handling_(nominal_handling),
              desired_departure_(desired_departure),
              desired_berth_position_(desired_berth_position),
              cost_delay_per_unit_(cost_delay_per_unit),
              cost_late_departure_(cost_late_departure),
              cost_berth_offset_(cost_berth_offset)
        {
        }

        /// @brief Gets the nominal arrival time of the vessel.
        ///
        /// This function returns the nominal arrival time of the vessel.
        ///
        /// @return The nominal arrival time of the vessel.
        [[nodiscard]] constexpr TimeType GetNominalArrival() const noexcept
        {
            return nominal_arrival_;
        }

        /// @brief Gets the nominal handling time of the vessel.
        ///
        /// This function returns the nominal handling time of the vessel.
        ///
        /// @return The nominal handling time of the vessel.
        [[nodiscard]] constexpr TimeType GetNominalHandling() const noexcept
        {
            return nominal_handling_;
        }

        /// @brief Gets the desired departure time of the vessel.
        ///
        /// This function returns the desired departure time of the vessel.
        ///
        /// @return The desired departure time of the vessel.
        [[nodiscard]] constexpr TimeType GetDesiredDeparture() const noexcept
        {
            return desired_departure_;
        }

        /// @brief Gets the desired berth position of the vessel.
        ///
        /// This function returns the desired berth position of the vessel.
        ///
        /// @return The desired berth position of the vessel.
        [[nodiscard]] constexpr DistanceType GetDesiredBerthPosition() const noexcept
        {
            return desired_berth_position_;
        }

        /// @brief Gets the cost per unit delay for the vessel.
        ///
        /// This function returns the cost per unit delay for the vessel.
        ///
        /// @return The cost per unit delay for the vessel.
        [[nodiscard]] constexpr CostType GetCostDelayPerUnit() const noexcept
        {
            return cost_delay_per_unit_;
        }

        /// @brief Gets the cost for late departure of the vessel.
        ///
        /// This function returns the cost for late departure of the vessel.
        ///
        /// @return The cost for late departure of the vessel.
        [[nodiscard]] constexpr CostType GetCostLateDeparture() const noexcept
        {
            return cost_late_departure_;
        }

        /// @brief Gets the cost for berth offset of the vessel.
        ///
        /// This function returns the cost for berth offset of the vessel.
        ///
        /// @return The cost for berth offset of the vessel.
        [[nodiscard]] constexpr CostType GetCostBerthOffset() const noexcept
        {
            return cost_berth_offset_;
        }

        /// @brief Compares two VesselPlan objects for equality.
        ///
        /// This function checks if two VesselPlan objects have the same nominal arrival time,
        /// nominal handling time, desired departure time, desired berth position,
        /// cost per unit delay, cost for late departure, and cost for berth offset.
        ///
        /// @tparam OtherTimeType The type of the other VesselPlan's time measurements.
        /// @tparam OtherDistanceType The type of the other VesselPlan's distance measurements.
        /// @tparam OtherCostType The type of the other VesselPlan's cost measurements.
        /// @param left The left-hand side VesselPlan object.
        /// @param right The right-hand side VesselPlan object.
        ///
        /// @return \c true if the VesselPlan objects are equal, \c false otherwise.
        template <typename OtherTimeType, typename OtherDistanceType, typename OtherCostType>
            requires std::unsigned_integral<OtherTimeType> && std::unsigned_integral<OtherDistanceType> &&
            std::is_arithmetic_v<OtherCostType>
        [[nodiscard]] friend constexpr bool operator==(const VesselPlan& left,
                                                       const VesselPlan<OtherTimeType, OtherDistanceType, OtherCostType>
                                                       &
                                                       right) noexcept
        {
            return left.GetNominalArrival() == right.GetNominalArrival()
                && left.GetNominalHandling() == right.GetNominalHandling()
                && left.GetDesiredDeparture() == right.GetDesiredDeparture()
                && left.GetDesiredBerthPosition() == right.GetDesiredBerthPosition()
                && left.GetCostDelayPerUnit() == right.GetCostDelayPerUnit()
                && left.GetCostLateDeparture() == right.GetCostLateDeparture()
                && left.GetCostBerthOffset() == right.GetCostBerthOffset();
        }

        /// @brief Compares two VesselPlan objects for inequality.
        ///
        /// This function checks if two VesselPlan objects do not have the same nominal arrival time,
        /// nominal handling time, desired departure time, desired berth position,
        /// cost per unit delay, cost for late departure, and cost for berth offset.
        ///
        /// @tparam OtherTimeType The type of the other VesselPlan's time measurements.
        /// @tparam OtherDistanceType The type of the other VesselPlan's distance measurements.
        /// @tparam OtherCostType The type of the other VesselPlan's cost measurements.
        /// @param left The left-hand side VesselPlan object.
        /// @param right The right-hand side VesselPlan object.
        ///
        /// @return \c true if the VesselPlan objects are not equal, \c false otherwise.
        template <typename OtherTimeType, typename OtherDistanceType, typename OtherCostType>
            requires std::unsigned_integral<OtherTimeType> && std::unsigned_integral<OtherDistanceType> &&
            std::is_arithmetic_v<OtherCostType>
        [[nodiscard]] friend constexpr bool operator!=(const VesselPlan& left,
                                                       const VesselPlan<OtherTimeType, OtherDistanceType, OtherCostType>
                                                       &
                                                       right) noexcept
        {
            return !(left == right);
        }

        /// @brief Hash function for \c absl::flat_hash_* containers.
        ///
        /// This function computes a hash value for the VesselPlan object, combining its nominal arrival time,
        /// nominal handling time, desired departure time, desired berth position,
        /// cost per unit delay, cost for late departure, and cost for berth offset.
        ///
        /// @tparam H The hash type, typically \c absl::Hash or similar.
        /// @param h The initial hash state.
        /// @param vessel_plan The VesselPlan object to hash.
        ///
        /// @return The updated hash state after combining the VesselPlan's properties.
        template <typename H>
        friend constexpr H AbslHashValue(H h, const VesselPlan& vessel_plan) noexcept
        {
            return H::combine(std::move(h), vessel_plan.nominal_arrival_, vessel_plan.nominal_handling_,
                              vessel_plan.desired_departure_, vessel_plan.desired_berth_position_,
                              vessel_plan.cost_delay_per_unit_, vessel_plan.cost_late_departure_,
                              vessel_plan.cost_berth_offset_);
        }

        // Delete copy and move assignment operators to prevent copying or moving and make the class immutable.

        constexpr VesselPlan& operator=(const VesselPlan&) noexcept = delete;
        constexpr VesselPlan& operator=(VesselPlan&&) noexcept = delete;

    private:
        TimeType nominal_arrival_;
        TimeType nominal_handling_;
        TimeType desired_departure_;

        DistanceType desired_berth_position_;

        CostType cost_delay_per_unit_;
        CostType cost_late_departure_;
        CostType cost_berth_offset_;
    };
}

#endif
