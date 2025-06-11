// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_MODEL_VESSEL_H_
#define DOCK_ALLOC_MODEL_VESSEL_H_

#include <concepts>
#include <utility>
#include "dockalloc/core/type_traits/concepts.h"
#include "dockalloc/core/miscellaneous/core_defines.h"
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
        /// This constructor creates a new Vessel object by moving another.
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

    private:
        DistanceType length_;
        DistanceType width_;
        DistanceType draft_;
    };

    template <typename TimeType, typename CostType>
        requires std::unsigned_integral<TimeType> && core::IsArithmetic<CostType>
    class VesselScenario
    {
    public:
        /// @brief Copy constructor.
        ///
        /// This constructor creates a copy of another \c VesselScenario object.
        ///
        /// @param other The \c VesselScenario object to copy.
        constexpr VesselScenario(const VesselScenario& other) noexcept = default;

        /// @brief Move constructor.
        ///
        /// This constructor creates a new \c VesselScenario object by moving another.
        ///
        /// @param other The \c VesselScenario object to move.
        constexpr VesselScenario(const VesselScenario&& other) noexcept = default;

        /// @brief Constructs a \c VesselScenario with the given values.
        ///
        /// This constructor initializes a \c VesselScenario object with the specified arrival time,
        /// planned departure time, processing time, and cost parameters.
        ///
        /// @param arrival_time The time when the vessel arrives.
        /// @param planned_departure_time The planned time for the vessel to depart.
        /// @param processing_time The time required to process the vessel.
        /// @param cost_delay_per_unit The cost incurred for each unit of delay.
        /// @param cost_late_departure The cost incurred for a late departure.
        /// @param cost_berth_offset The cost incurred for berth offset.
        [[nodiscard]] constexpr explicit VesselScenario(const TimeType arrival_time,
                                                        const TimeType planned_departure_time,
                                                        const TimeType processing_time,
                                                        const CostType cost_delay_per_unit,
                                                        const CostType cost_late_departure,
                                                        const CostType cost_berth_offset) noexcept
            : arrival_time_(arrival_time),
              planned_departure_time_(planned_departure_time),
              processing_time_(processing_time),
              cost_delay_per_unit_(cost_delay_per_unit),
              cost_late_departure_(cost_late_departure),
              cost_berth_offset_(cost_berth_offset)
        {
        }

        /// @brief Gets the arrival time of the vessel.
        ///
        /// This function returns the time when the vessel arrives.
        ///
        /// @return The arrival time of the vessel.
        [[nodiscard]] TimeType GetArrivalTime() const
        {
            return arrival_time_;
        }

        /// @brief Gets the planned departure time of the vessel.
        ///
        /// This function returns the planned time for the vessel to depart.
        ///
        /// @return The planned departure time of the vessel.
        [[nodiscard]] TimeType GetPlannedDepartureTime() const
        {
            return planned_departure_time_;
        }

        /// @brief Gets the processing time of the vessel.
        ///
        /// This function returns the time required to process the vessel.
        ///
        /// @return The processing time of the vessel.
        [[nodiscard]] TimeType GetProcessingTime() const
        {
            return processing_time_;
        }

        /// @brief Gets the cost incurred for each unit of delay.
        ///
        /// This function returns the cost associated with each unit of delay for the vessel.
        ///
        /// @return The cost incurred for each unit of delay.
        [[nodiscard]] CostType GetCostDelayPerUnit() const
        {
            return cost_delay_per_unit_;
        }

        /// @brief Gets the cost incurred for a late departure.
        ///
        /// This function returns the cost associated with a late departure of the vessel.
        ///
        /// @return The cost incurred for a late departure.
        [[nodiscard]] CostType GetCostLateDeparture() const
        {
            return cost_late_departure_;
        }

        /// @brief Gets the cost incurred for berth offset.
        ///
        /// This function returns the cost associated with berth offset for the vessel.
        ///
        /// @return The cost incurred for berth offset.
        [[nodiscard]] CostType GetCostBerthOffset() const
        {
            return cost_berth_offset_;
        }

        /// @brief Compares two \c VesselScenario objects for equality.
        ///
        /// This function checks if two \c VesselScenario objects have the same arrival time,
        /// planned departure time, processing time, and cost parameters.
        ///
        /// @tparam OtherTimeType The type of the other \c VesselScenario's time measurements.
        /// @tparam OtherCostType The type of the other \c VesselScenario's cost measurements.
        /// @param left The left-hand side \c VesselScenario object.
        /// @param right The right-hand side \c VesselScenario object.
        ///
        /// @return \c true if the scenarios are equal, \c false otherwise.
        template <typename OtherTimeType, typename OtherCostType>
            requires std::unsigned_integral<OtherTimeType> && core::IsArithmetic<OtherCostType>
        [[nodiscard]] friend constexpr bool operator==(const VesselScenario& left,
                                                       const VesselScenario<OtherTimeType, OtherCostType>& right)
            noexcept
        {
            return left.GetArrivalTime() == right.GetArrivalTime() &&
                left.GetPlannedDepartureTime() == right.GetPlannedDepartureTime() &&
                left.GetProcessingTime() == right.GetProcessingTime() &&
                left.GetCostDelayPerUnit() == right.GetCostDelayPerUnit() &&
                left.GetCostLateDeparture() == right.GetCostLateDeparture() &&
                left.GetCostBerthOffset() == right.GetCostBerthOffset();
        }

        /// @brief Compares two \c VesselScenario objects for inequality.
        ///
        /// This function checks if two \c VesselScenario objects do not have the same arrival time,
        /// planned departure time, processing time, and cost parameters.
        ///
        /// @tparam OtherTimeType The type of the other \c VesselScenario's time measurements.
        /// @tparam OtherCostType The type of the other \c VesselScenario's cost measurements.
        /// @param left The left-hand side \c VesselScenario object.
        /// @param right The right-hand side \c VesselScenario object.
        ///
        /// @return \c true if the scenarios are not equal, \c false otherwise.
        template <typename OtherTimeType, typename OtherCostType>
            requires std::unsigned_integral<OtherTimeType> && core::IsArithmetic<OtherCostType>
        [[nodiscard]] friend constexpr bool operator!=(const VesselScenario& left,
                                                       const VesselScenario<OtherTimeType, OtherCostType>& right)
            noexcept
        {
            return !(left == right);
        }

        /// @brief Hash function for \c absl::flat_hash_* containers.
        ///
        /// This function computes a hash value for the \c VesselScenario object, combining its arrival time,
        /// planned departure time, processing time, and cost parameters.
        ///
        /// @tparam H The hash type, typically \c absl::Hash or similar.
        /// @param h The initial hash state.
        /// @param scenario The \c VesselScenario object to hash.
        ///
        /// @return The updated hash state after combining the scenario's properties.
        template <typename H>
        friend constexpr H AbslHashValue(H h, const VesselScenario& scenario) noexcept
        {
            return H::combine(std::move(h), scenario.arrival_time_, scenario.planned_departure_time_,
                              scenario.processing_time_, scenario.cost_delay_per_unit_,
                              scenario.cost_late_departure_, scenario.cost_berth_offset_);
        }

    private:
        TimeType arrival_time_;
        TimeType planned_departure_time_;
        TimeType processing_time_;

        CostType cost_delay_per_unit_;
        CostType cost_late_departure_;
        CostType cost_berth_offset_;
    };
}

#endif
