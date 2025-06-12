// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_MODEL_VESSEL_H_
#define DOCK_ALLOC_MODEL_VESSEL_H_

#include <concepts>
#include <utility>
#include <vector>
#include "dockalloc/core/type_traits/concepts.h"
#include "dockalloc/core/algorithm/almost_equal.h"

namespace dockalloc::model
{
    /// @brief Represents a vessel with length, width, and draft.
    ///
    /// This class encapsulates the properties of a vessel, including its length, width, and draft.
    ///
    /// @tparam DistanceType The type used for the distance measurements of the vessel.
    template <typename DistanceType>
        requires core::IsArithmetic<DistanceType>
    class Vessel
    {
    public:
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
            requires core::IsArithmetic<OtherDistanceType>
        [[nodiscard]] friend constexpr bool operator==(const Vessel& left, const Vessel& right) noexcept
        {
            return core::AlmostEqual<DistanceType, OtherDistanceType>(left.GetLength(), right.GetLength()) &&
                core::AlmostEqual<DistanceType, OtherDistanceType>(left.GetWidth(), right.GetWidth()) &&
                core::AlmostEqual<DistanceType, OtherDistanceType>(left.GetDraft(), right.GetDraft());
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
            requires core::IsArithmetic<OtherDistanceType>
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
            return H::combine(std::move(h), vessel.GetLength(), vessel.GetWidth(), vessel.GetDraft());
        }

    private:
        DistanceType length_;
        DistanceType width_;
        DistanceType draft_;
    };

    /// @brief Represents a scenario for a vessel.
    ///
    /// This class encapsulates the scenario of a vessel, including its arrival time, planned departure time,
    /// processing time, and cost parameters.
    ///
    /// @tparam TimeType The type used for the time measurements of the vessel scenario.
    /// @tparam CostType The type used for the cost measurements of the vessel scenario.
    /// @tparam ProbabilityType The type used for the probability measurements of the vessel scenario.
    template <typename TimeType, typename CostType, typename ProbabilityType = double>
        requires std::unsigned_integral<TimeType> && core::IsArithmetic<CostType> && std::floating_point<
            ProbabilityType>
    class VesselScenario
    {
    public:
        /// @brief Constructs a \c VesselScenario with the given values.
        ///
        /// This constructor initializes a \c VesselScenario object with the specified arrival time,
        /// planned departure time, processing time, and cost parameters.
        ///
        /// @param probability The probability of the vessel scenario.
        /// @param arrival_time The time when the vessel arrives.
        /// @param planned_departure_time The planned time for the vessel to depart.
        /// @param processing_time The time required to process the vessel.
        /// @param cost_delay_per_unit The cost incurred for each unit of delay.
        /// @param cost_late_departure The cost incurred for a late departure.
        /// @param cost_berth_offset The cost incurred for berth offset.
        [[nodiscard]] constexpr explicit VesselScenario(const ProbabilityType probability, const TimeType arrival_time,
                                                        const TimeType planned_departure_time,
                                                        const TimeType processing_time,
                                                        const CostType cost_delay_per_unit,
                                                        const CostType cost_late_departure,
                                                        const CostType cost_berth_offset) noexcept
            : probability_(probability),
              arrival_time_(arrival_time),
              planned_departure_time_(planned_departure_time),
              processing_time_(processing_time),
              cost_delay_per_unit_(cost_delay_per_unit),
              cost_late_departure_(cost_late_departure),
              cost_berth_offset_(cost_berth_offset)
        {
        }

        /// @brief Gets the probability of the vessel scenario.
        ///
        /// This function returns the probability associated with the vessel scenario.
        ///
        /// @return The probability of the vessel scenario.
        [[nodiscard]] constexpr ProbabilityType GetProbability() const noexcept
        {
            return probability_;
        }

        /// @brief Gets the arrival time of the vessel.
        ///
        /// This function returns the time when the vessel arrives.
        ///
        /// @return The arrival time of the vessel.
        [[nodiscard]] constexpr TimeType GetArrivalTime() const
        {
            return arrival_time_;
        }

        /// @brief Gets the planned departure time of the vessel.
        ///
        /// This function returns the planned time for the vessel to depart.
        ///
        /// @return The planned departure time of the vessel.
        [[nodiscard]] constexpr TimeType GetPlannedDepartureTime() const
        {
            return planned_departure_time_;
        }

        /// @brief Gets the processing time of the vessel.
        ///
        /// This function returns the time required to process the vessel.
        ///
        /// @return The processing time of the vessel.
        [[nodiscard]] constexpr TimeType GetProcessingTime() const
        {
            return processing_time_;
        }

        /// @brief Gets the cost incurred for each unit of delay.
        ///
        /// This function returns the cost associated with each unit of delay for the vessel.
        ///
        /// @return The cost incurred for each unit of delay.
        [[nodiscard]] constexpr CostType GetCostDelayPerUnit() const
        {
            return cost_delay_per_unit_;
        }

        /// @brief Gets the cost incurred for a late departure.
        ///
        /// This function returns the cost associated with a late departure of the vessel.
        ///
        /// @return The cost incurred for a late departure.
        [[nodiscard]] constexpr CostType GetCostLateDeparture() const
        {
            return cost_late_departure_;
        }

        /// @brief Gets the cost incurred for berth offset.
        ///
        /// This function returns the cost associated with berth offset for the vessel.
        ///
        /// @return The cost incurred for berth offset.
        [[nodiscard]] constexpr CostType GetCostBerthOffset() const
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
            requires std::unsigned_integral<TimeType> && core::IsArithmetic<CostType> && std::floating_point<
                ProbabilityType>
        [[nodiscard]] friend constexpr bool operator==(const VesselScenario& left,
                                                       const VesselScenario<OtherTimeType, OtherCostType>& right)
            noexcept
        {
            return core::AlmostEqual<ProbabilityType, OtherTimeType>(left.GetProbability(), right.GetProbability()) &&
                core::AlmostEqual<TimeType, OtherTimeType>(left.GetArrivalTime(), right.GetArrivalTime()) &&
                core::AlmostEqual<TimeType, OtherTimeType>(left.GetPlannedDepartureTime(),
                                                           right.GetPlannedDepartureTime()) &&
                core::AlmostEqual<TimeType, OtherTimeType>(left.GetProcessingTime(), right.GetProcessingTime()) &&
                core::AlmostEqual<CostType, OtherCostType>(left.GetCostDelayPerUnit(), right.GetCostDelayPerUnit()) &&
                core::AlmostEqual<CostType, OtherCostType>(left.GetCostLateDeparture(), right.GetCostLateDeparture()) &&
                core::AlmostEqual<CostType, OtherCostType>(left.GetCostBerthOffset(), right.GetCostBerthOffset());
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
        ProbabilityType probability_;

        TimeType arrival_time_;
        TimeType planned_departure_time_;
        TimeType processing_time_;

        CostType cost_delay_per_unit_;
        CostType cost_late_departure_;
        CostType cost_berth_offset_;
    };

    template <typename TimeType, typename DistanceType, typename CostType, typename ProbabilityType = double>
        requires std::unsigned_integral<TimeType> && std::unsigned_integral<DistanceType> && core::IsArithmetic<
            CostType> && std::floating_point<ProbabilityType>
    class VesselScenarioBundle
    {
    public:
        /// @brief Constructs a \c VesselScenarioBundle with the given vessel, desired berth position, and scenarios.
        ///
        /// This constructor initializes a \c VesselScenarioBundle object with the specified vessel,
        /// desired berth position, and a collection of vessel scenarios.
        ///
        /// @tparam ScenariosContainer The type of the container holding the vessel scenarios.
        /// @param vessel The vessel associated with the scenarios.
        /// @param desired_berth_position The desired position for the vessel at the berth.
        /// @param scenarios The collection of vessel scenarios.
        template <typename ScenariosContainer>
            requires std::constructible_from<std::vector<VesselScenario<TimeType, CostType, ProbabilityType>>,
                                             ScenariosContainer&&>
        [[nodiscard]] constexpr VesselScenarioBundle(const Vessel<DistanceType>& vessel,
                                                     const DistanceType desired_berth_position,
                                                     ScenariosContainer&& scenarios) noexcept
            : vessel_(vessel),
              desired_berth_position_(desired_berth_position),
              scenarios_(std::forward<ScenariosContainer>(scenarios))
        {
        }

        /// @brief Gets the vessel associated with this scenario bundle.
        ///
        /// This function returns a reference to the vessel that is part of this scenario bundle.
        ///
        /// @return A reference to the vessel associated with this scenario bundle.
        [[nodiscard]] constexpr const Vessel<DistanceType>& GetVessel() noexcept
        {
            return vessel_;
        }

        /// @brief Gets the desired berth position for the vessel.
        ///
        /// This function returns the desired position for the vessel at the berth.
        ///
        /// @return The desired berth position for the vessel.
        [[nodiscard]] constexpr DistanceType GetDesiredBerthPosition() const noexcept
        {
            return desired_berth_position_;
        }

        /// @brief Gets the collection of vessel scenarios.
        ///
        /// This function returns a reference to the vector containing all vessel scenarios in this bundle.
        ///
        /// @return A reference to the vector of vessel scenarios.
        [[nodiscard]] constexpr const std::vector<VesselScenario<TimeType, CostType, ProbabilityType>>&
        GetScenarios() const
        {
            return scenarios_;
        }

        /// @brief Gets a specific vessel scenario by index.
        ///
        /// This function retrieves a vessel scenario at the specified index from the collection of scenarios.
        ///
        /// @param index The index of the scenario to retrieve.
        ///
        /// @pre 0 <= index < GetScenarioCount()
        ///
        /// @return A reference to the vessel scenario at the specified index.
        [[nodiscard]] constexpr const VesselScenario<TimeType, CostType, ProbabilityType>& GetScenario(
            const size_t index) const noexcept
        {
            DCHECK_LT(index, scenarios_.size());

            return scenarios_[index];
        }

        /// @brief Gets the number of scenarios in this bundle.
        ///
        /// This function returns the total count of vessel scenarios available in this bundle.
        ///
        /// @return The number of scenarios in this bundle.
        [[nodiscard]] constexpr size_t GetScenarioCount() const noexcept
        {
            return scenarios_.size();
        }

        /// @brief Access operator for vessel scenarios.
        ///
        /// This operator allows access to a vessel scenario at the specified index using the subscript operator.
        ///
        /// @param index The index of the scenario to access.
        ///
        /// @pre 0 <= index < GetScenarioCount()
        ///
        /// @return A reference to the vessel scenario at the specified index.
        [[nodiscard]] constexpr const VesselScenario<TimeType, CostType, ProbabilityType>& operator[](
            const size_t index) const noexcept
        {
            return GetScenario(index);
        }

    private:
        Vessel<DistanceType> vessel_;
        DistanceType desired_berth_position_;
        std::vector<VesselScenario<TimeType, CostType, ProbabilityType>> scenarios_;
    };
}

#endif
