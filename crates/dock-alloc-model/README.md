# dock-alloc-model

A foundational Rust crate providing validated, type-safe data structures for the **Berth Allocation Problem (BAP)**.

`dock-alloc-model` defines the core entities of a berth allocation scenario: `Request`s for quay space, the `Problem` to be solved, and the final `Solution`. It is designed to be a solver-agnostic layer, allowing developers to focus on building optimization algorithms (e.g., heuristics, MILP, CP) without worrying about the integrity and correctness of the underlying data model.

## Key Features

-   **Type-Safe Primitives**: Uses strong types from the `dock-alloc-core` crate like `RequestId`, `SpaceLength`, and `TimePoint` to prevent common bugs with primitive types.
-   **Comprehensive `Request` Model**: Captures a wide range of real-world constraints, including vessel length, processing duration, feasible time/space windows, target positions, and costs for delay, deviation, and dropping.
-   **Abstract by Design**: A `Request` is not just for ships! The model is flexible enough to represent any space-time constraint. For example, it can model a **maintenance window** by creating a request with zero cost and a hard feasibility constraint, which is then `PreAssigned` in the problem.
-   **Rigorous Validation**: The `Problem` and `Solution` constructors perform exhaustive checks to ensure logical consistency. This includes detecting overlaps between pre-assignments, assignments outside quay boundaries, violations of feasibility windows, and more. This saves solver developers from writing complex and error-prone validation logic.
-   **Solver-Agnostic**: The model makes no assumptions about the optimization technique used. It serves as a pure data layer for any kind of solver.
-   **Generic & Flexible**: Uses generic types for time (`TimeType`) and cost (`CostType`), allowing for the use of `i64`, floating-point types, or custom high-precision numeric types.

## Core Components

The crate revolves around a few central structs:

1.  **`Request<TimeType, CostType>`**: Represents a single requirement for a space-time slot. It holds all the physical, temporal, and cost-related parameters for one booking.

2.  **`Problem<TimeType, CostType>`**: Defines a complete, validated scenario. It contains:
    -   A set of all `Request`s.
    -   A set of `ProblemEntry`s, which specify whether a request is `Unassigned` (needs scheduling) or `PreAssigned` (already fixed in place).
    -   The total `quay_length`.

3.  **`Solution<TimeType, CostType>`**: Represents a complete and validated solution to a `Problem`. It contains:
    -   A `Decision` for each request (`Assign` or `Drop`).
    -   `SolutionStats` with aggregated metrics like total cost, total waiting time, and number of dropped requests.

## Usage Example

Here's how to define a problem with two requests—one to be scheduled and one representing a fixed maintenance window—and then create a valid solution for it.

```rust
use std::collections::HashSet;
use dock_alloc_core::domain::{
    Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use dock_alloc_model::{
    Problem, ProblemEntry, Request, RequestId, Solution, Decision, Assignment
};

// --- 1. Define the Requests ---

// A standard vessel request that needs to be scheduled.
let vessel_request = Request::new(
    RequestId::new(1),
    SpaceLength::new(150),      // 150m long
    TimeDelta::new(3600 * 4),   // needs 4 hours
    SpacePosition::new(200),    // prefers position 200m
    Cost::new(50),              // cost per second of delay
    Cost::new(10),              // cost per meter of deviation
    TimeInterval::new(TimePoint::new(0), TimePoint::new(3600 * 24)),
    SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(800)),
    None, // This request cannot be dropped
).unwrap();

// A request representing a pre-scheduled maintenance block.
// It has no costs and a very specific time/space window.
let maintenance_request = Request::new(
    RequestId::new(2),
    SpaceLength::new(100),      // Maintenance area is 100m
    TimeDelta::new(3600 * 2),   // Lasts 2 hours
    SpacePosition::new(400),    // Target position (not relevant due to pre-assignment)
    Cost::new(0),               // No cost
    Cost::new(0),               // No cost
    TimeInterval::new(TimePoint::new(3600 * 6), TimePoint::new(3600 * 8)),
    SpaceInterval::new(SpacePosition::new(400), SpacePosition::new(500)),
    None,
).unwrap();


// --- 2. Create the Problem ---

let requests = HashSet::from([vessel_request, maintenance_request]);

let entries = HashSet::from([
    // The vessel is unassigned and needs a schedule.
    ProblemEntry::Unassigned(RequestId::new(1)),
    // The maintenance is pre-assigned to a fixed time and place.
    ProblemEntry::PreAssigned(Assignment::new(
        RequestId::new(2),
        SpacePosition::new(400),
        TimePoint::new(3600 * 6), // Starts exactly 6 hours in
    )),
]);

let quay_length = SpaceLength::new(1000);
let problem = Problem::new(requests, entries, quay_length).unwrap();


// --- 3. Define a Solution from a Solver's Output ---

// Assume our solver decides to place the vessel right at the start of the quay
// immediately at its arrival time.
let solver_decisions = vec![
    Decision::Assign(Assignment::new(
        RequestId::new(1),
        SpacePosition::new(0),
        TimePoint::new(0), // No waiting time
    ))
];

// The Solution constructor will validate these decisions against the problem.
// It automatically includes the pre-assigned entries.
let solution = Solution::new(&problem, solver_decisions).unwrap();


// --- 4. Analyze the Solution ---

println!("Solution is valid!");
println!("Total cost: {}", solution.stats().total_cost()); // waiting_cost(0) + deviation_cost(200)
println!("Total waiting time: {}", solution.stats().total_waiting_time());

let vessel1_decision = solution.decisions().get(&RequestId::new(1)).unwrap();
println!("Decision for vessel 1: {:?}", vessel1_decision);

// Cost should be 0 (waiting) + (200 * 10) = 2000
assert_eq!(solution.stats().total_cost().value(), 2000);
```
