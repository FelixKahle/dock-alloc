# Dock Allocation Model (`dock-alloc-model`)

A high-level Rust crate for modeling the **Berth Allocation Problem (BAP)** using structured, domain-specific types.

`dock-alloc-model` builds on the type-safe primitives from `dock-alloc-core` to provide comprehensive data structures for defining BAP instances and their solutions. It serves as the primary interface for algorithms that solve berth allocation challenges.

---

## Core Concepts

This crate defines the entities that make up a complete berth allocation problem, from individual ship requests to the final solution.

* **`RequestId`**: A simple wrapper for a `u64` to provide a unique, type-safe identifier for each request.
* **`Request<T, C>`**: Represents a single vessel or entity needing a berth. It bundles all relevant data:
    * Physical attributes like `length` and `processing_duration`.
    * Constraints like `feasible_time_window` and `feasible_space_window`.
    * Economic factors like `cost_per_delay` and `cost_per_position_deviation`.
* **`Assignment<T, C>`**: A concrete allocation of a `Request` to a specific `start_time` and `start_position`. This is the fundamental building block of a solution.
* **`Problem<T, C>`**: Encapsulates an entire BAP instance. It includes the `quay_length` and a set of `ProblemEntry` items, which can be either unassigned requests to be scheduled or pre-assigned assignments that are fixed.
* **`Solution<T, C>`**: Represents a complete set of assignments for a given problem. It automatically calculates `SolutionStats` (total cost, total waiting time, etc.) to provide an immediate measure of the solution's quality.

---

## Features

* **Structured Problem Representation**: Provides clear, ergonomic structs to define complex BAP instances.
* **Builds on a Safe Core**: Inherits the compile-time safety and correctness guarantees of `dock-alloc-core`.
* **Automatic Solution Analysis**: The `Solution` struct automatically computes key performance indicators (KPIs) like total cost, waiting time, and deviation from target positions.
* **Flexible and Generic**: Uses generic types for time and cost (`T`, `C`) to adapt to different scales and precision requirements.
* **Comprehensive Documentation**: Every public API is documented with clear explanations and usage examples.

---

## Usage

Here is a basic example of how to define a simple BAP instance, create a solution, and review its statistics.

```rust
use dock_alloc_core::domain::{
    Cost, SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use dock_alloc_model::{Assignment, Problem, ProblemEntry, Request, RequestId, Solution};
use std::collections::{HashMap, HashSet};

fn main() {
    // 1. Define a request for a ship needing a berth.
    let request = Request::new(
        RequestId::new(1),
        SpaceLength::new(100), // Ship length
        TimeDelta::new(10), // Processing time
        SpacePosition::new(50), // Target position on the quay
        Cost::new(5), // Cost per unit of waiting time
        Cost::new(2), // Cost per unit of distance from target
        TimeInterval::new(TimePoint::new(0), TimePoint::new(100)), // Feasible arrival window
        SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(200)), // Feasible berthing area
    );

    // 2. Create a problem instance.
    let mut entries = HashSet::new();
    entries.insert(ProblemEntry::Unassigned(request));
    let problem = Problem::new(entries, SpaceLength::new(200)); // Total quay length is 200.

    println!("Defined a problem with {} request(s).", problem.entries().len());

    // 3. (A solver would run here) Create a hypothetical assignment for the request.
    let assignment = Assignment::new(
        request,
        SpacePosition::new(30), // Assigned position
        TimePoint::new(5), // Assigned time
    );

    // 4. Construct a solution from the assignments.
    let mut assignments = HashMap::new();
    assignments.insert(request.id(), assignment);
    let solution = Solution::from_assignments(assignments);

    // 5. Review the solution's automatically calculated statistics.
    let stats = solution.stats();
    println!(
        "Solution Stats:\n - Total Cost: {}\n - Total Waiting Time: {}\n - Total Position Deviation: {}",
        stats.total_cost(),
        stats.total_waiting_time(),
        stats.total_target_position_deviation()
    );
    // Expected output:
    // Defined a problem with 1 request(s).
    // Solution Stats:
    //  - Total Cost: Cost(65)
    //  - Total Waiting Time: TimeDelta(5)
    //  - Total Position Deviation: SpaceLength(20)
}
```
