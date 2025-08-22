# Dock Allocation Core (`dock-alloc-core`)

A foundational Rust crate providing robust, type-safe primitives for the **Berth Allocation Problem (BAP)**.

`dock-alloc-core` is the bedrock of the Dock Allocation project. It establishes a strong data model for the two primary domains of the problem—**time** and **space**—to prevent common logical errors at compile time.

---

## Core Concepts

The library's design revolves around the newtype pattern to create distinct, non-interchangeable types for different domain concepts. This means you can't accidentally add a `TimePoint` to another `TimePoint`, or a `SpacePosition` to another `SpacePosition`, which helps ensure logical correctness throughout your application.

### Time Domain

* **`TimePoint<T>`**: Represents a specific, absolute point in time (e.g., an arrival timestamp).
* **`TimeDelta<T>`**: Represents a duration or the difference between two time points (e.g., handling time).
* **`TimeInterval<T>`**: A half-open interval `[start, end)` composed of two `TimePoint`s, representing a time window.

### Space Domain

* **`SpacePosition`**: Represents a discrete position along a one-dimensional space (e.g., a quay).
* **`SpaceLength`**: Represents a length or size, such as that of a vessel or a quay segment.
* **`SpaceInterval`**: A half-open interval `[start, end)` representing a contiguous section of space.

### Cost Domain

* **`Cost<T>`**: Represents a cost associated with an allocation, such as the time or space used by a ship.

---

## Features

* **Type Safety**: Prevents incorrect operations between different domain types at compile time.
* **Robust Arithmetic**: All types implement standard arithmetic traits (`+`, `-`, `*`, `/`) with both panicking and safe (`checked_`, `saturating_`) versions to handle overflow and underflow gracefully.
* **Ergonomic API**: Includes convenient methods like `.span_of()` to create intervals and `Sum` implementations for easy aggregation.
* **Comprehensive Documentation**: Every public function is documented with clear explanations and examples.
* **Thoroughly Tested**: A full suite of unit tests covers functionality, edge cases, and panic conditions.

---

## Usage

Here is a basic example of how to model a ship's allocation on a quay using the types from this crate.

```rust
use dock_alloc_core::domain::{TimePoint, TimeDelta, SpacePosition, SpaceLength};

fn main() {
    // Define a time window for the ship's stay.
    let arrival_time = TimePoint::new(100_i64);
    let handling_duration = TimeDelta::new(50_i64);
    let time_window = arrival_time.span_of(handling_duration).unwrap();

    // Define the space required by the ship.
    let berth_position = SpacePosition::new(20);
    let ship_length = SpaceLength::new(15);
    let space_interval = berth_position.span_of(ship_length).unwrap();

    println!(
        "Ship is allocated from {} to {} at positions {} to {}.",
        time_window.start(),
        time_window.end(),
        space_interval.start(),
        space_interval.end()
    );
    // Output: Ship is allocated from TimePoint(100) to TimePoint(150) at positions SpacePosition(20) to SpacePosition(35).
}
```
