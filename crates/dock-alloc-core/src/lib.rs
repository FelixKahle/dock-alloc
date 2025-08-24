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

//! # Berth Allocation Core Library
//!
//! `dock_alloc_core` provides the foundational data structures and primitives
//! for solving the Berth Allocation Problem (BAP). It offers a type-safe and
//! robust API for representing the core concepts of time and quay space.
//!
//! This crate is the bedrock of the Dock Allocation project, designed to prevent
//! common logical errors at compile time by using strong types for domain-specific
//! concepts.
//!
//! ## Core Modules
//!
//! - **`domain`**: Contains the primary data types specific to BAP, such as
//!   `TimePoint`, `TimeDelta`, `SpacePosition`, `SpaceLength` and `Cost`.
//! - **`primitives`**: Provides generic, reusable structures like `Interval`, which
//!   are used to build the more complex domain types.

pub mod domain;
pub mod primitives;
