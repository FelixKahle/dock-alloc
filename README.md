# Dock-Alloc

[![License: MIT](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE)
[![C++](https://img.shields.io/badge/language-C++20-blue.svg)](https://isocpp.org/)
[![Test Status](https://img.shields.io/github/actions/workflow/status/FelixKahle/dock-alloc/test.yaml?label=tests)](https://github.com/FelixKahle/dock-alloc/actions/workflows/test.yaml)

**Dock-Alloc** is a research-driven C++20 project for developing a high-performance,
scalable solver for the **Berth Allocation Problem (BAP)**.
It combines modern data structures, bit-level optimization, and algorithm engineering techniques
to accelerate metaheuristic search procedures under spatio-temporal constraints.

---

## 🚢 Problem Description

The **Berth Allocation Problem (BAP)** is a classical NP-hard problem in maritime logistics.
It involves assigning vessels to berth positions over time, taking into account:

- Vessel dimensions and arrival windows
- Berth availability and compatibility
- Operational constraints (e.g., time windows, service durations)

Solving this problem efficiently is crucial for reducing congestion and improving
throughput at container terminals.

---

## 🎯 Project Goals

This project aims to:

- Develop **scalable data structures** for tracking berth occupancy in discrete time–space
- Enable **fast neighborhood generation and feasibility checks** for metaheuristics
- Support **local search** and **simulated annealing** in large-scale instances
- Evaluate novel techniques such as:
    - SIMD-accelerated bit vectors
    - Metadata-augmented segment trees
    - Sparse, event-driven interval trees for time
