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

use std::marker::PhantomData;

use crate::{
    domain::Version,
    ledger::{AssignmentLedger, AssignmentOverlay},
    occupancy::{BerthOccupancy, BerthOccupancyOverlay},
    quay::QuayRead,
};
use dock_alloc_model::Problem;
use num_traits::{PrimInt, Signed};

pub struct ProposeCtx<'brand, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    ledger: &'brand AssignmentLedger<'brand, 'brand, T, C>,
    berth: &'brand BerthOccupancy<T, Q>,
    problem: &'brand Problem<T, C>,
    stamp: Version,
    _brand: PhantomData<&'brand mut &'brand ()>,
}

impl<'brand, T, C, Q> ProposeCtx<'brand, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    pub fn new(
        ledger: &'brand AssignmentLedger<'brand, 'brand, T, C>,
        berth: &'brand BerthOccupancy<T, Q>,
        problem: &'brand Problem<T, C>,
        stamp: Version,
    ) -> Self {
        Self {
            ledger,
            berth,
            problem,
            stamp,
            _brand: PhantomData,
        }
    }

    pub fn ledger(&self) -> &'brand AssignmentLedger<'brand, 'brand, T, C> {
        self.ledger
    }

    pub fn berth(&self) -> &'brand BerthOccupancy<T, Q> {
        self.berth
    }

    pub fn problem(&self) -> &'brand Problem<T, C> {
        self.problem
    }

    pub fn stamp(&self) -> Version {
        self.stamp
    }
}
