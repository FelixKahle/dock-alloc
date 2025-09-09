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

use crate::{
    berth::{prelude::BerthOccupancy, quay::QuayRead},
    registry::ledger::AssignmentLedger,
};
use num_traits::{PrimInt, Signed};

pub struct SearchState<'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    ledger: AssignmentLedger<'p, T, C>,
    berth: BerthOccupancy<T, Q>,
}

impl<'p, T, C, Q> SearchState<'p, T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    #[inline]
    pub fn new(problem: &'p Problem<T, C>, berth_occupancy: BerthOccupancy<T, Q>) -> Self {
        let ledger = AssignmentLedger::new(problem);
        Self {
            ledger,
            berth: berth_occupancy,
        }
    }

    pub fn berth(&self) -> &BerthOccupancy<T, Q> {
        &self.berth
    }

    pub fn ledger(&self) -> &AssignmentLedger<'p, T, C> {
        &self.ledger
    }

    pub fn ledger_mut(&mut self) -> &mut AssignmentLedger<'p, T, C> {
        &mut self.ledger
    }

    #[inline]
    pub fn view(&'p self) -> SolutionRef<'p, T, C>
    where
        C: TryFrom<T> + TryFrom<usize>,
    {
        SolutionRef::from(&self.ledger)
    }

    #[inline]
    pub fn to_owned(&self) -> OwnedSolution<T, C>
    where
        C: TryFrom<T> + TryFrom<usize>,
    {
        self.view().into_owned()
    }
}

pub trait ConstructiveSolver<T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    type SolveError: std::error::Error;

    fn build_state<'p>(
        &self,
        problem: &'p Problem<T, C>,
    ) -> Result<SearchState<'p, T, C, Q>, Self::SolveError>;
}

pub trait Solver<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    type SolveError: std::error::Error;

    fn solve<'p>(
        &self,
        problem: &'p Problem<T, C>,
    ) -> Result<SolutionRef<'p, T, C>, Self::SolveError>;
}
