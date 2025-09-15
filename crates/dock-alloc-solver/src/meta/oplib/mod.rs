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

pub mod bandrepack;
pub mod blockshift;
pub mod cascaderelocate;
pub mod crossinsert;
pub mod destruct;
pub mod exchangetime;
pub mod latepenalty;
pub mod neighborhoodruinrecreate;
pub mod pairswap;
pub mod pull;
pub mod push;
pub mod relocate;
pub mod spaceshift;
pub mod swap;
pub mod windowtighten;

pub mod prelude {
    pub use super::{
        bandrepack::*, blockshift::*, cascaderelocate::*, crossinsert::*, destruct::*,
        exchangetime::*, latepenalty::*, neighborhoodruinrecreate::*, pairswap::*, pull::*,
        push::*, relocate::*, spaceshift::*, swap::*, windowtighten::*,
    };
    use crate::{berth::quay::QuayRead, meta::operator::Operator};
    use dock_alloc_model::prelude::*;
    use num_traits::FromPrimitive;

    pub fn op_list<T, C, Q>(
        _: &Problem<T, C>,
    ) -> Vec<Box<dyn Operator<Time = T, Cost = C, Quay = Q> + Send + Sync + 'static>>
    where
        T: dock_alloc_core::SolverVariable + FromPrimitive + 'static,
        C: dock_alloc_core::SolverVariable
            + core::convert::TryFrom<T>
            + core::convert::TryFrom<usize>
            + 'static,
        Q: QuayRead + Send + Sync + 'static,
    {
        vec![
            Box::new(DestructOperator::<T, C, Q>::default()),
            Box::new(DestructRegionOperator::<T, C, Q>::default()),
            Box::new(RelocateGreedyOperator::<T, C, Q>::default()),
            Box::new(PullForwardOperator::<T, C, Q>::default()),
            Box::new(SwapOperator::<T, C, Q>::default()),
            Box::new(CrossInsertOperator::<T, C, Q>::default()),
            Box::new(BlockShiftOperator::<T, C, Q>::default()),
            Box::new(SpaceShiftOperator::<T, C, Q>::default()),
            Box::new(PushBackOperator::<T, C, Q>::default()),
            Box::new(WindowTightenOperator::<T, C, Q>::default()),
            Box::new(BandRepackOperator::<T, C, Q>::default()),
            Box::new(TwoExchangeTimeOperator::<T, C, Q>::default()),
            Box::new(CascadeRelocateOperator::<T, C, Q>::default()),
            Box::new(NeighborhoodRuinRecreateOperator::<T, C, Q>::default()),
            Box::new(LatePenaltyFocusOperator::<T, C, Q>::default()),
            Box::new(PairSwapBandOperator::<T, C, Q>::default()),
        ]
    }
}
