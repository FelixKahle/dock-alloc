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

pub mod ec;
pub mod grbok;
pub mod grl;
pub mod mrs;
pub mod mtef;
pub mod mtlf;
pub mod rdr;
pub mod rl;
pub mod rs;
pub mod sn;
mod util;

pub mod prelude {
    pub use super::{
        ec::*, grbok::*, grl::*, mrs::*, mtef::*, mtlf::*, rdr::*, rl::*, rs::*, sn::*,
    };
    use crate::meta::operator::Operator;
    use dock_alloc_model::model::Problem;
    use num_traits::FromPrimitive;

    pub fn op_list<T, C, Q>(
        problem: &Problem<T, C>,
    ) -> Vec<Box<dyn Operator<Time = T, Cost = C, Quay = Q> + Send + Sync + 'static>>
    where
        T: dock_alloc_core::SolverVariable + FromPrimitive + 'static,
        C: dock_alloc_core::SolverVariable
            + core::convert::TryFrom<T>
            + core::convert::TryFrom<usize>
            + 'static,
        Q: crate::berth::quay::QuayRead + Send + Sync + 'static,
    {
        vec![
            Box::new(RandomSwapOperator::<T, C, Q>::from(problem)),
            Box::new(RandomDestroyRepairOperator::<T, C, Q>::from(problem)),
            Box::new(RelocateLocal::<T, C, Q>::from(problem)),
            Box::new(MoveToLatestFeasibleOperator::<T, C, Q>::from(problem)),
            Box::new(MoveToEarliestFeasibleOperator::<T, C, Q>::from(problem)),
            Box::new(SpaceNudgeLeftOperator::<T, C, Q>::from(problem)),
            Box::new(SpaceNudgeRightOperator::<T, C, Q>::from(problem)),
            Box::new(GlobalRelocateRandomOperator::<T, C, Q>::from(problem)),
            Box::new(GreedyRelocateBestOfKOperator::<T, C, Q>::from(problem)),
            Box::new(EjectionChain2Operator::<T, C, Q>::from(problem)),
            Box::new(MultiRelocateShakerOperator::<T, C, Q>::from(problem)),
        ]
    }
}
