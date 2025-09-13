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

use crate::{berth::quay::QuayRead, meta::operator::Operator};
use dock_alloc_core::SolverVariable;

pub struct NoOpOperator<T, C, Q> {
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for NoOpOperator<T, C, Q> {
    fn default() -> Self {
        Self {
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for NoOpOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        _: &mut rand_chacha::ChaCha8Rng,
        ctx: crate::framework::planning::PlanningContext<
            'p,
            'al,
            'bo,
            Self::Time,
            Self::Cost,
            Self::Quay,
        >,
    ) -> crate::framework::planning::Plan<'p, Self::Time, Self::Cost> {
        ctx.with_builder(|builder| builder.build())
    }

    fn name(&self) -> &'static str {
        "NoOpOperator"
    }
}
