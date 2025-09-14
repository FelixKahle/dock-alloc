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
    berth::quay::QuayRead,
    framework::planning::{Plan, PlanningContext},
    meta::operator::Operator,
};
use dock_alloc_core::{SolverVariable, space::SpaceInterval, time::TimeInterval};
use rand::seq::IteratorRandom;
use rand_chacha::ChaCha8Rng;

pub struct CrossInsertOperator<T, C, Q> {
    pub attempts: usize,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for CrossInsertOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            attempts: 32,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for CrossInsertOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "CrossInsertOperator"
    }

    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            for _ in 0..self.attempts {
                let mut txn = b.begin();

                let (Some(a), Some(bx)) = txn.with_explorer(|ex| {
                    let a = ex.iter_movable_assignments().choose(rng);
                    let b = ex.iter_movable_assignments().choose(rng);
                    (a, b)
                }) else {
                    return b.build();
                };
                if a.id() == bx.id() {
                    txn.discard();
                    continue;
                }

                let ra = a.branded_request();
                let rb = bx.branded_request();
                let sb = bx.assignment();

                let time_window = TimeInterval::new(
                    ra.arrival_time(),
                    sb.start_time() + rb.processing_duration(),
                );
                let space_window =
                    SpaceInterval::new(sb.start_position(), sb.start_position() + rb.length());

                let candidate = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&ra, time_window, space_window)
                        .choose(rng)
                });

                let Some(slot) = candidate else {
                    txn.discard();
                    continue;
                };

                if txn.propose_unassign(&a).is_err() {
                    txn.discard();
                    continue;
                }
                if txn.propose_assign(&ra, slot).is_err() {
                    txn.discard();
                    continue;
                }

                txn.commit();
                return b.build();
            }
            b.build()
        })
    }
}
