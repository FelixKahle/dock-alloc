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
use dock_alloc_core::SolverVariable;
use rand::seq::IteratorRandom;

pub struct SwapOperator<T, C, Q> {
    pub attempts: usize,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T: SolverVariable, C: SolverVariable + TryFrom<T> + TryFrom<usize>, Q: QuayRead + Send + Sync>
    Default for SwapOperator<T, C, Q>
{
    fn default() -> Self {
        Self {
            attempts: 32,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for SwapOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "SwapOperator"
    }

    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        rng: &mut rand_chacha::ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            for _ in 0..self.attempts {
                let mut txn = b.begin();
                let (Some(a), Some(bx)) = txn.with_explorer(|ex| {
                    let it = ex.iter_movable_assignments();
                    let a = it.choose(rng);
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
                let sa = a.assignment();
                let sb = bx.assignment();

                let ok_a = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(
                        &ra,
                        dock_alloc_core::time::TimeInterval::new(sb.start_time(), sb.start_time()),
                        dock_alloc_core::space::SpaceInterval::new(
                            sb.start_position(),
                            sb.start_position() + ra.length(),
                        ),
                    )
                    .next()
                });

                let ok_b = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(
                        &rb,
                        dock_alloc_core::time::TimeInterval::new(sa.start_time(), sa.start_time()),
                        dock_alloc_core::space::SpaceInterval::new(
                            sa.start_position(),
                            sa.start_position() + rb.length(),
                        ),
                    )
                    .next()
                });

                if let (Some(slot_a), Some(slot_b)) = (ok_a, ok_b) {
                    if txn.propose_unassign(&a).is_err() {
                        txn.discard();
                        continue;
                    }
                    if txn.propose_unassign(&bx).is_err() {
                        txn.discard();
                        continue;
                    }
                    if txn.propose_assign(&ra, slot_a).is_err() {
                        txn.discard();
                        continue;
                    }
                    if txn.propose_assign(&rb, slot_b).is_err() {
                        txn.discard();
                        continue;
                    }
                    txn.commit();
                    return b.build();
                }
                txn.discard();
            }
            b.build()
        })
    }
}
