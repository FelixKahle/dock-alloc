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
use dock_alloc_core::{SolverVariable, time::TimeDelta};
use rand::seq::IteratorRandom;
use rand_chacha::ChaCha8Rng;

pub struct BlockShiftOperator<T, C, Q> {
    pub max_block: usize,
    pub attempts: usize,
    _p: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for BlockShiftOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            max_block: 4,
            attempts: 16,
            _p: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for BlockShiftOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "BlockShiftOperator"
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

                // pick a random anchor assignment
                let Some(anchor) =
                    txn.with_explorer(|ex| ex.iter_movable_assignments().choose(rng))
                else {
                    return b.build();
                };

                let anchor_start = anchor.assignment().start_time();
                let block: Vec<_> = txn.with_explorer(|ex| {
                    ex.iter_movable_assignments()
                        .filter(|a| a.assignment().start_time() >= anchor_start)
                        .take(self.max_block)
                        .collect()
                });

                if block.is_empty() {
                    txn.discard();
                    continue;
                }

                // decide shift: forward (+) or backward (-) in time
                let dir = if rand::random::<bool>() { 1 } else { -1 };
                let delta = TimeDelta::new(T::one()) * T::from(dir).unwrap_or(T::one());

                let mut success = true;
                for a in &block {
                    let req = a.branded_request();
                    let cur_s = a.assignment().start_position();
                    let new_t = a.assignment().start_time() + delta;

                    let candidate = txn.with_explorer(|ex| {
                        ex.iter_slots_for_request_within(
                            &req,
                            dock_alloc_core::time::TimeInterval::new(
                                req.arrival_time(),
                                new_t + req.processing_duration(),
                            ),
                            dock_alloc_core::space::SpaceInterval::new(cur_s, cur_s + req.length()),
                        )
                        .find(|slot| slot.slot().start_time() == new_t)
                    });

                    let Some(slot) = candidate else {
                        success = false;
                        break;
                    };

                    if txn.propose_unassign(a).is_err() {
                        success = false;
                        break;
                    }
                    if txn.propose_assign(&req, slot).is_err() {
                        success = false;
                        break;
                    }
                }

                if success {
                    txn.commit();
                    return b.build();
                } else {
                    txn.discard();
                }
            }
            b.build()
        })
    }
}
