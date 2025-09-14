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
use dock_alloc_core::{
    SolverVariable,
    space::{SpaceInterval, SpacePosition},
    time::TimeInterval,
};
use rand::{Rng, seq::IteratorRandom};
use rand_chacha::ChaCha8Rng;

pub struct SpaceShiftOperator<T, C, Q> {
    pub max_shift: usize,
    pub attempts: usize,
    _p: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for SpaceShiftOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            max_shift: 5,
            attempts: 16,
            _p: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for SpaceShiftOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "SpaceShiftOperator"
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

                // Pick a random movable assignment
                let Some(a) = txn.with_explorer(|ex| ex.iter_movable_assignments().choose(rng))
                else {
                    return b.build();
                };

                let req = a.branded_request();
                let cur_t = a.assignment().start_time();
                let cur_s = a.assignment().start_position();
                let len = req.length();

                // choose random shift left (-) or right (+)
                let shift: i64 = rng.random_range(-(self.max_shift as i64)..=self.max_shift as i64);
                if shift == 0 {
                    txn.discard();
                    continue;
                }

                // compute new position
                let new_s = match (cur_s.value() as i64).try_into() {
                    Ok(v) => SpacePosition::new(v),
                    _ => {
                        txn.discard();
                        continue;
                    }
                };

                let space_window = SpaceInterval::new(new_s, new_s + len);
                let time_window = TimeInterval::new(cur_t, cur_t + req.processing_duration());

                // find slot at same start time but shifted in space
                let slot = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&req, time_window, space_window)
                        .find(|s| s.slot().start_time() == cur_t)
                });

                let Some(slot) = slot else {
                    txn.discard();
                    continue;
                };

                // Apply: unassign + assign in new position
                if txn.propose_unassign(&a).is_err() {
                    txn.discard();
                    continue;
                }
                if txn.propose_assign(&req, slot).is_err() {
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
