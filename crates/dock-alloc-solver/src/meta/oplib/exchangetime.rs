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

pub struct TwoExchangeTimeOperator<T, C, Q> {
    /// How many random pairs to try per call.
    pub attempts: usize,
    _p: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for TwoExchangeTimeOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            attempts: 32,
            _p: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for TwoExchangeTimeOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "TwoExchangeTimeOperator"
    }

    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut builder| {
            for _ in 0..self.attempts {
                let mut txn = builder.begin();

                // Pick two distinct movable assignments.
                let (Some(a), Some(b)) = txn.with_explorer(|ex| {
                    (
                        ex.iter_movable_assignments().choose(rng),
                        ex.iter_movable_assignments().choose(rng),
                    )
                }) else {
                    return builder.build();
                };
                if a.id() == b.id() {
                    txn.discard();
                    continue;
                }

                let ra = a.branded_request();
                let rb = b.branded_request();

                let sa = a.assignment().start_position();
                let sb = b.assignment().start_position();

                let ta = a.assignment().start_time();
                let tb = b.assignment().start_time();

                // Keep each in its own band; swap times only.
                let band_a = SpaceInterval::new(sa, sa + ra.length());
                let band_b = SpaceInterval::new(sb, sb + rb.length());

                // Exact-time windows (degenerate intervals).
                let time_for_a = TimeInterval::new(tb, tb);
                let time_for_b = TimeInterval::new(ta, ta);

                // Check feasibility for each at the other's start time in its own band.
                let slot_a_at_tb = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&ra, time_for_a, band_a)
                        .next()
                });
                let slot_b_at_ta = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&rb, time_for_b, band_b)
                        .next()
                });

                // If both feasible, apply the exchange: unassign both, assign into new times.
                if let (Some(slot_a), Some(slot_b)) = (slot_a_at_tb, slot_b_at_ta) {
                    if txn.propose_unassign(&a).is_err() {
                        txn.discard();
                        continue;
                    }
                    if txn.propose_unassign(&b).is_err() {
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
                    return builder.build();
                }

                txn.discard();
            }

            builder.build()
        })
    }
}
