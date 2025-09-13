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

use crate::berth::quay::QuayRead;
use crate::framework::planning::{Plan, PlanningContext};
use crate::meta::operator::Operator;
use dock_alloc_core::{
    SolverVariable,
    time::{TimeInterval, TimePoint},
};
use rand::seq::IteratorRandom;
use rand_chacha::ChaCha8Rng;

pub struct RelocateGreedyOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub attempts: usize,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for RelocateGreedyOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            attempts: 16,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for RelocateGreedyOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "RelocateGreedyOperator"
    }

    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, Self::Time, Self::Cost, Self::Quay>,
    ) -> Plan<'p, Self::Time, Self::Cost> {
        ctx.with_builder(|mut builder| {
            for _ in 0..self.attempts {
                let mut txn = builder.begin();

                let Some(a) = txn.with_explorer(|ex| ex.iter_movable_assignments().choose(rng))
                else {
                    return builder.build();
                };

                let req = a.branded_request();
                let cur_t = a.assignment().start_time();
                let cur_s = a.assignment().start_position();

                // generous global window
                let latest_event_time = txn
                    .problem()
                    .iter_any_requests()
                    .map(|r| r.arrival_time())
                    .max()
                    .unwrap_or(TimePoint::zero())
                    + txn
                        .problem()
                        .iter_any_requests()
                        .map(|r| r.processing_duration())
                        .sum();

                let time_window = TimeInterval::new(req.arrival_time(), latest_event_time);
                let space_window = txn.problem().quay_interval();

                // pick the earliest start slot (simple greedy)
                let best = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&req, time_window, space_window)
                        .min_by_key(|s| s.slot().start_time())
                });

                let Some(best) = best else {
                    txn.discard();
                    continue;
                };

                // skip if no change
                if best.slot().start_time() == cur_t && best.slot().space().start() == cur_s {
                    txn.discard();
                    continue;
                }

                if txn.propose_unassign(&a).is_err() {
                    txn.discard();
                    continue;
                }
                if txn.propose_assign(&req, best).is_err() {
                    txn.discard();
                    continue;
                }

                txn.commit();
                return builder.build();
            }
            builder.build()
        })
    }
}
