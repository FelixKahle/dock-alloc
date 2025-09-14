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

pub struct WindowTightenOperator<T, C, Q> {
    pub attempts: usize,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for WindowTightenOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            attempts: 4,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for WindowTightenOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "WindowTightenOperator"
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

                let Some(x) = txn.with_explorer(|ex| ex.iter_movable_assignments().choose(rng))
                else {
                    return builder.build();
                };

                let req = x.branded_request();
                let cur_t = x.assignment().start_time();
                let cur_s = x.assignment().start_position();
                if cur_t <= req.arrival_time() {
                    txn.discard();
                    continue;
                }

                let time_window = TimeInterval::new(req.arrival_time(), cur_t);
                let space_window = SpaceInterval::new(cur_s, cur_s + req.length());

                let best_earlier = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&req, time_window, space_window)
                        .min_by_key(|s| s.slot().start_time())
                });

                let Some(preview) = best_earlier else {
                    txn.discard();
                    continue;
                };
                if preview.slot().start_time() >= cur_t {
                    txn.discard();
                    continue;
                }

                if txn.propose_unassign(&x).is_err() {
                    txn.discard();
                    continue;
                }
                let fresh = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&req, time_window, space_window)
                        .find(|cand| {
                            cand.slot().start_time() == preview.slot().start_time()
                                && cand.slot().space().start() == preview.slot().space().start()
                                && cand.slot().space().end() == preview.slot().space().end()
                        })
                });
                let Some(chosen) = fresh else {
                    txn.discard();
                    continue;
                };
                if txn.propose_assign(&req, chosen).is_err() {
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
