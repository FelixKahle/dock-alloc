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
    time::{TimeDelta, TimeInterval},
};
use rand_chacha::ChaCha8Rng;

pub struct LatePenaltyFocusOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub attempts: usize,
    _p: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for LatePenaltyFocusOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            attempts: 8,
            _p: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for LatePenaltyFocusOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "LatePenaltyFocusOperator"
    }

    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        _rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut builder| {
            for _ in 0..self.attempts {
                let mut txn = builder.begin();
                let worst = txn.with_explorer(|ex| {
                    ex.iter_movable_assignments().max_by(|a, b| {
                        let aw = {
                            let t = a.assignment().start_time();
                            let arr = a.branded_request().arrival_time();
                            let w: TimeDelta<T> = (t - arr).max(TimeDelta::zero());
                            w.value()
                        };
                        let bw = {
                            let t = b.assignment().start_time();
                            let arr = b.branded_request().arrival_time();
                            let w: TimeDelta<T> = (t - arr).max(TimeDelta::zero());
                            w.value()
                        };
                        aw.cmp(&bw)
                    })
                });

                let Some(worst) = worst else {
                    return builder.build();
                };

                let req = worst.branded_request();
                let cur_t = worst.assignment().start_time();
                let arr = req.arrival_time();
                if cur_t <= arr {
                    txn.discard();
                    continue;
                }

                let time_window = TimeInterval::new(arr, cur_t);
                let quay_band = txn.problem().quay_interval();

                let best = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&req, time_window, quay_band)
                        .min_by_key(|s| s.slot().start_time())
                });

                let Some(slot) = best else {
                    txn.discard();
                    continue;
                };

                if slot.slot().start_time() >= cur_t {
                    txn.discard();
                    continue;
                }

                if txn.propose_unassign(&worst).is_err() {
                    txn.discard();
                    continue;
                }
                if txn.propose_assign(&req, slot).is_err() {
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
