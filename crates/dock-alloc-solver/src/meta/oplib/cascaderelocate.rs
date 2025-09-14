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
    time::{TimeInterval, TimePoint},
};
use rand::seq::{IteratorRandom, SliceRandom};
use rand_chacha::ChaCha8Rng;

pub struct CascadeRelocateOperator<T, C, Q> {
    pub attempts: usize,
    pub max_group: usize,
    _p: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for CascadeRelocateOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            attempts: 16,
            max_group: 6,
            _p: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for CascadeRelocateOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "CascadeRelocateOperator"
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

                let Some(seed) = txn.with_explorer(|ex| ex.iter_movable_assignments().choose(rng))
                else {
                    return builder.build();
                };

                let mut group = vec![seed.clone()];
                let need = self.max_group.saturating_sub(1);
                let mut extras: Vec<_> = txn.with_explorer(|ex| {
                    ex.iter_movable_assignments()
                        .filter(|a| a.id() != seed.id())
                        .choose_multiple(rng, need)
                });
                group.append(&mut extras);
                group.sort_by_key(|a| a.id().value());
                group.dedup_by_key(|a| a.id().value());

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
                let quay_band = txn.problem().quay_interval();

                // destroy
                let mut ok = true;
                for a in &group {
                    if txn.propose_unassign(a).is_err() {
                        ok = false;
                        break;
                    }
                }
                if !ok {
                    txn.discard();
                    continue;
                }

                {
                    let req = seed.branded_request();
                    let time_window = TimeInterval::new(req.arrival_time(), latest_event_time);
                    let slot = txn.with_explorer(|ex| {
                        ex.iter_slots_for_request_within(&req, time_window, quay_band)
                            .min_by_key(|s| s.slot().start_time())
                    });
                    let Some(s) = slot else {
                        txn.discard();
                        continue;
                    };
                    if txn.propose_assign(&req, s).is_err() {
                        txn.discard();
                        continue;
                    }
                }

                let seed_id = seed.id();
                let mut others: Vec<_> = group.into_iter().filter(|a| a.id() != seed_id).collect();
                others.shuffle(rng);

                let mut all_ok = true;
                for a in &others {
                    let req = a.branded_request();
                    let time_window = TimeInterval::new(req.arrival_time(), latest_event_time);
                    let slot = txn.with_explorer(|ex| {
                        ex.iter_slots_for_request_within(&req, time_window, quay_band)
                            .min_by_key(|s| s.slot().start_time())
                    });
                    let Some(s) = slot else {
                        all_ok = false;
                        break;
                    };
                    if txn.propose_assign(&req, s).is_err() {
                        all_ok = false;
                        break;
                    }
                }

                if all_ok {
                    txn.commit();
                    return builder.build();
                } else {
                    txn.discard();
                }
            }
            builder.build()
        })
    }
}
