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
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimeInterval, TimePoint},
};
use rand::seq::{IteratorRandom, SliceRandom};
use rand_chacha::ChaCha8Rng;

pub struct NeighborhoodRuinRecreateOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub time_radius: TimeDelta<T>,
    pub space_radius: SpaceLength,
    pub attempts: usize,
    pub shuffle_recreate: bool,
    _p: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for NeighborhoodRuinRecreateOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            time_radius: TimeDelta::zero(),
            space_radius: SpaceLength::new(0),
            attempts: 8,
            shuffle_recreate: true,
            _p: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for NeighborhoodRuinRecreateOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "NeighborhoodRuinRecreateOperator"
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

                // Seed
                let Some(seed) = txn.with_explorer(|ex| ex.iter_movable_assignments().choose(rng))
                else {
                    return builder.build();
                };

                let seed_t = seed.assignment().start_time();
                let seed_s = seed.assignment().start_position();
                let seed_len = seed.branded_request().length();

                let t_lo = TimePoint::new(seed_t.value().saturating_sub(self.time_radius.value()));
                let t_hi = TimePoint::new(seed_t.value().saturating_add(self.time_radius.value()));
                let nb_s_lo =
                    SpacePosition::new(seed_s.value().saturating_sub(self.space_radius.value()));
                let nb_s_hi = SpacePosition::new(
                    seed_s
                        .value()
                        .saturating_add(seed_len.value())
                        .saturating_add(self.space_radius.value()),
                );
                let nb_band = SpaceInterval::new(nb_s_lo, nb_s_hi);

                let mut neighborhood = txn.with_explorer(|ex| {
                    ex.iter_movable_assignments()
                        .filter(|a| {
                            let at = a.assignment().start_time();
                            if at < t_lo || at > t_hi {
                                return false;
                            }
                            let as_ = a.assignment().start_position();
                            let band = SpaceInterval::new(
                                as_,
                                SpacePosition::new(
                                    as_.value() + a.branded_request().length().value(),
                                ),
                            );
                            band.intersects(&nb_band)
                        })
                        .collect::<Vec<_>>()
                });

                if neighborhood.is_empty() {
                    txn.discard();
                    continue;
                }

                let mut ok = true;
                for a in &neighborhood {
                    if txn.propose_unassign(a).is_err() {
                        ok = false;
                        break;
                    }
                }
                if !ok {
                    txn.discard();
                    continue;
                }

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

                if self.shuffle_recreate {
                    neighborhood.shuffle(rng);
                } else {
                    neighborhood.sort_by_key(|a| a.branded_request().arrival_time());
                }

                let mut all_ok = true;
                for a in &neighborhood {
                    let req = a.branded_request();
                    let tw = TimeInterval::new(req.arrival_time(), latest_event_time);
                    let slot = txn.with_explorer(|ex| {
                        ex.iter_slots_for_request_within(&req, tw, quay_band)
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
