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
    space::SpacePosition,
    time::{TimeInterval, TimePoint},
};
use rand::{
    Rng,
    seq::{IteratorRandom, SliceRandom},
};
use rand_chacha::ChaCha8Rng;

pub struct DestructOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub fraction: f64,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for DestructOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            fraction: 0.05,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for DestructOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "DestructOperator"
    }

    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, Self::Time, Self::Cost, Self::Quay>,
    ) -> Plan<'p, Self::Time, Self::Cost> {
        ctx.with_builder(|mut builder| {
            let mut transaction = builder.begin();

            let victims = transaction.with_explorer(|explorer| {
                let n = explorer.iter_movable_assignments().count();
                let f = self.fraction.clamp(0.0, 1.0);
                let mut k = (f * n as f64).round() as usize;
                if f > 0.0 {
                    k = k.max(1);
                }

                explorer.iter_movable_assignments().choose_multiple(rng, k)
            });

            let mut unassigned: Vec<_> = victims
                .into_iter()
                .filter_map(|v| transaction.propose_unassign(&v).ok().map(|res| (v, res)))
                .collect();

            unassigned.shuffle(rng);

            let latest_event_time = transaction
                .problem()
                .iter_any_requests()
                .map(|r| r.arrival_time())
                .max()
                .unwrap_or(TimePoint::zero())
                + transaction
                    .problem()
                    .iter_any_requests()
                    .map(|r| r.processing_duration())
                    .sum();
            let quay_interval = transaction.problem().quay_interval();

            for target in unassigned {
                let request = target.0.branded_request();
                let arrival = request.arrival_time();
                let time_search_window = TimeInterval::new(arrival, latest_event_time);
                let option_slot = transaction.with_explorer(|explorer| {
                    explorer
                        .iter_slots_for_request_within(&request, time_search_window, quay_interval)
                        .choose(rng)
                });

                let res = match option_slot {
                    Some(slot) => transaction.propose_assign(&request, slot),
                    None => {
                        transaction.discard();
                        return builder.build();
                    }
                };

                if res.is_err() {
                    transaction.discard();
                    return builder.build();
                }
            }

            transaction.commit();
            builder.build()
        })
    }
}

pub struct DestructRegionOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub fraction: f64,
    _phantom: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for DestructRegionOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            fraction: 0.05,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for DestructRegionOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "DestructRegionOperator"
    }

    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, Self::Time, Self::Cost, Self::Quay>,
    ) -> Plan<'p, Self::Time, Self::Cost> {
        ctx.with_builder(|mut builder| {
            let mut transaction = builder.begin();

            let victims = transaction.with_explorer(|explorer| {
                let n = explorer.iter_movable_assignments().count();
                let f = self.fraction.clamp(0.0, 1.0);
                let mut k = (f * n as f64).round() as usize;
                if f > 0.0 {
                    k = k.max(1);
                }

                explorer.iter_movable_assignments().choose_multiple(rng, k)
            });

            let mut unassigned: Vec<_> = victims
                .into_iter()
                .filter_map(|v| transaction.propose_unassign(&v).ok().map(|res| (v, res)))
                .collect();

            unassigned.shuffle(rng);

            let latest_event_time = transaction
                .problem()
                .iter_any_requests()
                .map(|r| r.arrival_time())
                .max()
                .unwrap_or(TimePoint::zero())
                + transaction
                    .problem()
                    .iter_any_requests()
                    .map(|r| r.processing_duration())
                    .sum();
            let quay_interval = transaction.problem().quay_interval();

            for target in unassigned {
                let request = target.0.branded_request();
                let arrival = request.arrival_time();
                let time_search_window = TimeInterval::new(arrival, latest_event_time);

                let option_region = transaction.with_explorer(|explorer| {
                    explorer
                        .iter_regions_for_request_within(
                            &request,
                            time_search_window,
                            quay_interval,
                        )
                        .choose(rng)
                });

                let branded_region = match option_region {
                    Some(r) => r,
                    None => {
                        transaction.discard();
                        return builder.build();
                    }
                };

                let rectangle = branded_region.region().rectangle();

                let time_bounds = rectangle.time();
                let space_bounds = rectangle.space();
                let proc_duration = request.processing_duration();
                let req_length = request.length();

                // Random start time (earliest possible to latest valid)
                let latest_start_time = time_bounds.end() - proc_duration;
                let chosen_time = if time_bounds.start() >= latest_start_time {
                    time_bounds.start()
                } else {
                    let range = latest_start_time.value() - time_bounds.start().value();
                    let offset = match T::from(rng.random_range(T::zero()..=range)) {
                        Ok(val) => val,
                        Err(_) => {
                            transaction.discard();
                            return builder.build();
                        }
                    };
                    TimePoint::new(time_bounds.start().value() + offset)
                };

                let latest_start_pos = space_bounds
                    .end()
                    .value()
                    .saturating_sub(req_length.value());
                let chosen_pos = if space_bounds.start().value() >= latest_start_pos {
                    space_bounds.start()
                } else {
                    let range = latest_start_pos - space_bounds.start().value();
                    let offset = rng.random_range(0..=range);
                    SpacePosition::new(space_bounds.start().value() + offset)
                };

                if transaction
                    .propose_assign_at(&request, &branded_region, chosen_time, chosen_pos)
                    .is_err()
                {
                    transaction.discard();
                    return builder.build();
                }
            }

            transaction.commit();
            builder.build()
        })
    }
}
