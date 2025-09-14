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

// Copyright (c) 2025 Felix Kahle.
// MIT license header…

use crate::{
    berth::quay::QuayRead,
    framework::planning::{Plan, PlanningContext},
    meta::operator::Operator,
};
use dock_alloc_core::{
    SolverVariable,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::TimeInterval,
};
use rand::seq::IteratorRandom;
use rand_chacha::ChaCha8Rng;

pub struct PairSwapBandOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    pub attempts: usize,
    pub lateral_slack: usize,
    _p: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for PairSwapBandOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            attempts: 32,
            lateral_slack: 4,
            _p: core::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for PairSwapBandOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "PairSwapBandOperator"
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

                let (Some(a), Some(bx)) = txn.with_explorer(|ex| {
                    let a = ex.iter_movable_assignments().choose(rng);
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

                let t_a = sa.start_time();
                let t_b = sb.start_time();

                let s_b = sb.start_position();
                let s_a = sa.start_position();

                let slack = self.lateral_slack;

                let band_window_for = |req_len: SpaceLength,
                                       base_start: SpacePosition|
                 -> SpaceInterval {
                    let base = base_start.value();
                    let start = base.saturating_sub(slack);
                    let width = req_len.value().saturating_add(2 * slack);
                    SpaceInterval::new(SpacePosition::new(start), SpacePosition::new(start + width))
                };

                let len_a = ra.length();
                let len_b = rb.length();

                let space_win_for_a = band_window_for(len_a, s_b);
                let space_win_for_b = band_window_for(len_b, s_a);

                let time_exact_a = TimeInterval::new(t_a, t_a);
                let time_exact_b = TimeInterval::new(t_b, t_b);

                // Probe feasibility before modifying anything.
                let opt_slot_a = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&ra, time_exact_a, space_win_for_a)
                        .next()
                });

                let opt_slot_b = txn.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&rb, time_exact_b, space_win_for_b)
                        .next()
                });

                // Require both sides to be placeable to avoid partial changes.
                let (Some(slot_a), Some(slot_b)) = (opt_slot_a, opt_slot_b) else {
                    txn.discard();
                    continue;
                };

                // Apply the swap: unassign both, assign into the found slots.
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
            b.build()
        })
    }
}
