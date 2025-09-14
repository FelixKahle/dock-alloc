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

pub struct BandRepackOperator<T, C, Q> {
    pub attempts: usize,
    _p: core::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for BandRepackOperator<T, C, Q>
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

impl<T, C, Q> Operator for BandRepackOperator<T, C, Q>
where
    T: SolverVariable,
    C: SolverVariable + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "BandRepackOperator"
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

                // Pick two random movables to define the band.
                let (Some(a), Some(b)) = txn.with_explorer(|ex| {
                    (
                        ex.iter_movable_assignments().choose(rng),
                        ex.iter_movable_assignments().choose(rng),
                    )
                }) else {
                    return builder.build();
                };

                // Define spatial band [s_lo, s_hi) to *cover both* chosen assignments.
                let sa = a.assignment().start_position();
                let sb = b.assignment().start_position();
                let ea = sa + a.branded_request().length();
                let eb = sb + b.branded_request().length();

                let s_lo = if sa <= sb { sa } else { sb };
                let s_hi = if ea >= eb { ea } else { eb };

                // Collect movables that *start* within [s_lo, s_hi) and fully fit in the band.
                let mut targets = txn.with_explorer(|ex| {
                    ex.iter_movable_assignments()
                        .filter(|x| {
                            let sx = x.assignment().start_position();
                            let exx = sx + x.branded_request().length();
                            sx >= s_lo && exx <= s_hi
                        })
                        .collect::<Vec<_>>()
                });

                if targets.is_empty() {
                    txn.discard();
                    continue;
                }

                // Repack in a stable, sensible order: by start_time, then by start_position.
                targets.sort_by_key(|x| {
                    (x.assignment().start_time(), x.assignment().start_position())
                });

                let mut changed = false;
                let mut aborted = false;

                for x in targets {
                    let req = x.branded_request();
                    let t = x.assignment().start_time();
                    let cur_s = x.assignment().start_position();

                    // Time is fixed; space is band. Ask for leftmost feasible slot at time t.
                    let time_win = TimeInterval::new(t, t);
                    let space_win = SpaceInterval::new(s_lo, s_hi);

                    let leftmost = txn.with_explorer(|ex| {
                        ex.iter_slots_for_request_within(&req, time_win, space_win)
                            .min_by_key(|s| s.slot().space().start())
                    });

                    let Some(slot) = leftmost else {
                        continue;
                    };

                    // If it's not to the left of current start, skip.
                    if slot.slot().space().start() >= cur_s {
                        continue;
                    }

                    if txn.propose_unassign(&x).is_err() {
                        aborted = true;
                        break;
                    }
                    if txn.propose_assign(&req, slot).is_err() {
                        aborted = true;
                        break;
                    }
                    changed = true;
                }

                if aborted {
                    txn.discard();
                    continue;
                }
                if changed {
                    txn.commit();
                    return builder.build();
                }

                txn.discard();
            }

            builder.build()
        })
    }
}
