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
    _p: core::marker::PhantomData<(T, C, Q)>,
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
            _p: core::marker::PhantomData,
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

                let (Some(a), Some(b)) = txn.with_explorer(|ex| {
                    (
                        ex.iter_movable_assignments().choose(rng),
                        ex.iter_movable_assignments().choose(rng),
                    )
                }) else {
                    return builder.build();
                };

                let ta = a.assignment().start_time();
                let tb = b.assignment().start_time();
                let (t_lo, t_hi) = if ta <= tb { (ta, tb) } else { (tb, ta) };

                let mut within: Vec<_> = txn.with_explorer(|ex| {
                    ex.iter_movable_assignments()
                        .filter(|x| {
                            let t = x.assignment().start_time();
                            t >= t_lo && t <= t_hi
                        })
                        .collect()
                });

                if within.is_empty() {
                    txn.discard();
                    continue;
                }

                within.sort_by_key(|x| x.assignment().start_time());

                let mut changed = false;
                let mut aborted = false;

                for x in within {
                    let req = x.branded_request();
                    let cur_t = x.assignment().start_time();
                    let cur_s = x.assignment().start_position();
                    let len = req.length();

                    if cur_t <= req.arrival_time() {
                        continue;
                    }

                    let time_window = TimeInterval::new(req.arrival_time(), cur_t);
                    let space_window = SpaceInterval::new(cur_s, cur_s + len);

                    let best_earlier = txn.with_explorer(|ex| {
                        ex.iter_slots_for_request_within(&req, time_window, space_window)
                            .min_by_key(|s| s.slot().start_time())
                    });

                    let Some(slot) = best_earlier else {
                        continue;
                    };
                    if slot.slot().start_time() >= cur_t {
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
                } else {
                    txn.discard();
                    continue;
                }
            }

            builder.build()
        })
    }
}
