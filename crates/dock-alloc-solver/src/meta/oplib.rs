// crates/dock-alloc-solver/src/meta/op_destroy_repair.rs

use crate::{
    berth::quay::QuayRead,
    framework::planning::{Plan, PlanningContext},
    meta::operator::Operator,
};
use dock_alloc_core::{
    space::{SpaceInterval, SpacePosition},
    time::{TimeInterval, TimePoint},
};
use num_traits::{PrimInt, Signed, Zero};
use rand::{Rng, rngs::StdRng};

pub struct RandomSwapOperator<T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    pub attempts: usize, // how many random pairs to try before giving up
    _phantom: std::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for RandomSwapOperator<T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            attempts: 8,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for RandomSwapOperator<T, C, Q>
where
    T: PrimInt + Signed + Zero + Send + Sync,
    C: PrimInt + Signed + Send + Sync + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "RandomSwap"
    }

    fn propose<'p, 'al, 'bo>(
        &self,
        _iteration: usize,
        rng: &mut StdRng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            // Snapshot current movable assignments.
            let asgs = b.with_explorer(|ex| ex.iter_movable_assignments().collect::<Vec<_>>());
            let n = asgs.len();
            if n < 2 {
                return b.build();
            }

            for _try in 0..self.attempts {
                // Pick two distinct random indices.
                let i = rng.random_range(0..n);
                let mut j = rng.random_range(0..n);
                if n > 2 {
                    while j == i {
                        j = rng.random_range(0..n);
                    }
                } else if j == i {
                    j = (j + 1) % n;
                }

                let a = asgs[i].clone();
                let bmv = asgs[j].clone();

                // Extract geometry and requests.
                let a_req = a.assignment().request();
                let b_req = bmv.assignment().request();

                let a_len = a_req.length();
                let b_len = b_req.length();
                let a_proc = a_req.processing_duration();
                let b_proc = b_req.processing_duration();

                // Quick necessary condition: rectangles must be identical in size.
                if a_len != b_len || a_proc != b_proc {
                    continue;
                }

                let a_t = a.assignment().start_time();
                let a_s = a.assignment().start_position();

                let b_t = bmv.assignment().start_time();
                let b_s = bmv.assignment().start_position();

                // Feasible-time checks: arrival constraint (Explorer will clamp too,
                // but we want to avoid staging an impossible swap).
                if b_t < a_req.arrival_time() || a_t < b_req.arrival_time() {
                    continue;
                }

                // Feasible-space checks: each start position must be inside the other's
                // feasible window for its entire length.
                let a_win = a_req.feasible_space_window();
                let b_win = b_req.feasible_space_window();

                let a_target_ok = a_win.contains(b_s) && a_win.end() >= b_s + a_len;
                let b_target_ok = b_win.contains(a_s) && b_win.end() >= a_s + b_len;

                if !(a_target_ok && b_target_ok) {
                    continue;
                }

                // Looks feasible: perform the swap by unassigning both and reassigning crosswise.
                // Unassign A → RegionA
                let reg_a = match b.propose_unassign(&a) {
                    Ok(r) => r,
                    Err(_) => continue,
                };
                // Unassign B → RegionB
                let reg_b = match b.propose_unassign(&bmv) {
                    Ok(r) => r,
                    Err(_) => {
                        // We already unassigned A; at this point we can't roll back,
                        // but with the pre-checks above this path should be extremely rare.
                        // Return a no-op plan by just building; the meta engine validation
                        // will likely reject a partially-unassigned plan, so avoid falling here.
                        return b.build();
                    }
                };

                // Re-fetch branded requests now that they're unassigned.
                let a_id = a.id();
                let b_id = bmv.id();

                let a_req_b = match b
                    .with_explorer(|ex| ex.iter_unassigned_requests().find(|r| r.id() == a_id))
                {
                    Some(r) => r,
                    None => return b.build(),
                };
                let b_req_a = match b
                    .with_explorer(|ex| ex.iter_unassigned_requests().find(|r| r.id() == b_id))
                {
                    Some(r) => r,
                    None => return b.build(),
                };

                // Assign A at B's old rectangle (must be inside RegionB).
                if b.propose_assign_at(&a_req_b, &reg_b, b_t, b_s).is_err() {
                    return b.build();
                }
                // Assign B at A's old rectangle (must be inside RegionA).
                if b.propose_assign_at(&b_req_a, &reg_a, a_t, a_s).is_err() {
                    return b.build();
                }

                // Success — we performed exactly two unassigns and two assigns.
                return b.build();
            }

            // No feasible pair found → no-op plan.
            b.build()
        })
    }
}

pub struct RandomDestroyRepairOperator<T, C, Q>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    pub remove_frac: f64,
    pub min_remove: usize,
    pub max_remove: Option<usize>,
    pub horizon_end: T,
    _phantom: std::marker::PhantomData<(T, C, Q)>,
}

impl<T, C, Q> Default for RandomDestroyRepairOperator<T, C, Q>
where
    T: PrimInt + Signed + Zero,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            remove_frac: 0.10,
            min_remove: 1,
            max_remove: None,
            horizon_end: num_traits::cast::<i64, T>(10_000).unwrap_or(T::zero()),
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T, C, Q> Operator for RandomDestroyRepairOperator<T, C, Q>
where
    T: PrimInt + Signed + Zero + Send + Sync,
    C: PrimInt + Signed + Send + Sync + TryFrom<T> + TryFrom<usize>,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;

    fn name(&self) -> &'static str {
        "RandomDestroyRepairPeekSafe"
    }

    fn propose<'p, 'al, 'bo>(
        &self,
        _iteration: usize,
        rng: &mut StdRng,
        ctx: PlanningContext<'p, 'al, 'bo, Self::Time, Self::Cost, Self::Quay>,
    ) -> Plan<'p, Self::Time, Self::Cost> {
        ctx.with_builder(|mut b| {
            // Snapshot current movable assignments (valid only within this builder)
            let assignments =
                b.with_explorer(|ex| ex.iter_movable_assignments().collect::<Vec<_>>());
            let n = assignments.len();
            if n == 0 {
                return b.build();
            }

            // How many to consider
            let frac = self.remove_frac.clamp(0.0, 1.0);
            let mut k = ((n as f64) * frac).round() as usize;
            k = k.clamp(self.min_remove.min(n), n);
            if let Some(mx) = self.max_remove {
                k = k.min(mx.min(n));
            }
            if k == 0 {
                return b.build();
            }

            // Sample k indices without replacement
            let mut idxs: Vec<usize> = (0..n).collect();
            for i in 0..k {
                let j = rng.random_range(i..n);
                idxs.swap(i, j);
            }

            // Global search window
            let quay_len = b.problem().quay_length().value();
            let space_window =
                SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(quay_len));
            let time_window =
                TimeInterval::new(TimePoint::new(T::zero()), TimePoint::new(self.horizon_end));

            let mut any_change = false;

            for &ix in idxs.iter().take(k) {
                let picked = assignments[ix].clone(); // BrandedMovableAssignment (assigned)
                let rid = picked.id();
                let old_t = picked.start_time();
                let old_s = picked.start_position();

                // 1) PEAK: Find an alternative slot for the **assigned** request (by id).
                let Some(req_assigned) =
                    b.with_explorer(|ex| ex.iter_assigned_requests().find(|r| r.id() == rid))
                else {
                    continue; // Shouldn't happen, but safe to skip.
                };

                let alt_slot = b.with_explorer(|ex| {
                    ex.iter_slots_for_request_within(&req_assigned, time_window, space_window)
                        .find(|slot| {
                            let s = slot.slot().space().start();
                            let t = slot.slot().start_time();
                            s != old_s || t != old_t
                        })
                });

                // If no alternative slot, don’t touch this one
                let Some(new_slot) = alt_slot else { continue };

                // 2) DESTROY (stage): Unassign and keep the freed region
                let Ok(region) = b.propose_unassign(&picked) else {
                    // Could not free -> skip this one
                    continue;
                };

                // IMPORTANT: After unassign, re-fetch the **UNASSIGNED** request handle
                // to avoid using a stale "assigned" brand.
                let Some(req_unassigned) =
                    b.with_explorer(|ex| ex.iter_unassigned_requests().find(|r| r.id() == rid))
                else {
                    // Could not see it as unassigned (?) — restore original placement
                    let _ = b.propose_assign_at(&req_assigned, &region, old_t, old_s);
                    continue;
                };

                // 3) REPAIR (stage): Assign to the new slot; if it fails, restore.
                if b.propose_assign(&req_unassigned, new_slot).is_ok() {
                    any_change = true;
                } else {
                    // Restore the exact original placement inside the freed region
                    let _ = b.propose_assign_at(&req_unassigned, &region, old_t, old_s);
                }
            }

            // Return truly empty plan if nothing changed
            if !any_change {
                return ctx.with_builder(|bb| bb.build());
            }

            b.build()
        })
    }
}
