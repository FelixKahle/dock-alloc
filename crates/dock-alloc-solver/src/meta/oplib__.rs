// ========== 11) WindowRuinRecreate ==========

pub struct WindowRuinRecreate<T, C, Q> {
    pub window_secs: T,
    pub sample: usize,
    pub horizon_end: TimePoint<T>,
    _phantom: core::marker::PhantomData<(C, Q)>,
}
impl<T, C, Q> Default for WindowRuinRecreate<T, C, Q>
where
    T: PrimInt + Signed + Zero,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            window_secs: T::from(3600).unwrap_or(T::zero()),
            sample: 32,
            horizon_end: T::from(10_000).unwrap_or(T::zero()),
            _phantom: core::marker::PhantomData,
        }
    }
}
impl<T, C, Q> Operator for WindowRuinRecreate<T, C, Q>
where
    T: SolverVariable + Zero + Send + Sync,
    C: SolverVariable + TryFrom<T> + TryFrom<usize> + Send + Sync,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;
    fn name(&self) -> &'static str {
        "WindowRuinRecreate"
    }

    #[instrument(level = "info", skip_all)]
    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        rng: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let mut tx = b.begin();
            // pick a random center time in [0, horizon] and define a window
            let gw = global_time_window(&tx, self.horizon_end);
            let start0 = gw.start().value();
            let end0 = gw.end().value();
            if end0 <= start0 {
                return b.build();
            }
            let center = TimePoint::new(
                start0
                    + T::from(
                        rng.random_range(
                            0..usize::try_from((end0 - start0).max(T::zero()))
                                .ok()
                                .unwrap_or(1),
                        ),
                    )
                    .unwrap_or(start0),
            );
            let w_lo = TimePoint::new(center.value().saturating_sub(self.window_secs));
            let w_hi = TimePoint::new(center.value() + self.window_secs);
            let win = TimeInterval::new(w_lo, w_hi);

            // collect assignments in window
            let victims: Vec<_> = tx.with_explorer(|ex| {
                ex.iter_movable_assignments()
                    .filter(|m| {
                        let st = m.start_time();
                        st >= win.start() && st < win.end()
                    })
                    .take(self.sample)
                    .collect()
            });
            if victims.is_empty() {
                return b.build();
            }

            // unassign all
            let mut reqs = Vec::with_capacity(victims.len());
            let mut regions = Vec::with_capacity(victims.len());
            for m in victims {
                let req = m.branded_request();
                if let Ok(reg) = tx.propose_unassign(&m) {
                    reqs.push(req);
                    regions.push((reg, m.start_time(), m.start_position()));
                }
            }

            // greedy reinsert by rising waiting-cost
            for req in reqs {
                let (t_w, s_w) = req_windows(&req, gw, req.feasible_space_window());
                // simply take first available improving slot; if none, try original region best-effort
                let mut chosen = None;
                tx.with_explorer(|ex| {
                    for s in ex.iter_slots_for_request_within(&req, t_w, s_w) {
                        chosen = Some(s);
                        break;
                    }
                });
                if let Some(slot) = chosen {
                    let _ = tx.propose_assign(&req, slot);
                } else if let Some((reg, ot, os)) = regions.pop() {
                    let _ = tx.propose_assign_at(&req, &reg, ot, os);
                }
            }

            if tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}

// ========== 12) MultiRelocateShaker ==========

pub struct MultiRelocateShaker<T, C, Q> {
    pub relocations: usize,
    pub local_time_radius: T,
    pub local_space_radius: usize,
    _phantom: core::marker::PhantomData<(C, Q)>,
}
impl<T, C, Q> Default for MultiRelocateShaker<T, C, Q>
where
    T: PrimInt + Signed + Zero,
    C: PrimInt + Signed,
    Q: QuayRead,
{
    fn default() -> Self {
        Self {
            relocations: 3,
            local_time_radius: T::from(900).unwrap_or(T::zero()),
            local_space_radius: 256,
            _phantom: core::marker::PhantomData,
        }
    }
}
impl<T, C, Q> Operator for MultiRelocateShaker<T, C, Q>
where
    T: SolverVariable + Zero + Send + Sync,
    C: SolverVariable + TryFrom<T> + TryFrom<usize> + Send + Sync,
    Q: QuayRead + Send + Sync,
{
    type Time = T;
    type Cost = C;
    type Quay = Q;
    fn name(&self) -> &'static str {
        "MultiRelocateShaker"
    }

    #[instrument(level = "info", skip_all)]
    fn propose<'p, 'al, 'bo>(
        &self,
        _: usize,
        _: &mut ChaCha8Rng,
        ctx: PlanningContext<'p, 'al, 'bo, T, C, Q>,
    ) -> Plan<'p, T, C> {
        ctx.with_builder(|mut b| {
            let quay_len = b.problem().quay_length().value();
            let mut tx = b.begin();
            let mut done = 0usize;

            tx.with_explorer(|ex| {
                for cur in ex.iter_movable_assignments() {
                    if done >= self.relocations {
                        break;
                    }
                    let req = cur.branded_request();
                    let old_cost = cur.assignment().cost();
                    let old_t = cur.start_time();
                    let old_s = cur.start_position();

                    // local windows
                    let s_min =
                        SpacePosition::new(old_s.value().saturating_sub(self.local_space_radius));
                    let s_max =
                        SpacePosition::new((old_s.value() + self.local_space_radius).min(quay_len));
                    let band = SpaceInterval::new(s_min, s_max);
                    let fw = req.feasible_space_window();
                    let s_w = fw.intersection(&band).unwrap_or(fw);
                    let arr = req.arrival_time();
                    let t_lo =
                        core::cmp::max(arr, TimePoint::new(old_t.value() - self.local_time_radius));
                    let t_hi = TimePoint::new(old_t.value() + self.local_time_radius);
                    if t_lo >= t_hi {
                        continue;
                    }
                    let t_w = TimeInterval::new(t_lo, t_hi);

                    // best improving nearby
                    if let Some((_d, slot)) = best_improving_slot(&tx, &req, t_w, s_w, old_cost, 64)
                    {
                        // try the relocation
                        if tx.propose_unassign(&cur).is_ok()
                            && tx.propose_assign(&req, slot).is_ok()
                        {
                            done += 1;
                        }
                    }
                }
            });

            if done > 0 && tx.with_explorer(|ex| ex.iter_unassigned_requests().next().is_none()) {
                tx.commit();
            }
            b.build()
        })
    }
}
