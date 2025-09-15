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
    berth::{
        berthocc::BerthOccupancy,
        commit::BerthOverlayCommit,
        domain::{FreeRegion, FreeSlot},
        iter::{FeasibleRegionIter, FreeSlotIter, OverlayRunsIter, runs_cover_interval},
        operations::{FreeOperation, OccupyOperation, Operation},
        quay::{QuayRead, QuaySpaceIntervalOutOfBoundsError},
        slice::SliceView,
    },
    container::intervalset::IntervalSet,
    domain::SpaceTimeRectangle,
};
use dock_alloc_core::{
    SolverVariable,
    marker::Brand,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimeInterval, TimePoint},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    iter::{Copied, FusedIterator, Peekable},
};
use std::{
    fmt::Debug,
    ops::Bound::{Excluded, Unbounded},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BrandedFreeSlot<'brand, T>
where
    T: SolverVariable,
{
    slot: FreeSlot<T>,
    _brand: Brand<'brand>,
}

impl<'brand, T> BrandedFreeSlot<'brand, T>
where
    T: SolverVariable,
{
    #[inline]
    fn new(slot: FreeSlot<T>) -> Self {
        Self {
            slot,
            _brand: Brand::default(),
        }
    }

    #[inline]
    pub fn slot(&self) -> &FreeSlot<T> {
        &self.slot
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BrandedFreeRegion<'brand, T>
where
    T: SolverVariable,
{
    region: FreeRegion<T>,
    _brand: Brand<'brand>,
}

impl<'brand, T> BrandedFreeRegion<'brand, T>
where
    T: SolverVariable,
{
    #[inline]
    fn new(region: FreeRegion<T>) -> Self {
        Self {
            region,
            _brand: Brand::default(),
        }
    }

    #[inline]
    pub fn region(&self) -> &FreeRegion<T> {
        &self.region
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BerthOccupancyOverlay<'brand, 'a, T, Q>
where
    T: SolverVariable,
    Q: QuayRead,
{
    berth_occupancy: &'a BerthOccupancy<T, Q>,
    free_by_time: BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    occupied_by_time: BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    barrier_free_times: BTreeSet<TimePoint<T>>,
    barrier_occupied_times: BTreeSet<TimePoint<T>>,
    operations: Vec<Operation<T>>,
    _brand: Brand<'brand>,
}

impl<'brand, 'a, T, Q> SliceView<T> for BerthOccupancyOverlay<'brand, 'a, T, Q>
where
    T: SolverVariable,
    Q: QuayRead,
{
    type FreeRunsIter<'s>
        = OverlayRunsIter<<Q as QuayRead>::FreeIter<'s>>
    where
        Self: 's;

    #[inline]
    fn pred(&self, tp: TimePoint<T>) -> Option<TimePoint<T>> {
        let base = self.berth_occupancy.slice_predecessor_timepoint(tp);
        let free = self.free_by_time.range(..tp).next_back().map(|(t, _)| *t);
        let occ = self
            .occupied_by_time
            .range(..tp)
            .next_back()
            .map(|(t, _)| *t);
        let barf = self.barrier_free_times.range(..tp).next_back().copied();
        let baro = self.barrier_occupied_times.range(..tp).next_back().copied();
        [base, free, occ, barf, baro].into_iter().flatten().max()
    }

    #[inline]
    fn next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>> {
        self.overlay_next_key_after(after)
    }

    #[inline]
    fn has_key_at(&self, t: TimePoint<T>) -> bool {
        self.free_by_time.contains_key(&t)
            || self.occupied_by_time.contains_key(&t)
            || self.barrier_free_times.contains(&t)
            || self.barrier_occupied_times.contains(&t)
            || self.berth_occupancy.has_key_at(t)
    }

    fn free_runs_at(&self, time_point: TimePoint<T>) -> Self::FreeRunsIter<'_> {
        let last_free_barrier = self
            .barrier_free_times
            .range(..=time_point)
            .next_back()
            .copied();
        let last_occ_barrier = self
            .barrier_occupied_times
            .range(..=time_point)
            .next_back()
            .copied();

        fn last_effective<TimeType: SolverVariable>(
            map: &BTreeMap<TimePoint<TimeType>, SpaceIntervalSet>,
            tp: TimePoint<TimeType>,
            last_barrier: Option<TimePoint<TimeType>>,
        ) -> Option<(TimePoint<TimeType>, &SpaceIntervalSet)> {
            let (k_ref, set) = map.range(..=tp).next_back()?;
            let k = *k_ref;
            if let Some(b) = last_barrier
                && b > k
            {
                return None;
            }
            Some((k, set))
        }

        let free_eff = last_effective(&self.free_by_time, time_point, last_free_barrier);
        let occ_eff = last_effective(&self.occupied_by_time, time_point, last_occ_barrier);

        // If overlay has no effect for this tp, defer to base directly.
        if free_eff.is_none() && occ_eff.is_none() {
            return OverlayRunsIter::Base(self.berth_occupancy.free_runs_at(time_point));
        }

        // Start from base free runs at this timepoint.
        let base_iter = self.berth_occupancy.free_runs_at(time_point);
        let (lo, hi) = base_iter.size_hint();
        let est_base = hi.unwrap_or(lo);

        let mut runs = SpaceIntervalSet::with_capacity(est_base);
        runs.clear_and_fill_from_iter(base_iter);

        // Apply overlay precedence:
        //  - If newest change is FREE (kf > ko): (R \ O) ∪ F
        //  - Else (including tie kf == ko):     (R ∪ F) \ O   → occupy wins on overlap at same key
        match (free_eff, occ_eff) {
            (Some((kf, fset)), Some((ko, oset))) if kf > ko => {
                let mut tmp = SpaceIntervalSet::with_capacity(runs.len());
                runs.subtract_into(oset, &mut tmp);
                core::mem::swap(&mut runs, &mut tmp);
                tmp.clear();
                runs.union_into(fset, &mut tmp);
                core::mem::swap(&mut runs, &mut tmp);
            }
            _ => {
                if let Some((_, fset)) = free_eff {
                    let mut tmp = SpaceIntervalSet::with_capacity(runs.len() + fset.len());
                    runs.union_into(fset, &mut tmp);
                    core::mem::swap(&mut runs, &mut tmp);
                }
                if let Some((_, oset)) = occ_eff {
                    let mut tmp = SpaceIntervalSet::with_capacity(runs.len());
                    runs.subtract_into(oset, &mut tmp);
                    core::mem::swap(&mut runs, &mut tmp);
                }
            }
        }

        OverlayRunsIter::Owned(runs.into_intervals().into_iter())
    }
}

type SpaceIntervalSet = IntervalSet<SpacePosition>;

#[derive(Clone, Debug)]
struct KeysUnion<'a, T: SolverVariable> {
    free_keys:
        Peekable<Copied<std::collections::btree_map::Keys<'a, TimePoint<T>, SpaceIntervalSet>>>,
    occupied_keys:
        Peekable<Copied<std::collections::btree_map::Keys<'a, TimePoint<T>, SpaceIntervalSet>>>,
}

impl<'a, T: SolverVariable> KeysUnion<'a, T> {
    #[inline]
    fn new(
        free: &'a BTreeMap<TimePoint<T>, SpaceIntervalSet>,
        occ: &'a BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    ) -> Self {
        Self {
            free_keys: free.keys().copied().peekable(),
            occupied_keys: occ.keys().copied().peekable(),
        }
    }
}

impl<'a, T: SolverVariable> Iterator for KeysUnion<'a, T> {
    type Item = TimePoint<T>;
    fn next(&mut self) -> Option<Self::Item> {
        let free_key = self.free_keys.peek().copied();
        let occupied_key = self.occupied_keys.peek().copied();

        match (free_key, occupied_key) {
            (None, None) => None,
            (Some(_), None) => self.free_keys.next(),
            (None, Some(_)) => self.occupied_keys.next(),
            (Some(key1), Some(key2)) => match key1.cmp(&key2) {
                std::cmp::Ordering::Less => self.free_keys.next(),
                std::cmp::Ordering::Greater => self.occupied_keys.next(),
                std::cmp::Ordering::Equal => {
                    self.free_keys.next();
                    self.occupied_keys.next();
                    Some(key1)
                }
            },
        }
    }
}

impl<'a, T: SolverVariable> FusedIterator for KeysUnion<'a, T> {}

impl<'brand, 'a, T, Q> BerthOccupancyOverlay<'brand, 'a, T, Q>
where
    T: SolverVariable,
    Q: QuayRead,
{
    /// Creates a new, empty overlay for a given `BerthOccupancy`.
    #[inline]
    pub(crate) fn new(berth_occupancy: &'a BerthOccupancy<T, Q>) -> Self {
        Self {
            berth_occupancy,
            free_by_time: BTreeMap::new(),
            occupied_by_time: BTreeMap::new(),
            barrier_free_times: BTreeSet::new(),
            barrier_occupied_times: BTreeSet::new(),
            operations: Vec::new(),
            _brand: Brand::new(),
        }
    }

    /// Returns a reference to the underlying `BerthOccupancy`.
    #[inline]
    pub fn berth(&self) -> &'a BerthOccupancy<T, Q> {
        self.berth_occupancy
    }

    #[inline]
    pub fn operations(&self) -> &[Operation<T>] {
        &self.operations
    }

    #[inline]
    pub fn clear(&mut self) {
        self.free_by_time.clear();
        self.occupied_by_time.clear();
        self.barrier_free_times.clear();
        self.barrier_occupied_times.clear();
        self.operations.clear();
    }

    #[inline]
    pub fn absorb(&mut self, child: Self) {
        debug_assert!(std::ptr::eq(self.berth_occupancy, child.berth_occupancy));
        *self = child;
    }

    /// Records an occupied space at a specific time point in the overlay.
    #[inline]
    fn add_occupy(
        &mut self,
        time: TimePoint<T>,
        space: SpaceInterval,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        if !self.berth().space_within_quay(space) {
            return Err(QuaySpaceIntervalOutOfBoundsError::new(
                space,
                self.berth().quay_length(),
            ));
        }
        if space.is_empty() {
            return Ok(());
        }

        // If this space was marked as free in the overlay, un-mark it.
        if let Some(free_set) = self.free_by_time.get_mut(&time) {
            free_set.subtract_interval(space);
            if free_set.is_empty() {
                self.free_by_time.remove(&time);
            }
        }

        // Add the space to the set of occupied regions for this time point.
        self.occupied_by_time
            .entry(time)
            .or_default()
            .insert_and_coalesce(space);
        Ok(())
    }

    /// Marks a spatio-temporal rectangle as occupied in the overlay.
    pub fn occupy(
        &mut self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        if !self.berth().space_within_quay(rect.space()) {
            return Err(QuaySpaceIntervalOutOfBoundsError::new(
                rect.space(),
                self.berth().quay_length(),
            ));
        }

        let time = rect.time();
        let space = rect.space();
        let start = time.start();
        let end = time.end();

        // apply at start
        self.add_occupy(start, space)?;

        // collect interior union keys first (avoid borrowing self during mutation)
        let interior_keys: Vec<_> = self
            .covering_timepoints_union(time)
            .filter(|&tp| tp > start && tp < end)
            .collect();

        for tp in interior_keys {
            self.add_occupy(tp, space)?;
        }

        self.barrier_occupied_times.insert(end);

        // record
        self.operations
            .push(Operation::Occupy(OccupyOperation::new(*rect)));

        Ok(())
    }

    /// Records a free space at a specific time point in the overlay.
    #[inline]
    fn add_free(
        &mut self,
        time: TimePoint<T>,
        space: SpaceInterval,
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        if !self.berth().space_within_quay(space) {
            return Err(QuaySpaceIntervalOutOfBoundsError::new(
                space,
                self.berth().quay_length(),
            ));
        }
        if space.is_empty() {
            return Ok(());
        }

        // If this space was marked as occupied in the overlay, un-mark it.
        if let Some(occupied_set) = self.occupied_by_time.get_mut(&time) {
            occupied_set.subtract_interval(space);
            if occupied_set.is_empty() {
                self.occupied_by_time.remove(&time);
            }
        }

        // Add the space to the set of freed regions for this time point.
        self.free_by_time
            .entry(time)
            .or_default()
            .insert_and_coalesce(space);
        Ok(())
    }

    /// Marks a spatio-temporal rectangle as free in the overlay.
    pub fn free(
        &mut self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<BrandedFreeRegion<'brand, T>, QuaySpaceIntervalOutOfBoundsError> {
        if !self.berth().space_within_quay(rect.space()) {
            return Err(QuaySpaceIntervalOutOfBoundsError::new(
                rect.space(),
                self.berth().quay_length(),
            ));
        }

        let time = rect.time();
        let space = rect.space();
        let start = time.start();
        let end = time.end();

        // apply at start
        self.add_free(start, space)?;

        // collect interior union keys first (avoid borrowing self during mutation)
        let interior_keys: Vec<_> = self
            .covering_timepoints_union(time)
            .filter(|&tp| tp > start && tp < end)
            .collect();

        for tp in interior_keys {
            self.add_free(tp, space)?;
        }

        // stop carrying at end
        self.barrier_free_times.insert(end);

        // record
        self.operations
            .push(Operation::Free(FreeOperation::new(*rect)));
        Ok(BrandedFreeRegion::new(FreeRegion::new(*rect)))
    }

    /// Creates an iterator that merges keys from the base timeline, overlay maps, and barriers.
    fn covering_timepoints_union(
        &self,
        time_interval: TimeInterval<T>,
    ) -> impl Iterator<Item = TimePoint<T>> + '_ {
        let start = time_interval.start();
        let end = time_interval.end();

        let base_pred = self.berth().slice_predecessor_timepoint(start);
        let free_pred = self
            .free_by_time
            .range(..=start)
            .next_back()
            .map(|(t, _)| *t);
        let occ_pred = self
            .occupied_by_time
            .range(..=start)
            .next_back()
            .map(|(t, _)| *t);
        let barf_pred = self.barrier_free_times.range(..=start).next_back().copied();
        let baro_pred = self
            .barrier_occupied_times
            .range(..=start)
            .next_back()
            .copied();
        let pred = [base_pred, free_pred, occ_pred, barf_pred, baro_pred]
            .into_iter()
            .flatten()
            .max();

        let base_keys = pred
            .into_iter()
            .chain(self.berth().slices(start, end).interior_keys())
            .peekable();

        let overlay_keys = KeysUnion::new(&self.free_by_time, &self.occupied_by_time)
            .filter(move |&t| t >= start && t < end)
            .peekable();

        // merged barrier iterator (free ∪ occupy)
        let mut b_f = self
            .barrier_free_times
            .range(start..end)
            .copied()
            .peekable();
        let mut b_o = self
            .barrier_occupied_times
            .range(start..end)
            .copied()
            .peekable();
        let merged_barriers =
            std::iter::from_fn(move || match (b_f.peek().copied(), b_o.peek().copied()) {
                (None, None) => None,
                (Some(x), None) => {
                    b_f.next();
                    Some(x)
                }
                (None, Some(y)) => {
                    b_o.next();
                    Some(y)
                }
                (Some(x), Some(y)) => {
                    if x <= y {
                        b_f.next();
                        if x == y {
                            b_o.next();
                        }
                        Some(x)
                    } else {
                        b_o.next();
                        Some(y)
                    }
                }
            })
            .peekable();

        // merge base_keys, overlay_keys, merged_barriers (dedup)
        std::iter::from_fn({
            let mut a = base_keys;
            let mut b = overlay_keys;
            let mut c = merged_barriers;
            let mut last: Option<TimePoint<T>> = None;

            move || loop {
                let na = a.peek().copied();
                let nb = b.peek().copied();
                let nc = c.peek().copied();
                let next = [na, nb, nc].into_iter().flatten().min();
                match next {
                    None => return None,
                    Some(x) => {
                        if na == Some(x) {
                            a.next();
                        }
                        if nb == Some(x) {
                            b.next();
                        }
                        if nc == Some(x) {
                            c.next();
                        }
                        if last != Some(x) {
                            last = Some(x);
                            return last;
                        }
                    }
                }
            }
        })
    }

    /// Checks if a given spatio-temporal rectangle is completely free, considering the overlay.
    pub fn is_free(
        &self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        let time_interval = rect.time();
        let space_interval = rect.space();

        if !self.berth().space_within_quay(space_interval) {
            return Err(QuaySpaceIntervalOutOfBoundsError::new(
                space_interval,
                self.berth().quay_length(),
            ));
        }

        if rect.is_empty() {
            return Ok(true);
        }

        Ok(self
            .covering_timepoints_union(time_interval)
            .all(|tp| runs_cover_interval(self.free_runs_at(tp), space_interval)))
    }

    /// Checks if a given spatio-temporal rectangle is occupied, considering the overlay.
    #[inline]
    pub fn is_occupied(
        &self,
        rect: &SpaceTimeRectangle<T>,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        Ok(!self.is_free(rect)?)
    }

    /// Returns an iterator over all `FreeSlot`s, considering the overlay.
    #[inline]
    #[allow(clippy::type_complexity)]
    pub fn iter_free_slots(
        &self,
        time_window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> core::iter::Map<
        FreeSlotIter<'_, T, BerthOccupancyOverlay<'brand, 'a, T, Q>>,
        fn(FreeSlot<T>) -> BrandedFreeSlot<'brand, T>,
    >
    where
        T: Copy,
    {
        fn brand_slot<'b, Tx: SolverVariable>(x: FreeSlot<Tx>) -> BrandedFreeSlot<'b, Tx> {
            BrandedFreeSlot::new(x)
        }

        FreeSlotIter::new(self, time_window, duration, required_space, space_window)
            .map(brand_slot::<'brand, T>)
    }

    #[inline]
    #[allow(clippy::type_complexity)]
    pub fn iter_free_regions(
        &self,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> core::iter::Map<
        FeasibleRegionIter<'_, T, BerthOccupancyOverlay<'brand, 'a, T, Q>>,
        fn(FreeRegion<T>) -> BrandedFreeRegion<'brand, T>,
    > {
        fn brand_region<'b, Tx: SolverVariable>(r: FreeRegion<Tx>) -> BrandedFreeRegion<'b, Tx> {
            BrandedFreeRegion::new(r)
        }

        FeasibleRegionIter::new(self, window, duration, required_space, space_window)
            .map(brand_region::<'brand, T>)
    }

    /// Finds the next timeline key after a given time point, considering base, overlay, and barriers.
    #[inline]
    fn overlay_next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>> {
        let next_base = self.berth_occupancy.next_time_key_after(after);
        let next_free = self
            .free_by_time
            .range((Excluded(after), Unbounded))
            .next()
            .map(|(t, _)| *t);
        let next_occ = self
            .occupied_by_time
            .range((Excluded(after), Unbounded))
            .next()
            .map(|(t, _)| *t);
        let next_barf = self
            .barrier_free_times
            .range((Excluded(after), Unbounded))
            .next()
            .copied();
        let next_baro = self
            .barrier_occupied_times
            .range((Excluded(after), Unbounded))
            .next()
            .copied();
        [next_base, next_free, next_occ, next_barf, next_baro]
            .into_iter()
            .flatten()
            .min()
    }

    #[inline]
    pub fn into_commit(self) -> BerthOverlayCommit<T> {
        BerthOverlayCommit::new(self.operations)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::berth::{berthocc::BerthOccupancy, operations::Operation, quay::BooleanVecQuay};
    use num_traits::Zero;

    type T = i64;
    type BO = BerthOccupancy<T, BooleanVecQuay>;

    #[inline]
    fn pos(x: usize) -> SpacePosition {
        SpacePosition::new(x)
    }
    #[inline]
    fn len(x: usize) -> SpaceLength {
        SpaceLength::new(x)
    }
    #[inline]
    fn si(a: usize, b: usize) -> SpaceInterval {
        SpaceInterval::new(pos(a), pos(b))
    }
    #[inline]
    fn tp(t: T) -> TimePoint<T> {
        TimePoint::new(t)
    }
    #[inline]
    fn ti(a: T, b: T) -> TimeInterval<T> {
        TimeInterval::new(tp(a), tp(b))
    }
    #[inline]
    fn rect(tw: TimeInterval<T>, si: SpaceInterval) -> SpaceTimeRectangle<T> {
        SpaceTimeRectangle::new(si, tw)
    }

    #[test]
    fn test_overlay_constructs_empty_and_refs_base() {
        let berth = BO::new(len(10));
        let ov = BerthOccupancyOverlay::new(&berth);
        assert_eq!(ov.berth().quay_length(), len(10));
        assert!(ov.operations().is_empty());
    }

    #[test]
    fn test_overlay_add_free_and_add_occupy_affect_queries() {
        let mut berth = BO::new(len(10));
        // Base: occupy [5,10)×[2,6)
        berth.occupy(&rect(ti(5, 10), si(2, 6))).unwrap();

        let mut ov = BerthOccupancyOverlay::new(&berth);

        // At t=5, override a subrange as free via overlay
        ov.add_free(tp(5), si(2, 4)).unwrap();
        assert!(ov.is_free(&rect(ti(5, 10), si(2, 4))).unwrap());
        assert!(ov.is_occupied(&rect(ti(5, 10), si(4, 6))).unwrap());

        // Add an overlay-occupy on otherwise-free area at t=0
        ov.add_occupy(tp(0), si(0, 1)).unwrap();
        assert!(ov.is_occupied(&rect(ti(0, 5), si(0, 1))).unwrap());
        assert!(ov.is_free(&rect(ti(0, 5), si(1, 10))).unwrap());
    }

    #[test]
    fn test_overlay_free_across_timepoints_uses_pred_and_keys() {
        let mut berth = BO::new(len(10));
        // Create a base boundary at t=5 by occupying [2,6)
        berth.occupy(&rect(ti(5, 7), si(2, 6))).unwrap();

        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Free [4,5) across [4,6): will place free at predecessor of 4 (t=0) and at timepoint 5
        ov.free(&rect(ti(4, 6), si(4, 5))).unwrap();
        assert!(ov.is_free(&rect(ti(4, 6), si(4, 5))).unwrap());
    }

    fn collect_overlay_slots(
        ov: &BerthOccupancyOverlay<'_, '_, T, BooleanVecQuay>,
        tw: TimeInterval<T>,
        dur: TimeDelta<T>,
        need: SpaceLength,
        bounds: SpaceInterval,
    ) -> Vec<(T, (usize, usize))> {
        ov.iter_free_slots(tw, dur, need, bounds)
            .map(|bf| {
                let s = bf.slot();
                (
                    s.start_time().value(),
                    (s.space().start().value(), s.space().end().value()),
                )
            })
            .collect()
    }

    #[test]
    fn test_overlay_iter_free_slots_respects_overlay_deltas() {
        // Base: occupy [5,9)×[2,6)
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(5, 9), si(2, 6))).unwrap();
        let mut ov = BerthOccupancyOverlay::new(&berth);

        // Make the blocked band free at pred=0 and at key=5 so duration [5,8) can pass
        ov.add_free(tp(0), si(2, 6)).unwrap();
        ov.add_free(tp(5), si(2, 6)).unwrap();

        let items = collect_overlay_slots(&ov, ti(5, 9), TimeDelta::new(3), len(2), si(0, 10));
        assert!(
            items
                .iter()
                .any(|(t, (a, b))| *t == 5 && *a <= 2 && *b >= 6),
            "Expected a slot at start=5 that covers [2,6)"
        );
    }

    use std::collections::{BTreeMap, BTreeSet};

    fn iv_tuple(iv: SpaceInterval) -> (usize, usize) {
        (iv.start().value(), iv.end().value())
    }
    fn set_from_intervals(v: impl IntoIterator<Item = SpaceInterval>) -> BTreeSet<(usize, usize)> {
        v.into_iter().map(iv_tuple).collect()
    }

    fn collect_overlay_bands(
        ov: &BerthOccupancyOverlay<'_, '_, T, BooleanVecQuay>,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> BTreeMap<(T, T), BTreeSet<(usize, usize)>> {
        let mut out: BTreeMap<(T, T), Vec<SpaceInterval>> = BTreeMap::new();
        for r in ov.iter_free_regions(window, duration, required, bounds) {
            let rr = r.region();
            out.entry((
                rr.rectangle().time().start().value(),
                rr.rectangle().time().end().value(),
            ))
            .or_default()
            .push(rr.rectangle().space());
        }
        out.into_iter()
            .map(|(k, v)| (k, set_from_intervals(v)))
            .collect()
    }

    fn slot_set_for_start_overlay(
        ov: &BerthOccupancyOverlay<'_, '_, T, BooleanVecQuay>,
        s: TimePoint<T>,
        mut duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) -> BTreeSet<(usize, usize)> {
        if duration.value() < T::zero() {
            duration = TimeDelta::new(T::zero());
        }
        let tw = TimeInterval::new(s, s + duration);
        ov.iter_free_slots(tw, duration, required, bounds)
            .filter(|bf| bf.slot().start_time() == s)
            .map(|bf| iv_tuple(bf.slot().space()))
            .collect()
    }

    fn sample_starts_in_band(a: T, b: T) -> Vec<T> {
        if a >= b {
            return vec![];
        }
        let one = num_traits::One::one();
        let mut v = vec![a];
        let span = b - a;
        if span > one {
            v.push(a + (span / (one + one))); // approx midpoint
            v.push(b - one);
            v.sort_unstable();
            v.dedup();
        }
        v
    }

    fn assert_regions_match_slots_overlay(
        ov: &BerthOccupancyOverlay<'_, '_, T, BooleanVecQuay>,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required: SpaceLength,
        bounds: SpaceInterval,
    ) {
        let bands = collect_overlay_bands(ov, window, duration, required, bounds);
        for ((ts, te), spaces) in bands {
            for s in sample_starts_in_band(ts, te) {
                let got =
                    slot_set_for_start_overlay(ov, TimePoint::new(s), duration, required, bounds);
                assert_eq!(
                    got, spaces,
                    "overlay slots at start={} must equal region runs for band [{}, {})",
                    s, ts, te
                );
            }
        }
    }

    #[test]
    fn test_overlay_regions_vs_slots_consistency() {
        let berth = BO::new(len(10));
        let ov = BerthOccupancyOverlay::new(&berth);
        assert_regions_match_slots_overlay(&ov, ti(0, 10), TimeDelta::new(3), len(2), si(0, 10));
    }

    #[test]
    fn test_overlay_regions_vs_slots_with_overlay_keys() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Introduce overlay key at t=7 by occupying [1,3) only in overlay
        ov.add_occupy(tp(7), si(1, 3)).unwrap();
        assert_regions_match_slots_overlay(&ov, ti(5, 10), TimeDelta::new(2), len(1), si(0, 10));
    }

    #[test]
    fn test_overlay_keys_become_candidate_starts_for_slots() {
        let berth = BO::new(len(10)); // fully free; base has only origin
        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Add overlay key at 7
        ov.add_occupy(tp(7), si(0, 1)).unwrap();

        let starts: Vec<_> = ov
            .iter_free_slots(ti(0, 10), TimeDelta::new(2), len(1), si(0, 10))
            .map(|bf| bf.slot().start_time().value())
            .collect();

        let mut uniq = starts.clone();
        uniq.sort_unstable();
        uniq.dedup();
        assert!(uniq.contains(&0));
        assert!(uniq.contains(&7));
    }

    #[test]
    fn test_overlay_changes_at_start_are_applied_when_pred_differs() {
        let mut berth = BO::new(len(10));
        // Base boundary at 7 with occupation [2,6)
        berth.occupy(&rect(ti(7, 9), si(2, 6))).unwrap(); // keys 0,7,9

        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Default occupy at pred=0, but free exactly at window start=5
        ov.add_occupy(tp(0), si(2, 6)).unwrap();
        ov.add_free(tp(5), si(2, 6)).unwrap();

        let items: Vec<_> = ov
            .iter_free_slots(ti(5, 8), TimeDelta::new(2), len(3), si(0, 10))
            .collect();

        assert!(
            items.iter().any(|bf| bf.slot().start_time().value() == 5
                && bf.slot().space().start().value() <= 2
                && bf.slot().space().end().value() >= 6),
            "Expected overlay free at `start=5` to apply to initial slice"
        );
    }

    #[test]
    fn test_overlay_next_key_after_merges_sources() {
        let mut berth = BO::new(len(10));
        // Base keys at 5, 9
        berth.occupy(&rect(ti(5, 9), si(1, 2))).unwrap();

        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Overlay key at 7
        ov.add_free(tp(7), si(0, 1)).unwrap();

        assert_eq!(ov.overlay_next_key_after(tp(0)), Some(tp(5)));
        assert_eq!(ov.overlay_next_key_after(tp(5)), Some(tp(7)));
        assert_eq!(ov.overlay_next_key_after(tp(7)), Some(tp(9)));
        assert_eq!(ov.overlay_next_key_after(tp(9)), None);
    }

    #[test]
    fn test_overlay_records_operations_in_order() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        let r1 = rect(ti(2, 6), si(3, 5));
        let r2 = rect(ti(8, 10), si(1, 2));

        ov.occupy(&r1).unwrap();
        ov.free(&r2).unwrap();

        let ops = ov.operations();
        assert_eq!(ops.len(), 2);
        assert!(matches!(ops[0], Operation::Occupy(_)));
        assert!(matches!(ops[1], Operation::Free(_)));
    }

    #[test]
    fn test_overlay_is_free_out_of_bounds_returns_err() {
        let berth = BO::new(len(8));
        let ov = BerthOccupancyOverlay::new(&berth);

        let out_of_bounds = rect(ti(0, 2), si(7, 9)); // exceeds quay end=8
        let err = ov.is_free(&out_of_bounds).unwrap_err();
        // spot check: error references the offending interval length via Display/Debug not required
        let _ = err; // just assert it returns Err
    }

    #[test]
    fn test_regions_empty_base_single_band() {
        // Fully free quay of length 10
        let berth = BO::new(len(10));
        let ov = BerthOccupancyOverlay::new(&berth);

        // With duration=3, feasible starts are [0,7); space runs should be the whole [0,10)
        assert_regions_match_slots_overlay(&ov, ti(0, 10), TimeDelta::new(3), len(2), si(0, 10));
    }

    #[test]
    fn test_regions_split_by_base_occupy() {
        // Base: occupy [4,9)×[3,7), introducing base keys and a blocked spatial band
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(4, 9), si(3, 7))).unwrap();

        let ov = BerthOccupancyOverlay::new(&berth);

        // Regions should split across the base keys (including predecessor)
        // and in [4,9) the space runs must exclude [3,7).
        assert_regions_match_slots_overlay(&ov, ti(0, 12), TimeDelta::new(2), len(2), si(0, 10));
    }

    #[test]
    fn test_regions_respect_space_window_clipping() {
        // Base is fully free, but we restrict the space window to [3,8).
        let berth = BO::new(len(10));
        let ov = BerthOccupancyOverlay::new(&berth);

        // Required length 3 must fit entirely inside [3,8); slots/regions should reflect this clip.
        assert_regions_match_slots_overlay(&ov, ti(0, 10), TimeDelta::new(2), len(3), si(3, 8));
    }

    #[test]
    fn test_regions_zero_duration() {
        // Duration = 0 should be treated as admissible (degenerate rectangles);
        // regions and slots should still match.
        let berth = BO::new(len(10));
        let ov = BerthOccupancyOverlay::new(&berth);

        assert_regions_match_slots_overlay(&ov, ti(2, 7), TimeDelta::new(0), len(2), si(0, 10));
    }

    #[test]
    fn test_regions_required_space_too_large_yields_empty() {
        // Required space larger than quay/window → no feasible regions.
        let berth = BO::new(len(10));
        let ov = BerthOccupancyOverlay::new(&berth);

        let bands = collect_overlay_bands(&ov, ti(0, 10), TimeDelta::new(3), len(11), si(0, 10));
        assert!(
            bands.is_empty(),
            "Expected no feasible regions when required space exceeds quay/window"
        );
    }

    #[test]
    fn test_regions_with_overlay_free_and_occupy_mix() {
        // Base: occupy middle band to create constraints
        let mut berth = BO::new(len(12));
        berth.occupy(&rect(ti(3, 9), si(4, 8))).unwrap(); // keys 0,3,9

        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Overlay: free a subrange inside the base-occupied band and also add a new occupy elsewhere
        ov.add_free(tp(3), si(5, 7)).unwrap(); // carve a usable corridor inside [4,8)
        ov.add_free(tp(0), si(5, 7)).unwrap(); // predecessor slice must reflect it as well
        ov.add_occupy(tp(6), si(0, 2)).unwrap(); // create a new overlay-only obstacle

        // Check consistency with slots across a window overlapping all keys
        assert_regions_match_slots_overlay(&ov, ti(2, 10), TimeDelta::new(2), len(2), si(0, 12));
    }

    #[test]
    fn test_regions_apply_overlay_change_exactly_at_window_start() {
        // Base boundary at 7 with occupation [2,6)
        let mut berth = BO::new(len(10));
        berth.occupy(&rect(ti(7, 9), si(2, 6))).unwrap(); // keys 0,7,9

        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Occupy at predecessor; free exactly at the window start=5 (overlay-only key)
        ov.add_occupy(tp(0), si(2, 6)).unwrap();
        ov.add_free(tp(5), si(2, 6)).unwrap();

        // Regions should include a band starting at 5 that exposes [2,6)
        assert_regions_match_slots_overlay(&ov, ti(5, 8), TimeDelta::new(2), len(3), si(0, 10));

        // Additionally, ensure at least one region band starts at 5 and contains [2,6)
        let bands = collect_overlay_bands(&ov, ti(5, 8), TimeDelta::new(2), len(3), si(0, 10));
        let has_expected = bands
            .iter()
            .any(|(&(ts, _te), spaces)| ts == 5 && spaces.iter().any(|&(a, b)| a <= 2 && b >= 6));
        assert!(
            has_expected,
            "Expected a region band starting at 5 that includes space interval [2,6)"
        );
    }

    #[test]
    fn test_regions_band_splits_on_overlay_only_key() {
        // Base: fully free, only base origin key
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        // Introduce an overlay-only key at t=6 by occupying a small segment
        ov.add_occupy(tp(6), si(1, 2)).unwrap();

        // Expect region bands to split at t=6 (overlay key) within [0,10)
        assert_regions_match_slots_overlay(&ov, ti(0, 10), TimeDelta::new(2), len(1), si(0, 10));

        // Check that we indeed have bands on both sides of t=6
        let bands = collect_overlay_bands(&ov, ti(0, 10), TimeDelta::new(2), len(1), si(0, 10));
        let left_band_exists = bands.keys().any(|&(ts, te)| ts <= 0 && te > 0 && te <= 6);
        let right_band_exists = bands.keys().any(|&(ts, te)| ts >= 6 && te >= 8);
        assert!(
            left_band_exists && right_band_exists,
            "Expected region bands split by overlay key at t=6"
        );
    }

    #[test]
    fn test_regions_zero_duration_overlay_key_at_start_and_end() {
        let mut b = BO::new(len(10));
        // base keys 0 and 10
        b.occupy(&rect(ti(0, 10), si(9, 10))).unwrap();

        let mut ov = BerthOccupancyOverlay::new(&b);
        // overlay key exactly at window start
        ov.add_occupy(tp(0), si(0, 1)).unwrap();
        // overlay key exactly at window end (should appear as candidate for duration==0)
        ov.add_free(tp(10), si(0, 10)).unwrap();

        // duration 0 over [0,10): expect candidate bands split at 0 and 10 and match slots
        assert_regions_match_slots_overlay(&ov, ti(0, 10), TimeDelta::new(0), len(1), si(0, 10));
    }

    #[test]
    fn test_regions_single_start_with_overlay_pred_and_key_at_start() {
        // Only one admissible start: [5,10), dur=5 -> start must be 5
        let mut b = BO::new(len(10));
        b.occupy(&rect(ti(0, 5), si(0, 1))).unwrap(); // ensures key at 0 and 5

        let mut ov = BerthOccupancyOverlay::new(&b);
        // overlay change exactly at start=5
        ov.add_free(tp(5), si(2, 4)).unwrap();

        let bands = collect_overlay_bands(&ov, ti(5, 10), TimeDelta::new(5), len(1), si(0, 10));
        assert_eq!(bands.len(), 1);
        let ((ts, te), spaces) = bands.into_iter().next().unwrap();
        assert_eq!((ts, te), (5, 6)); // “single-start band”
        let slots = slot_set_for_start_overlay(&ov, tp(5), TimeDelta::new(5), len(1), si(0, 10));
        assert_eq!(spaces, slots);
    }

    #[test]
    fn test_overlay_into_commit_roundtrip_applies_to_base() {
        // Base: empty
        let mut berth = BO::new(len(12));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        let occ = rect(ti(2, 6), si(3, 7));
        let hole = rect(ti(4, 5), si(5, 6));

        // Record operations in overlay (non-destructive to base)
        ov.occupy(&occ).unwrap();
        ov.free(&hole).unwrap();

        // Base unchanged so far
        assert!(berth.is_free(&occ).unwrap());

        // Apply overlay's commit to base, expect same effect as querying overlay
        let commit = ov.into_commit();
        berth.apply(&commit).unwrap();

        // Check base state reflects overlay operations
        assert!(berth.is_occupied(&rect(ti(2, 4), si(3, 5))).unwrap());
        assert!(berth.is_free(&hole).unwrap());
        assert!(berth.is_occupied(&rect(ti(5, 6), si(6, 7))).unwrap());
    }

    #[test]
    fn test_overlay_clear_resets_state_and_operations() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);
        let r = rect(ti(2, 6), si(1, 4));
        ov.occupy(&r).unwrap();
        assert!(ov.is_occupied(&r).unwrap());
        assert_eq!(ov.operations().len(), 1);

        ov.clear();
        // After clear, overlay stops affecting queries; base is free everywhere
        assert!(ov.is_free(&r).unwrap());
        assert!(ov.operations().is_empty());
    }

    #[test]
    fn test_overlay_absorb_replaces_with_child_state() {
        let berth = BO::new(len(12));
        let mut parent = BerthOccupancyOverlay::new(&berth);
        let mut child = BerthOccupancyOverlay::new(&berth);

        let r_parent = rect(ti(1, 3), si(0, 2));
        let r_child = rect(ti(5, 7), si(4, 6));

        parent.occupy(&r_parent).unwrap();
        child.occupy(&r_child).unwrap();

        // absorb() should make parent identical to child (not a merge)
        parent.absorb(child);

        assert!(parent.is_free(&r_parent).unwrap());
        assert!(parent.is_occupied(&r_child).unwrap());

        let ops = parent.operations();
        assert_eq!(ops.len(), 1);
        assert!(matches!(ops[0], Operation::Occupy(_)));
    }

    #[test]
    fn test_overlay_operations_order_with_duplicates() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        let r = rect(ti(2, 6), si(3, 7));
        ov.occupy(&r).unwrap();
        ov.occupy(&r).unwrap(); // duplicate occupy should just union in set
        ov.free(&r).unwrap();

        let ops = ov.operations();
        assert_eq!(ops.len(), 3);
        assert!(matches!(ops[0], Operation::Occupy(_)));
        assert!(matches!(ops[1], Operation::Occupy(_)));
        assert!(matches!(ops[2], Operation::Free(_)));

        // Final overlay view should be free over r (occupied twice, then freed)
        assert!(ov.is_free(&r).unwrap());
    }

    #[test]
    fn test_overlay_occupy_on_empty_base_does_not_leak_past_end() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        let r = rect(ti(2, 6), si(1, 4));
        ov.occupy(&r).unwrap();

        // Past the end should be free again
        assert!(ov.is_free(&rect(ti(6, 8), si(1, 4))).unwrap());
    }

    #[test]
    fn test_tail_window_is_free_in_time_slots_and_regions_exist() {
        type T = i64;
        type BO = BerthOccupancy<T, BooleanVecQuay>;

        // Quay of length 10, occupy something EARLY to set a finite "latest end".
        let mut berth = BO::new(len(10));
        // Base occupancy: [2,6)×[3,5). Latest end = t=6
        berth.occupy(&rect(ti(2, 6), si(3, 5))).unwrap();

        // Overlay with no extra deltas.
        let ov = BerthOccupancyOverlay::new(&berth);

        // Tail starts strictly AFTER the latest base end.
        let tail_start = tp(7);
        let tail_end = tp(100);
        let tail_window = ti(tail_start.value(), tail_end.value());

        // Requirements that comfortably fit in the quay.
        let dur = TimeDelta::new(2);
        let need = len(2);
        let bounds = si(0, 10);

        // 1) There must be at least one free region in the tail window.
        let mut regions = ov.iter_free_regions(tail_window, dur, need, bounds);
        let first_region = regions.next();
        assert!(
            first_region.is_some(),
            "Expected at least one feasible free region in the tail window"
        );

        // 2) There must be at least one free slot in the tail window.
        let mut slots = ov.iter_free_slots(tail_window, dur, need, bounds);
        let first_slot = slots.next();
        assert!(
            first_slot.is_some(),
            "Expected at least one feasible free slot in the tail window"
        );

        // Sanity: any slot produced must start within the tail window.
        if let Some(bf) = first_slot {
            let st = bf.slot().start_time();
            assert!(
                st >= tail_start && st < tail_end,
                "Slot start time must lie within the tail window"
            );
        }

        // Sanity: any region produced must cover the requested duration inside the tail window.
        if let Some(br) = first_region {
            let r = br.region().rectangle().time();
            assert!(
                r.start() >= tail_start && r.end() <= tail_end && (r.end() - r.start()) >= dur,
                "Region band must lie within tail window and cover duration"
            );
        }
    }

    #[test]
    fn test_same_key_free_and_occupy_occupy_wins() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        let r = rect(ti(5, 8), si(2, 6));

        // Create both overlay entries at the SAME key = 5
        ov.add_free(tp(5), r.space()).unwrap();
        ov.add_occupy(tp(5), r.space()).unwrap();

        assert!(
            ov.is_occupied(&r).unwrap(),
            "occupy must win on tie at same timestamp"
        );
    }

    #[test]
    fn test_barrier_without_overlay_set_prevents_carry() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        // Occupy [2,6)×[3,7) with the *barrier* added by `occupy` at t=6
        ov.occupy(&rect(ti(2, 6), si(3, 7))).unwrap();

        // Just after the barrier: should be free again
        assert!(ov.is_free(&rect(ti(6, 8), si(3, 7))).unwrap());

        // And right before the barrier: still occupied
        assert!(ov.is_occupied(&rect(ti(5, 6), si(3, 7))).unwrap());
    }

    #[test]
    fn test_merged_keys_are_sorted_and_deduped() {
        let mut berth = BO::new(len(10));
        // Base keys: 3 and 8 (occupy two disjoint windows)
        berth.occupy(&rect(ti(3, 5), si(0, 1))).unwrap();
        berth.occupy(&rect(ti(8, 9), si(0, 1))).unwrap();

        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Overlay key at 6, and a barrier at 7 (implicit via a free op)
        ov.add_occupy(tp(6), si(1, 2)).unwrap();
        ov.add_free(tp(7), si(1, 2)).unwrap(); // creates a barrier at 7

        assert_eq!(ov.overlay_next_key_after(tp(0)), Some(tp(3)));
        assert_eq!(ov.overlay_next_key_after(tp(3)), Some(tp(5))); // base end
        assert_eq!(ov.overlay_next_key_after(tp(5)), Some(tp(6))); // overlay
        assert_eq!(ov.overlay_next_key_after(tp(6)), Some(tp(7))); // barrier
        assert_eq!(ov.overlay_next_key_after(tp(7)), Some(tp(8))); // base
        assert_eq!(ov.overlay_next_key_after(tp(8)), Some(tp(9)));
        assert_eq!(ov.overlay_next_key_after(tp(9)), None);
    }

    #[test]
    fn test_same_key_partial_overlap_occupy_wins_only_on_overlap() {
        let berth = BO::new(len(12));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        // At t=5, free [2,8) then occupy [4,10) — same timestamp
        // Overlap is [4,8).
        ov.add_free(tp(5), si(2, 8)).unwrap();
        ov.add_occupy(tp(5), si(4, 10)).unwrap();

        // Overlap [4,8) must be occupied.
        assert!(ov.is_occupied(&rect(ti(5, 7), si(4, 8))).unwrap());
        // Left non-overlap [2,4) remains free per the free op.
        assert!(ov.is_free(&rect(ti(5, 7), si(2, 4))).unwrap());
        // Right tail [8,10) occupied (only from occupy).
        assert!(ov.is_occupied(&rect(ti(5, 7), si(8, 10))).unwrap());
    }

    #[test]
    fn test_disjoint_intervals_coalesce_and_query_correctly() {
        let berth = BO::new(len(20));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        // Make several small occupied islands at the same key
        ov.add_occupy(tp(4), si(1, 3)).unwrap();
        ov.add_occupy(tp(4), si(3, 5)).unwrap(); // touches previous -> coalesce [1,5)
        ov.add_occupy(tp(4), si(10, 12)).unwrap();

        // Free a hole inside [1,5) to split it
        ov.add_free(tp(4), si(2, 4)).unwrap();

        // Now at t=4 we expect occupied: [1,2) ∪ [4,5) ∪ [10,12)
        assert!(ov.is_occupied(&rect(ti(4, 6), si(1, 2))).unwrap());
        assert!(ov.is_free(&rect(ti(4, 6), si(2, 4))).unwrap());
        assert!(ov.is_occupied(&rect(ti(4, 6), si(4, 5))).unwrap());
        assert!(ov.is_occupied(&rect(ti(4, 6), si(10, 12))).unwrap());
    }

    #[test]
    fn test_zero_and_negative_duration_respect_barriers() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        // Occupy with a barrier at 6
        ov.occupy(&rect(ti(2, 6), si(4, 8))).unwrap();

        // Duration == 0: starts should include 2 and 6; 6 should reflect *post*-band state (free)
        let starts: Vec<_> = ov
            .iter_free_slots(ti(2, 6), TimeDelta::new(0), len(1), si(0, 10))
            .map(|bf| bf.slot().start_time().value())
            .collect();
        assert!(starts.contains(&2));
        assert!(starts.contains(&6));

        // Negative duration treated like 0 by our helpers: same set of starts should be reachable
        let starts_neg: Vec<_> = ov
            .iter_free_slots(ti(2, 6), TimeDelta::new(-3), len(1), si(0, 10))
            .map(|bf| bf.slot().start_time().value())
            .collect();
        assert!(starts_neg.contains(&2));
        assert!(starts_neg.contains(&6));
    }

    #[test]
    fn test_overlay_key_at_zero_affects_initial_slice() {
        let berth = BO::new(len(10)); // base origin at t=0
        let mut ov = BerthOccupancyOverlay::new(&berth);

        ov.add_occupy(tp(0), si(0, 2)).unwrap();

        // The very first slice [0,1) must see the overlay at its predecessor (t=0).
        assert!(ov.is_occupied(&rect(ti(0, 1), si(0, 2))).unwrap());
        assert!(ov.is_free(&rect(ti(0, 1), si(2, 10))).unwrap());
    }

    #[test]
    fn exact_fit_required_space_across_entire_quay() {
        let berth = BO::new(len(8));
        let ov = BerthOccupancyOverlay::new(&berth);

        // require full length inside [0,8)
        let items: Vec<_> = ov
            .iter_free_slots(ti(0, 3), TimeDelta::new(3), len(8), si(0, 8))
            .collect();
        assert!(!items.is_empty(), "Full-length slot should be produced");
    }

    fn snapshot_runs_at(
        ov: &BerthOccupancyOverlay<'_, '_, T, BooleanVecQuay>,
        t: T,
    ) -> Vec<(usize, usize)> {
        ov.free_runs_at(tp(t))
            .map(|iv| (iv.start().value(), iv.end().value()))
            .collect()
    }

    #[test]
    fn test_disjoint_ops_commute() {
        let berth = BO::new(len(10));

        // Plan A: free then occupy (disjoint)
        let mut a = BerthOccupancyOverlay::new(&berth);
        a.add_free(tp(4), si(0, 2)).unwrap();
        a.add_occupy(tp(4), si(6, 8)).unwrap();

        // Plan B: occupy then free
        let mut b = BerthOccupancyOverlay::new(&berth);
        b.add_occupy(tp(4), si(6, 8)).unwrap();
        b.add_free(tp(4), si(0, 2)).unwrap();

        assert_eq!(snapshot_runs_at(&a, 4), snapshot_runs_at(&b, 4));
    }

    #[test]
    fn test_into_commit_roundtrip_is_idempotent_on_base() {
        let mut berth = BO::new(len(12));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        // Complex overlay: carve hole + add disjoint obstacle
        let big = rect(ti(2, 9), si(3, 9));
        let hole = rect(ti(4, 6), si(5, 7));
        let obs = rect(ti(7, 10), si(0, 2));

        ov.occupy(&big).unwrap();
        ov.free(&hole).unwrap();
        ov.occupy(&obs).unwrap();

        // Before apply: base differs from overlay
        assert!(berth.is_free(&big).unwrap());

        // Apply commit (op-log form)
        let commit = ov.into_commit();
        berth.apply(&commit).unwrap();

        // Now base should match overlay’s queries for a few probes
        assert!(berth.is_occupied(&rect(ti(3, 4), si(3, 9))).unwrap());
        assert!(berth.is_free(&hole).unwrap());
        assert!(berth.is_occupied(&obs).unwrap());

        // Reapply commit: should be a no-op (idempotent)
        let before = berth.time_event_count();
        berth.apply(&commit).unwrap();
        assert_eq!(before, berth.time_event_count());
    }

    #[test]
    fn test_add_free_oob_is_error_and_does_not_mutate() {
        let berth = BO::new(len(8));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        let res = ov.add_free(tp(2), si(7, 10)); // [7,10) exceeds quay end 8
        assert!(res.is_err());

        // No keys introduced by failure
        assert_eq!(ov.overlay_next_key_after(tp(0)), None);
    }

    #[test]
    fn test_barrier_splits_when_base_has_no_keys() {
        let berth = BO::new(len(10)); // base: only origin
        let mut ov = BerthOccupancyOverlay::new(&berth);

        // Create a band [2,6) by adding free at 2 and barrier at 6 via occupy then free
        ov.add_occupy(tp(0), si(0, 1)).unwrap(); // force a change pre-2
        ov.add_free(tp(2), si(0, 1)).unwrap(); // barrier at 2 via free(..end)
        ov.add_occupy(tp(6), si(0, 1)).unwrap(); // another barrier at 6

        // Regions over [0,8) with dur=2 should show a band split at 2 and 6
        assert_regions_match_slots_overlay(&ov, ti(0, 8), TimeDelta::new(2), len(1), si(0, 10));
    }

    #[test]
    fn test_overlay_change_is_carried_across_all_base_interior_keys() {
        let mut berth = BO::new(len(10));
        // Create interior base keys at 3, 5, 7
        berth.occupy(&rect(ti(3, 4), si(9, 10))).unwrap();
        berth.occupy(&rect(ti(5, 6), si(9, 10))).unwrap();
        berth.occupy(&rect(ti(7, 8), si(9, 10))).unwrap();

        let mut ov = BerthOccupancyOverlay::new(&berth);
        // Free [2,6)×[1,3): should place entries at 2 and across interior keys 3,5
        ov.free(&rect(ti(2, 6), si(1, 3))).unwrap();

        // All slices covering [2,6) must reflect this free band, despite base keys at 3 and 5
        for t in [2, 3, 4, 5].into_iter().map(TimePoint::new) {
            assert!(
                ov.is_free(&rect(TimeInterval::new(t, t + TimeDelta::new(1)), si(1, 3)))
                    .unwrap()
            );
        }
    }

    #[test]
    fn test_clear_removes_barriers_effect() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        ov.occupy(&rect(ti(2, 6), si(3, 5))).unwrap(); // creates barrier at 6
        assert_eq!(ov.overlay_next_key_after(tp(2)), Some(tp(6)));

        ov.clear();
        assert_eq!(ov.overlay_next_key_after(tp(2)), None);
    }

    #[test]
    fn test_absorb_copies_barriers_and_sets() {
        let berth = BO::new(len(10));
        let mut a = BerthOccupancyOverlay::new(&berth);
        let mut b = BerthOccupancyOverlay::new(&berth);

        a.occupy(&rect(ti(2, 6), si(1, 3))).unwrap(); // barrier @6
        b.free(&rect(ti(4, 5), si(0, 2))).unwrap(); // barrier @5

        // Replace A with B
        a.absorb(b);

        assert_eq!(a.overlay_next_key_after(tp(0)), Some(tp(4)));
        assert_eq!(a.overlay_next_key_after(tp(4)), Some(tp(5)));

        assert!(a.is_free(&rect(ti(4, 5), si(0, 2))).unwrap());
        assert!(
            a.operations()
                .iter()
                .any(|op| matches!(op, Operation::Free(_)))
        );
    }

    #[test]
    fn test_duration_equal_to_band_width_yields_single_start() {
        let berth = BO::new(len(10));
        let mut ov = BerthOccupancyOverlay::new(&berth);

        // Create a free band exactly [3,6) by occupying outside it
        ov.add_occupy(tp(0), si(0, 10)).unwrap(); // block everything at pred
        ov.add_free(tp(3), si(0, 10)).unwrap(); // open [3,6)
        ov.add_occupy(tp(6), si(0, 10)).unwrap(); // close at 6

        // Duration equals 3 -> only start 3 is valid inside [3,6)
        let starts: Vec<_> = ov
            .iter_free_slots(ti(0, 10), TimeDelta::new(3), len(2), si(0, 10))
            .map(|bf| bf.slot().start_time().value())
            .collect();
        assert_eq!(starts.into_iter().filter(|&s| s == 3).count(), 1);
    }

    #[test]
    fn test_overlay_applies_changes_at_all_union_keys_no_ghost_slots() {
        let mut berth = BO::new(SpaceLength::new(20));

        // Build overlay and create two overlay keys at t=3 and t=7 by alternating free/occupy.
        let mut ov = crate::berth::overlay::BerthOccupancyOverlay::new(&berth);
        let rect = |a, b, s, e| {
            crate::domain::SpaceTimeRectangle::new(
                SpaceInterval::new(SpacePosition::new(s), SpacePosition::new(e)),
                TimeInterval::new(TimePoint::new(a), TimePoint::new(b)),
            )
        };

        // Occupy [0,10)×[0,10). Adds barrier at t=10; keys at 0 and 10.
        ov.occupy(&rect(0, 10, 0, 10)).unwrap();

        // Free a subrange [4,6) across time [3,7) – creates overlay-only keys at 3 and 7.
        ov.free(&rect(3, 7, 4, 6)).unwrap();

        {
            // Within the query bounds [0,10), with dur=3 and need=2, the ONLY valid start is t=3,
            // and the slot must be exactly the carved corridor [4,6). No ghost starts across 7.
            let tw = TimeInterval::new(TimePoint::new(0), TimePoint::new(10));
            let mut saw_any = false;

            for fs in ov.iter_free_slots(
                tw,
                TimeDelta::new(3),
                SpaceLength::new(2),
                SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10)),
            ) {
                saw_any = true;

                let t = fs.slot().start_time().value();
                assert_eq!(
                    t, 3,
                    "unexpected start_time {}, starts must split at union keys (3 and 7) with no ghosts",
                    t
                );

                let s0 = fs.slot().space().start().value();
                let s1 = fs.slot().space().end().value();
                assert_eq!(
                    (s0, s1),
                    (4, 6),
                    "slot at t=3 must be the carved corridor [4,6), got [{}, {})",
                    s0,
                    s1
                );
            }

            assert!(saw_any, "expected at least one slot at t=3");
        }

        // Now we can move `ov` and mutably borrow `berth`.
        let commit = ov.into_commit();
        berth.apply(&commit).unwrap();

        // After applying, base should be:
        //  - t=0: occupied on [0,10), so free is [10,20)
        //  - t=3: corridor [4,6) free in addition to tail [10,20)
        //  - t=7: corridor ended at barrier; back to [10,20)
        let expect = |t: i64| -> Vec<(usize, usize)> {
            match t {
                0 => vec![(10, 20)],
                3 => vec![(4, 6), (10, 20)],
                7 => vec![(10, 20)],
                _ => unreachable!(),
            }
        };

        for &t in &[0, 3, 7] {
            let pairs: Vec<_> = berth
                .free_runs_at(TimePoint::new(t))
                .map(|iv| (iv.start().value(), iv.end().value()))
                .collect();
            assert_eq!(pairs, expect(t), "unexpected free runs at t={}", t);
        }
    }
}
