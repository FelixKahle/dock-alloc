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
    domain::{SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint},
    marker::Brand,
};
use num_traits::{PrimInt, Signed};
use std::ops::Bound::{Excluded, Unbounded};
use std::{
    collections::BTreeMap,
    iter::{Copied, FusedIterator, Peekable},
};

pub struct BrandedFreeSlot<'brand, T>
where
    T: PrimInt + Signed,
{
    slot: FreeSlot<T>,
    _brand: Brand<'brand>,
}

impl<'brand, T> BrandedFreeSlot<'brand, T>
where
    T: PrimInt + Signed,
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

pub struct BrandedFreeRegion<'brand, T>
where
    T: PrimInt + Signed,
{
    region: FreeRegion<T>,
    _brand: Brand<'brand>,
}

impl<'brand, T> BrandedFreeRegion<'brand, T>
where
    T: PrimInt + Signed,
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

/// A non-destructive overlay for a `BerthOccupancy`.
///
/// This struct allows for temporary modifications to the occupancy state without
/// altering the underlying `BerthOccupancy`. It works by tracking occupied and freed
/// regions as deltas in separate maps. This is useful for speculative modifications
/// during a search algorithm.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BerthOccupancyOverlay<'brand, 'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    berth_occupancy: &'a BerthOccupancy<T, Q>,
    free_by_time: BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    occupied_by_time: BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    operations: Vec<Operation<T>>,
    _brand: Brand<'brand>,
}

impl<'brand, 'a, T, Q> SliceView<T> for BerthOccupancyOverlay<'brand, 'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    type FreeRunsIter<'s>
        = OverlayRunsIter<<Q as QuayRead>::FreeIter<'s>>
    where
        Self: 's;

    #[inline]
    fn pred(&self, time_point: TimePoint<T>) -> Option<TimePoint<T>> {
        self.berth_occupancy.slice_predecessor_timepoint(time_point)
    }

    #[inline]
    fn next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>> {
        self.overlay_next_key_after(after)
    }

    #[inline]
    fn has_key_at(&self, time_point: TimePoint<T>) -> bool {
        self.free_by_time.contains_key(&time_point)
            || self.occupied_by_time.contains_key(&time_point)
            || self.berth_occupancy.has_key_at(time_point)
    }

    fn free_runs_at(&self, time_point: TimePoint<T>) -> Self::FreeRunsIter<'_> {
        let free_overlay_set = self.free_by_time.get(&time_point);
        let occupied_overlay_set = self.occupied_by_time.get(&time_point);

        if free_overlay_set.is_none() && occupied_overlay_set.is_none() {
            return OverlayRunsIter::Base(self.berth_occupancy.free_runs_at(time_point));
        }

        let base_iter = self.berth_occupancy.free_runs_at(time_point);
        let (lo, hi) = base_iter.size_hint();
        let est_base = hi.unwrap_or(lo);

        let free_len = free_overlay_set.map(|s| s.len()).unwrap_or(0);
        let occ_len = occupied_overlay_set.map(|s| s.len()).unwrap_or(0);

        let mut runs = SpaceIntervalSet::with_capacity(est_base.max(free_len).max(occ_len));
        runs.clear_and_fill_from_iter(base_iter);

        match (free_overlay_set, occupied_overlay_set) {
            (Some(free_set), None) => {
                let mut tmp = SpaceIntervalSet::with_capacity(runs.len() + free_set.len());
                runs.union_into(free_set, &mut tmp);
                core::mem::swap(&mut runs, &mut tmp);
            }
            (None, Some(occ_set)) => {
                let mut tmp = SpaceIntervalSet::with_capacity(runs.len());
                runs.subtract_into(occ_set, &mut tmp);
                core::mem::swap(&mut runs, &mut tmp);
            }
            (Some(free_set), Some(occ_set)) => {
                let mut tmp = SpaceIntervalSet::with_capacity(runs.len() + free_set.len());
                runs.union_into(free_set, &mut tmp);
                core::mem::swap(&mut runs, &mut tmp);
                tmp.clear();
                runs.subtract_into(occ_set, &mut tmp);
                core::mem::swap(&mut runs, &mut tmp);
            }
            _ => {}
        }

        OverlayRunsIter::Owned(runs.into_intervals().into_iter())
    }
}

type SpaceIntervalSet = IntervalSet<SpacePosition>;

#[derive(Clone, Debug)]
struct KeysUnion<'a, T: PrimInt + Signed> {
    free_keys:
        Peekable<Copied<std::collections::btree_map::Keys<'a, TimePoint<T>, SpaceIntervalSet>>>,
    occupied_keys:
        Peekable<Copied<std::collections::btree_map::Keys<'a, TimePoint<T>, SpaceIntervalSet>>>,
}

impl<'a, T: PrimInt + Signed> KeysUnion<'a, T> {
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

impl<'a, T: PrimInt + Signed> Iterator for KeysUnion<'a, T> {
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

impl<'a, T: PrimInt + Signed> FusedIterator for KeysUnion<'a, T> {}

impl<'brand, 'a, T, Q> BerthOccupancyOverlay<'brand, 'a, T, Q>
where
    T: PrimInt + Signed,
    Q: QuayRead,
{
    /// Creates a new, empty overlay for a given `BerthOccupancy`.
    pub(crate) fn new(berth_occupancy: &'a BerthOccupancy<T, Q>) -> Self {
        Self {
            berth_occupancy,
            free_by_time: BTreeMap::new(),
            occupied_by_time: BTreeMap::new(),
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

        let time_window = rect.time();
        let space_interval = rect.space();

        // Apply the occupation to all timeline slices covered by the rectangle's time window.
        if let Some(pred) = self
            .berth()
            .slice_predecessor_timepoint(time_window.start())
        {
            self.add_occupy(pred, space_interval)?;
        }
        for timepoint in self
            .berth()
            .slices(time_window.start(), time_window.end())
            .interior_keys()
        {
            self.add_occupy(timepoint, space_interval)?;
        }

        // Record the operation
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
    ) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        if !self.berth().space_within_quay(rect.space()) {
            return Err(QuaySpaceIntervalOutOfBoundsError::new(
                rect.space(),
                self.berth().quay_length(),
            ));
        }

        let time_window = rect.time();
        let space_interval = rect.space();

        // Apply the free operation to all timeline slices covered by the rectangle's time window.
        if let Some(pred) = self
            .berth()
            .slice_predecessor_timepoint(time_window.start())
        {
            self.add_free(pred, space_interval)?;
        }
        for timepoint in self
            .berth()
            .slices(time_window.start(), time_window.end())
            .interior_keys()
        {
            self.add_free(timepoint, space_interval)?;
        }

        // Record the operation
        self.operations
            .push(Operation::Free(FreeOperation::new(*rect)));

        Ok(())
    }

    /// Creates an iterator that merges keys from the base timeline and the overlay maps.
    fn covering_timepoints_union(
        &self,
        time_interval: TimeInterval<T>,
    ) -> impl Iterator<Item = TimePoint<T>> + '_ {
        let start = time_interval.start();
        let end = time_interval.end();

        // Base: predecessor at `start` (if any) + interior keys (Excluded bounds)
        let base_keys = self.berth().slices(start, end).covering_keys().peekable();

        // Overlay keys inside [start, end)
        let overlay_keys = KeysUnion::new(&self.free_by_time, &self.occupied_by_time)
            .filter(move |&t| t >= start && t < end)
            .peekable();

        // Merge two sorted, strictly ascending streams with de-duplication.
        std::iter::from_fn({
            let mut base_iter = base_keys;
            let mut overlay_iter = overlay_keys;
            let mut last_yielded: Option<TimePoint<T>> = None;

            move || loop {
                let next_base_key = base_iter.peek().copied();
                let next_overlay_key = overlay_iter.peek().copied();
                let next_key = match (next_base_key, next_overlay_key) {
                    (None, None) => return None,
                    (Some(key), None) => {
                        base_iter.next();
                        Some(key)
                    }
                    (None, Some(key)) => {
                        overlay_iter.next();
                        Some(key)
                    }
                    (Some(base_key), Some(overlay_key)) => match base_key.cmp(&overlay_key) {
                        std::cmp::Ordering::Less => {
                            base_iter.next();
                            Some(base_key)
                        }
                        std::cmp::Ordering::Greater => {
                            overlay_iter.next();
                            Some(overlay_key)
                        }
                        std::cmp::Ordering::Equal => {
                            base_iter.next();
                            overlay_iter.next();
                            Some(base_key)
                        }
                    },
                };
                // Ensure we only yield unique keys
                if next_key != last_yielded {
                    last_yielded = next_key;
                    return last_yielded;
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
    pub fn iter_free_slots(
        &'a self,
        time_window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> impl Iterator<Item = BrandedFreeSlot<'brand, T>> + 'a
    where
        T: Copy,
    {
        FreeSlotIter::new(self, time_window, duration, required_space, space_window)
            .map(|slot| BrandedFreeSlot::new(slot))
    }

    /// Returns an iterator over all feasible `SpaceTimeRectangle` regions, considering the overlay.
    #[inline]
    pub fn iter_free_regions(
        &'a self,
        window: TimeInterval<T>,
        duration: TimeDelta<T>,
        required_space: SpaceLength,
        space_window: SpaceInterval,
    ) -> impl Iterator<Item = BrandedFreeRegion<'brand, T>> + 'a
    where
        T: Copy,
    {
        FeasibleRegionIter::new(self, window, duration, required_space, space_window)
            .map(|region| BrandedFreeRegion::new(region))
    }

    /// Finds the next timeline key after a given time point, considering both base and overlay keys.
    #[inline]
    fn overlay_next_key_after(&self, after: TimePoint<T>) -> Option<TimePoint<T>> {
        let next_base_key = self.berth_occupancy.next_time_key_after(after);
        let next_free_key = self
            .free_by_time
            .range((Excluded(after), Unbounded))
            .next()
            .map(|(t, _)| *t);
        let next_occupied_key = self
            .occupied_by_time
            .range((Excluded(after), Unbounded))
            .next()
            .map(|(t, _)| *t);
        [next_base_key, next_free_key, next_occupied_key]
            .into_iter()
            .flatten()
            .min()
    }

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

    // ------- Smoke: construct overlay, no ops recorded initially -------
    #[test]
    fn test_overlay_constructs_empty_and_refs_base() {
        let berth = BO::new(len(10));
        let ov = BerthOccupancyOverlay::new(&berth);
        assert_eq!(ov.berth().quay_length(), len(10));
        assert!(ov.operations().is_empty());
    }

    // ------- add_free / add_occupy (single timepoint deltas) + is_free / is_occupied -------
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

    // ------- iter_free_slots yields Branded wrapper and respects overlay -------
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

    // ------- Candidate starts should include overlay keys (via overlay_next_key_after) -------
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

    // ------- Overlay changes exactly at window start when predecessor differs -------
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

    // ------- overlay_next_key_after merges base and overlay keys -------
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
}
