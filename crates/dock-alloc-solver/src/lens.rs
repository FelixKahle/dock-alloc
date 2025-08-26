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

use crate::occ::BerthOccupancy;
use crate::quay::{Quay, QuayRead, QuayWrite};
use dock_alloc_core::domain::{SpaceInterval, SpaceLength, TimeDelta, TimeInterval, TimePoint};
use num_traits::{PrimInt, Signed, Zero};
use std::collections::BTreeMap;
use std::fmt::Display;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Overlay<T: PrimInt + Signed> {
    frees: BTreeMap<TimePoint<T>, Vec<SpaceInterval>>,
    occs: BTreeMap<TimePoint<T>, Vec<SpaceInterval>>,
}

impl<T: PrimInt + Signed> Default for Overlay<T> {
    fn default() -> Self {
        Self {
            frees: BTreeMap::new(),
            occs: BTreeMap::new(),
        }
    }
}

impl<T: PrimInt + Signed> Overlay<T> {
    #[inline]
    pub fn empty() -> Self {
        Self::default()
    }

    #[inline]
    pub fn add_free(&mut self, time: TimePoint<T>, space: SpaceInterval) {
        if space.start() >= space.end() {
            return;
        }
        let v = self.frees.entry(time).or_default();
        insert_coalesced(v, space);
    }

    #[inline]
    pub fn add_occupy(&mut self, time: TimePoint<T>, space: SpaceInterval) {
        if space.start() >= space.end() {
            return;
        }
        let v = self.occs.entry(time).or_default();
        insert_coalesced(v, space);
    }

    #[inline]
    pub fn free_keys(&self) -> impl Iterator<Item = TimePoint<T>> + '_ {
        self.frees.keys().copied()
    }

    #[inline]
    pub fn occ_keys(&self) -> impl Iterator<Item = TimePoint<T>> + '_ {
        self.occs.keys().copied()
    }
}

impl<T: PrimInt + Signed + Display> Display for Overlay<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Overlay(frees: {}, occs: {})",
            self.frees.len(),
            self.occs.len()
        )
    }
}

pub trait TimelineSlices<T: PrimInt + Signed, Q: QuayRead> {
    fn predecessor_key(&self, t: TimePoint<T>) -> Option<TimePoint<T>>;
    fn keys_in_open(&self, start: TimePoint<T>, end: TimePoint<T>, out: &mut Vec<TimePoint<T>>);
    fn quay_at(&self, key: TimePoint<T>) -> &Q;
}

impl<T, Q> TimelineSlices<T, Q> for BerthOccupancy<T, Q>
where
    T: PrimInt + Signed + Zero + Copy,
    Q: QuayRead + QuayWrite + Clone + PartialEq,
{
    fn predecessor_key(&self, t: TimePoint<T>) -> Option<TimePoint<T>> {
        self.slice_predecessor_key(t)
    }

    fn keys_in_open(&self, start: TimePoint<T>, end: TimePoint<T>, out: &mut Vec<TimePoint<T>>) {
        self.slice_keys_in_open(start, end, out);
    }

    fn quay_at(&self, key: TimePoint<T>) -> &Q {
        self.snapshot_at(key).expect("slice key must exist")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AvailabilityView<'a, T: PrimInt + Signed, Q: Quay> {
    berth: &'a BerthOccupancy<T, Q>,
    slice_keys: Vec<TimePoint<T>>,
}

impl<'a, T, Q> AvailabilityView<'a, T, Q>
where
    T: PrimInt + Signed + Zero + Copy,
    Q: QuayRead + QuayWrite + Clone + PartialEq,
    BerthOccupancy<T, Q>: TimelineSlices<T, Q>,
{
    pub fn new(berth: &'a BerthOccupancy<T, Q>, time_window: TimeInterval<T>) -> Self {
        let mut slice_keys = Vec::<TimePoint<T>>::new();
        if let Some(k0) = berth.predecessor_key(time_window.start()) {
            slice_keys.push(k0);
        }
        berth.keys_in_open(time_window.start(), time_window.end(), &mut slice_keys);
        Self { berth, slice_keys }
    }

    #[inline]
    pub fn slice_keys(&self) -> &[TimePoint<T>] {
        &self.slice_keys
    }

    #[inline]
    pub fn berth(&self) -> &BerthOccupancy<T, Q> {
        self.berth
    }

    pub fn is_rect_free_under(&self, space: SpaceInterval, overlay: Option<&Overlay<T>>) -> bool {
        for &key in &self.slice_keys {
            let q = self.berth.quay_at(key);
            if let Some(ov) = overlay
                && overlay_any_occupy_overlaps(ov, key, space) {
                    return false;
                }

            let base_free = q.check_free(space);
            if base_free {
                continue;
            }

            if let Some(ov) = overlay {
                let freed = overlay_frees_for_key_clamped(ov, key, space);
                if range_fully_covered(space, &freed) {
                    continue;
                }
            }
            return false;
        }
        true
    }

    pub fn intersect_free_runs(
        &self,
        required_len: SpaceLength,
        search_space: SpaceInterval,
        overlay: Option<&Overlay<T>>,
    ) -> Vec<SpaceInterval> {
        let mut acc_a: Vec<SpaceInterval> = Vec::new();
        let mut acc_b: Vec<SpaceInterval> = Vec::new();
        let mut first = true;

        for &key in &self.slice_keys {
            let q = self.berth.quay_at(key);
            let mut runs = collect_runs(q, search_space, required_len);

            if let Some(ov) = overlay {
                let frees = overlay_frees_for_key_clamped(ov, key, search_space);
                if !frees.is_empty() {
                    runs = runs_union_linear(&runs, &frees);
                }
                let occs = overlay_occupies_for_key_clamped(ov, key, search_space);
                if !occs.is_empty() {
                    runs = runs_subtract_linear(&runs, &occs);
                }
                runs.retain(|r| r.extent() >= required_len);
            }

            if first {
                acc_a = runs;
                first = false;
            } else {
                acc_b.clear();
                runs_intersect_into(&acc_a, &runs, &mut acc_b);
                std::mem::swap(&mut acc_a, &mut acc_b);
            }

            if acc_a.is_empty() {
                break;
            }
        }

        acc_a
    }
}

pub struct FreePlacementIter<T>
where
    T: PrimInt + Signed + Zero + Copy,
{
    proc_len: TimeDelta<T>,
    keys_all: Vec<TimePoint<T>>,
    runs_per_key: Vec<Vec<SpaceInterval>>,
    t0_keys: Vec<TimePoint<T>>,
    t0_to_ix: Vec<usize>,
    idx_t0: usize,
    cur_runs: Vec<SpaceInterval>,
    idx_run: usize,
    current_t0: Option<TimePoint<T>>,
    scratch_a: Vec<SpaceInterval>,
    scratch_b: Vec<SpaceInterval>,
}

impl<T> FreePlacementIter<T>
where
    T: PrimInt + Signed + Zero + Copy,
{
    pub fn new<'a, Q>(
        berth: &'a BerthOccupancy<T, Q>,
        search_time: TimeInterval<T>,
        proc_len: TimeDelta<T>,
        len: SpaceLength,
        search_space: SpaceInterval,
        overlay: Option<&'a Overlay<T>>,
    ) -> Self
    where
        Q: crate::quay::Quay + Clone + PartialEq,
        BerthOccupancy<T, Q>: TimelineSlices<T, Q>,
    {
        let mut keys_all = Vec::<TimePoint<T>>::new();
        if let Some(k0) = berth.predecessor_key(search_time.start()) {
            keys_all.push(k0);
        }
        berth.keys_in_open(search_time.start(), search_time.end(), &mut keys_all);
        let mut runs_per_key: Vec<Vec<SpaceInterval>> = Vec::with_capacity(keys_all.len());
        for &key in &keys_all {
            let q = berth.quay_at(key);
            let mut runs = collect_runs(q, search_space, len);

            if let Some(ov) = overlay {
                let frees = overlay_frees_for_key_clamped(ov, key, search_space);
                if !frees.is_empty() {
                    runs = runs_union_linear(&runs, &frees);
                }
                let occs = overlay_occupies_for_key_clamped(ov, key, search_space);
                if !occs.is_empty() {
                    runs = runs_subtract_linear(&runs, &occs);
                }
                runs.retain(|r| r.extent() >= len);
            }

            runs_per_key.push(runs);
        }

        let mut t0_keys = Vec::<TimePoint<T>>::new();
        let mut t0_to_ix = Vec::<usize>::new();
        for (ix, &k) in keys_all.iter().enumerate() {
            let t1 = k + proc_len;
            if k >= search_time.start() && t1 <= search_time.end() {
                t0_keys.push(k);
                t0_to_ix.push(ix);
            }
        }

        Self {
            proc_len,
            keys_all,
            runs_per_key,
            t0_keys,
            t0_to_ix,
            idx_t0: 0,
            cur_runs: Vec::new(),
            idx_run: 0,
            current_t0: None,
            scratch_a: Vec::new(),
            scratch_b: Vec::new(),
        }
    }

    #[inline]
    fn next_runs_for_next_t0(&mut self) -> bool {
        while self.idx_t0 < self.t0_keys.len() {
            let t0 = self.t0_keys[self.idx_t0];
            let ix0 = self.t0_to_ix[self.idx_t0];
            self.idx_t0 += 1;

            let t1 = t0 + self.proc_len;
            self.scratch_a.clear();
            self.scratch_b.clear();
            self.scratch_a.extend_from_slice(&self.runs_per_key[ix0]);

            let mut j = ix0 + 1;
            while j < self.keys_all.len() && self.keys_all[j] < t1 {
                if self.scratch_a.is_empty() {
                    break;
                }
                self.scratch_b.clear();
                runs_intersect_into(&self.scratch_a, &self.runs_per_key[j], &mut self.scratch_b);
                core::mem::swap(&mut self.scratch_a, &mut self.scratch_b);
                j += 1;
            }

            if !self.scratch_a.is_empty() {
                self.cur_runs.clear();
                self.cur_runs.extend_from_slice(&self.scratch_a);
                self.idx_run = 0;
                self.current_t0 = Some(t0);
                return true;
            }
        }
        false
    }
}

impl<T> Iterator for FreePlacementIter<T>
where
    T: PrimInt + Signed + Zero + Copy,
{
    type Item = (TimePoint<T>, SpaceInterval);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.idx_run < self.cur_runs.len() {
                let run = self.cur_runs[self.idx_run];
                self.idx_run += 1;
                let t0 = self
                    .current_t0
                    .expect("current_t0 set when cur_runs is non-empty");
                return Some((t0, run));
            }
            if !self.next_runs_for_next_t0() {
                return None;
            }
        }
    }
}

fn collect_runs<Q: QuayRead>(
    q: &Q,
    bounds: SpaceInterval,
    req_len: SpaceLength,
) -> Vec<SpaceInterval> {
    q.iter_free_intervals(req_len, bounds).collect()
}

#[inline]
pub fn coalesce_in_place(v: &mut Vec<SpaceInterval>) {
    if v.is_empty() {
        return;
    }
    v.sort_by_key(|r| r.start());
    let mut w = 0usize;
    for i in 1..v.len() {
        if v[w].end() >= v[i].start() {
            let end = if v[w].end() > v[i].end() {
                v[w].end()
            } else {
                v[i].end()
            };
            v[w] = SpaceInterval::new(v[w].start(), end);
        } else {
            w += 1;
            if w != i {
                v[w] = v[i];
            }
        }
    }
    v.truncate(w + 1);
}

#[inline]
pub fn runs_union_linear(a: &[SpaceInterval], b: &[SpaceInterval]) -> Vec<SpaceInterval> {
    let mut out: Vec<SpaceInterval> = Vec::with_capacity(a.len() + b.len());
    let mut i = 0usize;
    let mut j = 0usize;

    let mut push_run = |r: SpaceInterval| {
        if let Some(last) = out.last_mut()
            && last.end() >= r.start() {
                let new_end = if last.end() > r.end() {
                    last.end()
                } else {
                    r.end()
                };
                let s = last.start();
                *last = SpaceInterval::new(s, new_end);
                return;
            }
        out.push(r);
    };

    while i < a.len() && j < b.len() {
        if a[i].start() <= b[j].start() {
            push_run(a[i]);
            i += 1;
        } else {
            push_run(b[j]);
            j += 1;
        }
    }
    while i < a.len() {
        push_run(a[i]);
        i += 1;
    }
    while j < b.len() {
        push_run(b[j]);
        j += 1;
    }

    out
}

#[inline]
pub fn runs_subtract_linear(a: &[SpaceInterval], b: &[SpaceInterval]) -> Vec<SpaceInterval> {
    let mut out: Vec<SpaceInterval> = Vec::new();
    let mut i = 0usize;
    let mut j = 0usize;

    while i < a.len() {
        let mut cur = a[i];
        while j < b.len() && b[j].end() <= cur.start() {
            j += 1;
        }
        let mut k = j;
        let mut cur_consumed = false;

        while k < b.len() && b[k].start() < cur.end() {
            if b[k].start() <= cur.start() && b[k].end() >= cur.end() {
                cur_consumed = true;
                break;
            }
            if b[k].start() > cur.start() {
                out.push(SpaceInterval::new(cur.start(), b[k].start()));
            }
            if b[k].end() < cur.end() {
                cur = SpaceInterval::new(b[k].end(), cur.end());
                k += 1;
            } else {
                cur_consumed = true;
                break;
            }
        }

        if !cur_consumed {
            out.push(cur);
        }

        i += 1;
    }

    coalesce_in_place(&mut out);
    out
}

#[inline]
pub fn runs_intersect(a: &[SpaceInterval], b: &[SpaceInterval]) -> Vec<SpaceInterval> {
    let mut out: Vec<SpaceInterval> = Vec::new();
    let (mut i, mut j) = (0usize, 0usize);
    while i < a.len() && j < b.len() {
        let s = if a[i].start() > b[j].start() {
            a[i].start()
        } else {
            b[j].start()
        };
        let e = if a[i].end() < b[j].end() {
            a[i].end()
        } else {
            b[j].end()
        };
        if s < e {
            out.push(SpaceInterval::new(s, e));
        }
        if a[i].end() < b[j].end() {
            i += 1;
        } else {
            j += 1;
        }
    }
    out
}

/// Intersection into a provided output buffer to reduce allocations.
#[inline]
pub fn runs_intersect_into(a: &[SpaceInterval], b: &[SpaceInterval], out: &mut Vec<SpaceInterval>) {
    out.clear();
    let (mut i, mut j) = (0usize, 0usize);
    while i < a.len() && j < b.len() {
        let s = if a[i].start() > b[j].start() {
            a[i].start()
        } else {
            b[j].start()
        };
        let e = if a[i].end() < b[j].end() {
            a[i].end()
        } else {
            b[j].end()
        };
        if s < e {
            out.push(SpaceInterval::new(s, e));
        }
        if a[i].end() < b[j].end() {
            i += 1;
        } else {
            j += 1;
        }
    }
}

#[inline]
fn insert_coalesced(v: &mut Vec<SpaceInterval>, r: SpaceInterval) {
    if r.start() >= r.end() {
        return;
    }
    let i = match v.binary_search_by_key(&r.start(), |x| x.start()) {
        Ok(i) => i,
        Err(i) => i,
    };
    v.insert(i, r);

    // Merge forward while current overlaps/touches the next.
    while i + 1 < v.len() && v[i].end() >= v[i + 1].start() {
        let start = v[i].start();
        let end = if v[i].end() > v[i + 1].end() {
            v[i].end()
        } else {
            v[i + 1].end()
        };
        v[i] = SpaceInterval::new(start, end);
        v.remove(i + 1);
    }

    // Merge backward if previous overlaps/touches current.
    if i > 0 && v[i - 1].end() >= v[i].start() {
        let start = v[i - 1].start();
        let end = if v[i - 1].end() > v[i].end() {
            v[i - 1].end()
        } else {
            v[i].end()
        };
        v[i - 1] = SpaceInterval::new(start, end);
        v.remove(i);
    }
}

#[inline]
pub fn range_fully_covered(want: SpaceInterval, runs: &[SpaceInterval]) -> bool {
    if want.start() >= want.end() {
        return true;
    }
    let mut cursor = want.start();
    for r in runs {
        if r.end() <= cursor {
            continue;
        }
        if r.start() > cursor {
            return false; // gap
        }
        cursor = if cursor > r.end() { cursor } else { r.end() };
        if cursor >= want.end() {
            return true;
        }
    }
    false
}

fn overlay_frees_for_key_clamped<T: PrimInt + Signed>(
    ov: &Overlay<T>,
    key: TimePoint<T>,
    bounds: SpaceInterval,
) -> Vec<SpaceInterval> {
    let mut v = Vec::new();
    if let Some(list) = ov.frees.get(&key) {
        for r in list {
            if let Some(cl) = bounds.clamp(r) {
                v.push(cl);
            }
        }
    }
    v
}

fn overlay_occupies_for_key_clamped<T: PrimInt + Signed>(
    ov: &Overlay<T>,
    key: TimePoint<T>,
    bounds: SpaceInterval,
) -> Vec<SpaceInterval> {
    let mut v = Vec::new();
    if let Some(list) = ov.occs.get(&key) {
        for r in list {
            if let Some(cl) = bounds.clamp(r) {
                v.push(cl);
            }
        }
    }
    v
}

fn overlay_any_occupy_overlaps<T: PrimInt + Signed>(
    ov: &Overlay<T>,
    key: TimePoint<T>,
    space: SpaceInterval,
) -> bool {
    ov.occs
        .get(&key)
        .is_some_and(|list| list.iter().any(|r| r.intersects(&space)))
}

pub fn overlay_occupy_rect<T, Q>(
    ov: &mut Overlay<T>,
    berth: &BerthOccupancy<T, Q>,
    window: TimeInterval<T>,
    space: SpaceInterval,
) where
    T: PrimInt + Signed + Zero + Copy,
    Q: QuayRead + QuayWrite + Clone + PartialEq,
    BerthOccupancy<T, Q>: TimelineSlices<T, Q>,
{
    if let Some(k0) = berth.predecessor_key(window.start()) {
        ov.add_occupy(k0, space);
    }
    let mut keys = Vec::new();
    berth.keys_in_open(window.start(), window.end(), &mut keys);
    for k in keys {
        ov.add_occupy(k, space);
    }
}

pub fn overlay_free_rect<T, Q>(
    ov: &mut Overlay<T>,
    berth: &BerthOccupancy<T, Q>,
    window: TimeInterval<T>,
    space: SpaceInterval,
) where
    T: PrimInt + Signed + Zero + Copy,
    Q: QuayRead + QuayWrite + Clone + PartialEq,
    BerthOccupancy<T, Q>: TimelineSlices<T, Q>,
{
    if let Some(k0) = berth.predecessor_key(window.start()) {
        ov.add_free(k0, space);
    }
    let mut keys = Vec::new();
    berth.keys_in_open(window.start(), window.end(), &mut keys);
    for k in keys {
        ov.add_free(k, space);
    }
}

#[cfg(test)]
mod tests {
    use super::TimelineSlices;
    use super::*;
    use crate::occ::BerthOccupancy;
    use crate::quay::BTreeMapQuay;
    use dock_alloc_core::domain::SpacePosition;

    type T = i64;
    type BO = BerthOccupancy<T, BTreeMapQuay>;

    fn pos(x: usize) -> SpacePosition {
        SpacePosition::new(x)
    }
    fn len(x: usize) -> SpaceLength {
        SpaceLength::new(x)
    }
    fn si(a: usize, b: usize) -> SpaceInterval {
        SpaceInterval::new(pos(a), pos(b))
    }
    fn tp(t: T) -> TimePoint<T> {
        TimePoint::new(t)
    }
    fn ti(a: T, b: T) -> TimeInterval<T> {
        TimeInterval::new(tp(a), tp(b))
    }

    #[test]
    fn timeline_slices_predecessor_and_interior_keys() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        // Create boundaries at 0, 5, 10
        berth.occupy(ti(5, 10), si(2, 4));

        // Predecessor at exact key
        assert_eq!(berth.predecessor_key(tp(5)), Some(tp(5)));
        // Predecessor strictly inside
        assert_eq!(berth.predecessor_key(tp(6)), Some(tp(5)));
        // Predecessor at origin
        assert_eq!(berth.predecessor_key(tp(0)), Some(tp(0)));
        // No predecessor before origin
        assert_eq!(berth.predecessor_key(tp(-1)), None);

        // Interior keys in (4, 12) should be [5, 10]
        let mut keys = Vec::new();
        berth.keys_in_open(tp(4), tp(12), &mut keys);
        assert_eq!(keys, vec![tp(5), tp(10)]);
    }

    #[test]
    fn availability_is_free_without_overlay() {
        let quay_length = len(10);
        let berth = BO::new(quay_length);

        let view = AvailabilityView::new(&berth, ti(0, 10));
        assert!(view.is_rect_free_under(si(0, 10), None));
        assert!(view.is_rect_free_under(si(3, 7), None));
    }

    #[test]
    fn availability_overlay_occupy_blocks() {
        let quay_length = len(12);
        let berth = BO::new(quay_length);

        let mut ov = Overlay::empty();
        ov.add_occupy(tp(0), si(2, 5)); // applies to predecessor key 0

        let view = AvailabilityView::new(&berth, ti(0, 10));
        assert!(!view.is_rect_free_under(si(2, 5), Some(&ov)));
        assert!(view.is_rect_free_under(si(0, 2), Some(&ov)));
        assert!(view.is_rect_free_under(si(5, 12), Some(&ov)));
    }

    #[test]
    fn availability_overlay_free_covers_base_occupied() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);

        // Base occupied on [5,10) for space [2,6)
        berth.occupy(ti(5, 10), si(2, 6));

        let view = AvailabilityView::new(&berth, ti(5, 10));
        // Without overlay, space is not free
        assert!(!view.is_rect_free_under(si(2, 6), None));

        // Overlay frees exactly that space at the only slice key (5)
        let mut ov = Overlay::empty();
        ov.add_free(tp(5), si(2, 6));

        assert!(view.is_rect_free_under(si(2, 6), Some(&ov)));
    }

    #[test]
    fn intersect_free_runs_overlay_union_and_subtract() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        // Occupy [2,6) in the window [5,10)
        berth.occupy(ti(5, 10), si(2, 6));

        let view = AvailabilityView::new(&berth, ti(5, 10));

        // Base runs within [0,10) at t=5 are [0,2) and [6,10)
        // Overlay adds free [2,4) -> union becomes [0,4) and [6,10)
        // Overlay occupies [7,9) -> subtract becomes [0,4), [6,7), [9,10)
        // After filtering by required len 2: only [0,4)
        let mut ov = Overlay::empty();
        ov.add_free(tp(5), si(2, 4));
        ov.add_occupy(tp(5), si(7, 9));

        let runs = view.intersect_free_runs(len(2), si(0, 10), Some(&ov));
        let pairs: Vec<(usize, usize)> = runs
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert_eq!(pairs, vec![(0, 4)]);
    }

    #[test]
    fn free_placement_iter_basic() {
        let quay_length = len(8);
        let berth = BO::new(quay_length);

        let search_time = ti(0, 10);
        let proc_len = TimeDelta::new(3);
        let required = len(2);
        let search_space = si(0, 5);

        let it =
            FreePlacementIter::new(&berth, search_time, proc_len, required, search_space, None);
        let items: Vec<(T, (usize, usize))> = it
            .map(|(t0, space)| (t0.value(), (space.start().value(), space.end().value())))
            .collect();

        // With a single time slice at t=0, we get placements only at t0=0
        // and the entire search_space is free.
        assert_eq!(items, vec![(0, (0, 5))]);
    }

    #[test]
    fn intersect_free_runs_across_multiple_slices() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);

        // Two slices: boundaries at 0, 5, 10 by occupying in [5,10) and [10,15)
        berth.occupy(ti(5, 10), si(2, 6)); // Occupied [2,6) in slice starting at 5
        berth.occupy(ti(10, 15), si(1, 3)); // Occupied [1,3) in slice starting at 10

        // Window covers both slices [5,15)
        let view = AvailabilityView::new(&berth, ti(5, 15));

        // Base runs within [0,10):
        // - At t=5: free [0,2) and [6,12)
        // - At t=10: free [0,1), [3,12)
        // Intersection across slices gives [0,1) and [6,12)
        let runs = view.intersect_free_runs(len(1), si(0, 12), None);
        let pairs: Vec<(usize, usize)> = runs
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert_eq!(pairs, vec![(0, 1), (6, 12)]);
    }

    #[test]
    fn overlay_applies_to_predecessor_slice_key() {
        let quay_length = len(10);
        let berth = BO::new(quay_length);

        // Window starts at t=2, predecessor slice key is 0
        // Overlay occupies [3,5) at key=0 -> should block availability over the window
        let mut ov = Overlay::empty();
        ov.add_occupy(tp(0), si(3, 5));

        let view = AvailabilityView::new(&berth, ti(2, 6));
        assert!(!view.is_rect_free_under(si(3, 5), Some(&ov)));
        // Non-overlapping region remains free
        assert!(view.is_rect_free_under(si(0, 3), Some(&ov)));
    }

    #[test]
    fn runs_subtract_linear_touching_edges_half_open() {
        // A: [0,2), [4,6)
        let a = vec![si(0, 2), si(4, 6)];
        // B subtract exactly [2,4) (touches edges)
        let b = vec![si(2, 4)];

        let out = runs_subtract_linear(&a, &b);
        let pairs: Vec<(usize, usize)> = out
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect();

        // Half-open means touching at edges does not remove anything extra
        assert_eq!(pairs, vec![(0, 2), (4, 6)]);
    }

    #[test]
    fn range_fully_covered_edge_cases() {
        // Fully covered by a single run
        let want = si(2, 8);
        let runs = vec![si(0, 10)];
        assert!(range_fully_covered(want, &runs));

        // Covered by two adjacent runs that coalesce
        let want2 = si(2, 8);
        let runs2 = vec![si(0, 5), si(5, 10)];
        assert!(range_fully_covered(want2, &runs2));

        // Gap inside coverage
        let want3 = si(2, 8);
        let runs3 = vec![si(0, 4), si(5, 10)];
        assert!(!range_fully_covered(want3, &runs3));

        // Empty want is always considered covered
        let want_empty = si(5, 5);
        let runs_any = vec![si(0, 1)];
        assert!(range_fully_covered(want_empty, &runs_any));
    }

    #[test]
    fn free_placement_iter_with_overlay_creates_slots() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        // Base: occupy everything in [5,10)
        berth.occupy(ti(5, 10), si(0, 10));

        // Overlay: free [2,6) at key=5, creating a viable placement
        let mut ov = Overlay::empty();
        ov.add_free(tp(5), si(2, 6));

        let search_time = ti(5, 10);
        let proc_len = TimeDelta::new(3);
        let required = len(3);
        let search_space = si(0, 10);

        let it = FreePlacementIter::new(
            &berth,
            search_time,
            proc_len,
            required,
            search_space,
            Some(&ov),
        );
        let items: Vec<(T, (usize, usize))> = it
            .map(|(t0, space)| (t0.value(), (space.start().value(), space.end().value())))
            .collect();

        // Should yield at t0=5 with runs inside [2,6); exact run is [2,6) since required=3
        assert_eq!(items, vec![(5, (2, 6))]);
    }

    #[test]
    fn test_overlay_occupy_rect_populates_all_slice_keys() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);

        // Create boundaries at 0,5,10
        berth.occupy(ti(5, 10), si(1, 2));
        // Window [2,9): predecessor key 0, interior key 5
        let window = ti(2, 9);
        let space = si(3, 7);

        let mut ov = Overlay::empty();
        overlay_occupy_rect(&mut ov, &berth, window, space);

        let mut keys: Vec<T> = ov.occ_keys().map(|tp| tp.value()).collect();
        keys.sort_unstable();
        keys.dedup();
        assert_eq!(keys, vec![0, 5]);
    }

    #[test]
    fn test_overlay_free_rect_populates_all_slice_keys() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);

        // Create boundaries at 0,5,10
        berth.occupy(ti(5, 10), si(1, 2));
        // Window [6,12): predecessor key 5, interior key 10
        let window = ti(6, 12);
        let space = si(2, 8);

        let mut ov = Overlay::empty();
        overlay_free_rect(&mut ov, &berth, window, space);

        let mut keys: Vec<T> = ov.free_keys().map(|tp| tp.value()).collect();
        keys.sort_unstable();
        keys.dedup();
        assert_eq!(keys, vec![5, 10]);
    }

    #[test]
    fn fully_occupied_slice_made_feasible_by_overlay() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        // Base: fully occupy the slice [5,10) across the entire space
        berth.occupy(ti(5, 10), si(0, 10));

        // Without overlay, nothing is free in this slice
        let view = AvailabilityView::new(&berth, ti(5, 10));
        assert!(!view.is_rect_free_under(si(3, 7), None));
        let base_runs: Vec<_> = view
            .intersect_free_runs(len(2), si(0, 10), None)
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert!(base_runs.is_empty());

        // Overlay frees [3,7) at key=5: feasibility restored
        let mut ov = Overlay::empty();
        ov.add_free(tp(5), si(3, 7));

        assert!(view.is_rect_free_under(si(3, 7), Some(&ov)));
        let runs: Vec<_> = view
            .intersect_free_runs(len(2), si(0, 10), Some(&ov))
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert_eq!(runs, vec![(3, 7)]);
    }

    #[test]
    fn free_placement_iter_spans_multiple_slices_intersection_shrinks() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        // Create two slices: [5,10) and [10,15), with differing free regions
        berth.occupy(ti(5, 10), si(2, 8)); // slice @5 free: [0,2) and [8,10)
        berth.occupy(ti(10, 15), si(4, 10)); // slice @10 free: [0,4)

        let search_time = ti(5, 15);
        let proc_len = TimeDelta::new(10); // spans both slices
        let required = len(2);
        let search_space = si(0, 10);

        let it =
            FreePlacementIter::new(&berth, search_time, proc_len, required, search_space, None);
        let items: Vec<(T, (usize, usize))> = it
            .map(|(t0, space)| (t0.value(), (space.start().value(), space.end().value())))
            .collect();

        // Intersection across both slices yields only [0,2)
        assert_eq!(items, vec![(5, (0, 2))]);
    }

    #[test]
    fn runs_intersect_and_subtract_properties() {
        // Simple LCG for repeatable randomness
        struct Lcg(u64);
        impl Lcg {
            fn new(seed: u64) -> Self {
                Self(seed)
            }
            fn next(&mut self) -> u64 {
                self.0 = self
                    .0
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                self.0
            }
            fn gen_usize(&mut self, upper: usize) -> usize {
                if upper == 0 {
                    0
                } else {
                    (self.next() as usize) % upper
                }
            }
        }

        fn make_interval(a: usize, b: usize) -> SpaceInterval {
            let sa = SpacePosition::new(a);
            let sb = SpacePosition::new(b);
            if sa <= sb {
                SpaceInterval::new(sa, sb)
            } else {
                SpaceInterval::new(sb, sa)
            }
        }

        // Generate random, sorted, coalesced run sets
        fn gen_runs(rng: &mut Lcg, max_runs: usize, universe: usize) -> Vec<SpaceInterval> {
            let n = rng.gen_usize(max_runs + 1);
            let mut v: Vec<SpaceInterval> = Vec::with_capacity(n);
            for _ in 0..n {
                let a = rng.gen_usize(universe + 1);
                let b = rng.gen_usize(universe + 1);
                if a != b {
                    v.push(make_interval(a, b));
                }
            }
            v.sort_by_key(|r| r.start());
            coalesce_in_place(&mut v);
            v
        }

        fn assert_sorted_coalesced_valid(v: &[SpaceInterval]) {
            for i in 0..v.len() {
                // Non-empty
                assert!(
                    v[i].start() < v[i].end(),
                    "empty or inverted interval at {}",
                    i
                );
                // Sorted and coalesced: strict separation
                if i + 1 < v.len() {
                    assert!(
                        v[i].end() < v[i + 1].start(),
                        "not coalesced/sorted at {}: {:?} then {:?}",
                        i,
                        (v[i].start().value(), v[i].end().value()),
                        (v[i + 1].start().value(), v[i + 1].end().value())
                    );
                }
            }
        }

        let mut rng = Lcg::new(0xA1B2C3D4E5F60789);
        let universe = 64;

        for _ in 0..200 {
            let a = gen_runs(&mut rng, 8, universe);
            let b = gen_runs(&mut rng, 8, universe);

            let inter = runs_intersect(&a, &b);
            assert_sorted_coalesced_valid(&inter);

            let sub = runs_subtract_linear(&a, &b);
            assert_sorted_coalesced_valid(&sub);
        }
    }
}
