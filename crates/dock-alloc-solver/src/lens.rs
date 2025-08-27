// Copyright (c) 2025 Felix Kahle.
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to do so, subject to the following conditions:
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

/// A collection of sorted, non-overlapping, and coalesced space intervals.
///
/// Invariants:
/// - Sorted by `start()`
/// - Non-overlapping and non-touching (adjacent merged)
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SpaceIntervalSet {
    intervals: Vec<SpaceInterval>,
}

impl SpaceIntervalSet {
    #[inline]
    pub fn new() -> Self {
        Self {
            intervals: Vec::new(),
        }
    }

    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            intervals: Vec::with_capacity(cap),
        }
    }

    #[inline]
    pub fn from_vec(mut intervals: Vec<SpaceInterval>) -> Self {
        if !intervals.is_empty() {
            Self::coalesce_in_place(&mut intervals);
        }
        Self { intervals }
    }

    #[inline]
    pub fn from_iter<I: IntoIterator<Item = SpaceInterval>>(iter: I) -> Self {
        let mut v: Vec<SpaceInterval> = iter.into_iter().collect();
        if !v.is_empty() {
            Self::coalesce_in_place(&mut v);
        }
        Self { intervals: v }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.intervals.len()
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.intervals.is_empty()
    }
    #[inline]
    pub fn as_slice(&self) -> &[SpaceInterval] {
        &self.intervals
    }
    #[inline]
    pub fn clear(&mut self) {
        self.intervals.clear()
    }
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.intervals.reserve(additional)
    }
    #[inline]
    pub fn into_vec(self) -> Vec<SpaceInterval> {
        self.intervals
    }

    #[inline]
    pub fn covers(&self, want: SpaceInterval) -> bool {
        if want.start() >= want.end() {
            return true;
        }
        let mut cursor = want.start();
        for r in &self.intervals {
            if r.end() <= cursor {
                continue;
            }
            if r.start() > cursor {
                return false;
            }
            cursor = cursor.max(r.end());
            if cursor >= want.end() {
                return true;
            }
        }
        false
    }

    #[inline]
    pub fn overlaps(&self, s: SpaceInterval) -> bool {
        if self.intervals.is_empty() {
            return false;
        }

        let mut lo = 0usize;
        let mut hi = self.intervals.len();
        while lo < hi {
            let mid = (lo + hi) / 2;
            if self.intervals[mid].start() < s.start() {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        if lo > 0 && self.intervals[lo - 1].intersects(&s) {
            return true;
        }
        if lo < self.intervals.len() && self.intervals[lo].intersects(&s) {
            return true;
        }
        false
    }

    #[inline]
    pub fn clamped_to(&self, bounds: SpaceInterval) -> Self {
        if self.is_empty() {
            return Self::new();
        }
        let mut out = Self::with_capacity(self.len());
        for r in &self.intervals {
            if let Some(cl) = bounds.clamp(r) {
                out.push_coalesced(cl);
            }
        }
        out
    }

    #[inline]
    pub fn clamped_linear(&self, bounds: SpaceInterval) -> Self {
        if self.is_empty() {
            return Self::new();
        }
        let a = &self.intervals;
        let mut i = match a.binary_search_by_key(&bounds.start(), |r| r.end()) {
            Ok(i) | Err(i) => i,
        };

        let mut out = Self::with_capacity(/* rough upper bound */ 4.min(a.len()));
        while i < a.len() && a[i].start() < bounds.end() {
            let s = core::cmp::max(a[i].start(), bounds.start());
            let e = core::cmp::min(a[i].end(), bounds.end());
            if s < e {
                // safe to push directly: inputs are disjoint → outputs are disjoint
                out.intervals.push(SpaceInterval::new(s, e));
            }
            i += 1;
        }
        out
    }

    /// Insert `r` while maintaining invariants (O(log n + k)).
    #[inline]
    pub fn push_coalesced(&mut self, r: SpaceInterval) {
        if r.start() >= r.end() {
            return;
        }
        let v = &mut self.intervals;
        let mut i = match v.binary_search_by_key(&r.start(), |x| x.start()) {
            Ok(i) => i,
            Err(i) => i,
        };
        let mut s = r.start();
        let mut e = r.end();
        if i > 0 && v[i - 1].end() >= s {
            i -= 1;
            s = v[i].start().min(s);
        }
        let mut j = i;
        while j < v.len() && v[j].start() <= e {
            e = v[j].end().max(e);
            j += 1;
        }
        let new_iv = SpaceInterval::new(s, e);
        if i == v.len() {
            v.push(new_iv);
        } else if j == i {
            v.insert(i, new_iv);
        } else {
            v[i] = new_iv;
            if j > i + 1 {
                v.drain(i + 1..j);
            }
        }
    }

    #[inline]
    pub fn union(&self, other: &Self) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }

        let (a, b) = (&self.intervals, &other.intervals);
        let mut out = Vec::with_capacity(a.len() + b.len());
        let (mut i, mut j) = (0usize, 0usize);
        while i < a.len() && j < b.len() {
            let pick = if a[i].start() <= b[j].start() {
                let x = a[i];
                i += 1;
                x
            } else {
                let x = b[j];
                j += 1;
                x
            };
            Self::push_and_merge(&mut out, pick);
        }
        while i < a.len() {
            Self::push_and_merge(&mut out, a[i]);
            i += 1;
        }
        while j < b.len() {
            Self::push_and_merge(&mut out, b[j]);
            j += 1;
        }
        Self { intervals: out }
    }

    #[inline]
    pub fn subtract(&self, other: &Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return self.clone();
        }

        let (a, b) = (&self.intervals, &other.intervals);
        let mut out: Vec<SpaceInterval> = Vec::with_capacity(a.len());
        let (mut i, mut j) = (0usize, 0usize);

        while i < a.len() {
            let mut cur = a[i];
            while j < b.len() && b[j].end() <= cur.start() {
                j += 1;
            }
            let mut k = j;
            let mut consumed = false;

            while k < b.len() && b[k].start() < cur.end() {
                let sub = b[k];
                if sub.start() > cur.start() {
                    out.push(SpaceInterval::new(cur.start(), sub.start()));
                }
                if sub.end() >= cur.end() {
                    consumed = true;
                    break;
                }
                cur = SpaceInterval::new(sub.end(), cur.end());
                k += 1;
            }
            if !consumed {
                out.push(cur);
            }
            j = k;
            i += 1;
        }
        debug_assert!(Self::is_sorted_non_overlapping(&out));
        Self { intervals: out }
    }

    #[inline]
    pub fn intersection(&self, other: &Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return Self::new();
        }
        let (a, b) = (&self.intervals, &other.intervals);
        let mut out: Vec<SpaceInterval> = Vec::with_capacity(a.len().min(b.len()));
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
                i += 1
            } else {
                j += 1
            }
        }
        debug_assert!(Self::is_sorted_non_overlapping(&out));
        Self { intervals: out }
    }

    #[inline]
    pub fn intersection_into(&self, other: &Self, out: &mut Self) {
        if self.is_empty() || other.is_empty() {
            out.clear();
            return;
        }
        let (a, b) = (&self.intervals, &other.intervals);
        out.intervals.clear();
        out.intervals.reserve(a.len().min(b.len()));
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
                out.intervals.push(SpaceInterval::new(s, e));
            }
            if a[i].end() < b[j].end() {
                i += 1
            } else {
                j += 1
            }
        }
        debug_assert!(Self::is_sorted_non_overlapping(&out.intervals));
    }

    #[inline]
    pub fn filter_min_length(mut self, min: SpaceLength) -> Self {
        if min.value() > 1 {
            self.intervals.retain(|r| r.extent() >= min);
        }
        self
    }

    #[inline]
    fn coalesce_in_place(v: &mut Vec<SpaceInterval>) {
        if v.len() < 2 {
            return;
        }
        v.sort_by_key(|r| r.start());
        let mut w = 0usize;
        for i in 1..v.len() {
            if v[w].end() >= v[i].start() {
                v[w] = SpaceInterval::new(v[w].start(), v[w].end().max(v[i].end()));
            } else {
                w += 1;
                v[w] = v[i];
            }
        }
        v.truncate(w + 1);
        debug_assert!(Self::is_sorted_non_overlapping(v));
    }

    #[inline]
    fn push_and_merge(vec: &mut Vec<SpaceInterval>, run: SpaceInterval) {
        if let Some(last) = vec.last_mut() {
            if last.end() >= run.start() {
                *last = SpaceInterval::new(last.start(), last.end().max(run.end()));
                return;
            }
        }
        vec.push(run);
    }

    #[inline]
    #[cfg(debug_assertions)]
    fn is_sorted_non_overlapping(v: &[SpaceInterval]) -> bool {
        v.windows(2).all(|w| w[0].end() < w[1].start())
    }

    #[inline]
    #[cfg(not(debug_assertions))]
    fn is_sorted_non_overlapping(_v: &[SpaceInterval]) -> bool {
        true
    }
}

impl core::ops::Deref for SpaceIntervalSet {
    type Target = [SpaceInterval];
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.intervals
    }
}
impl<'a> IntoIterator for &'a SpaceIntervalSet {
    type Item = &'a SpaceInterval;
    type IntoIter = core::slice::Iter<'a, SpaceInterval>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.intervals.iter()
    }
}
impl<'a> IntoIterator for &'a mut SpaceIntervalSet {
    type Item = &'a mut SpaceInterval;
    type IntoIter = core::slice::IterMut<'a, SpaceInterval>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.intervals.iter_mut()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BerthOccupancyOverlay<T: PrimInt + Signed> {
    free_by_time: BTreeMap<TimePoint<T>, SpaceIntervalSet>,
    occupied_by_time: BTreeMap<TimePoint<T>, SpaceIntervalSet>,
}

impl<T: PrimInt + Signed> Default for BerthOccupancyOverlay<T> {
    fn default() -> Self {
        Self {
            free_by_time: BTreeMap::new(),
            occupied_by_time: BTreeMap::new(),
        }
    }
}

impl<T: PrimInt + Signed> BerthOccupancyOverlay<T> {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn add_free(&mut self, time: TimePoint<T>, space: SpaceInterval) {
        if space.start() >= space.end() {
            return;
        }
        self.free_by_time
            .entry(time)
            .or_insert_with(SpaceIntervalSet::new)
            .push_coalesced(space);
    }

    #[inline]
    pub fn add_occupy(&mut self, time: TimePoint<T>, space: SpaceInterval) {
        if space.start() >= space.end() {
            return;
        }
        self.occupied_by_time
            .entry(time)
            .or_insert_with(SpaceIntervalSet::new)
            .push_coalesced(space);
    }

    #[inline]
    pub fn free_keys(&self) -> impl Iterator<Item = TimePoint<T>> + '_ {
        self.free_by_time.keys().copied()
    }
    #[inline]
    pub fn occ_keys(&self) -> impl Iterator<Item = TimePoint<T>> + '_ {
        self.occupied_by_time.keys().copied()
    }

    #[inline]
    pub fn adjust_runs(
        &self,
        key: TimePoint<T>,
        base: SpaceIntervalSet,
        bounds: SpaceInterval,
        min_len: SpaceLength,
    ) -> SpaceIntervalSet {
        let mut out = base;
        if let Some(f) = self.free_by_time.get(&key) {
            let frees = f.clamped_linear(bounds);
            if !frees.is_empty() {
                out = out.union(&frees);
            }
        }
        if let Some(o) = self.occupied_by_time.get(&key) {
            let occs = o.clamped_linear(bounds);
            if !occs.is_empty() {
                out = out.subtract(&occs);
            }
        }
        out.filter_min_length(min_len)
    }

    #[inline]
    fn occupied_overlaps_at(&self, key: TimePoint<T>, space: SpaceInterval) -> bool {
        self.occupied_by_time
            .get(&key)
            .is_some_and(|set| set.overlaps(space))
    }

    pub fn occupy<Q>(
        &mut self,
        berth: &BerthOccupancy<T, Q>,
        window: TimeInterval<T>,
        space: SpaceInterval,
    ) where
        T: Zero + Copy,
        Q: QuayRead + QuayWrite + Clone + PartialEq,
    {
        if let Some(k0) = berth.predecessor_key(window.start()) {
            self.add_occupy(k0, space);
        }
        for k in berth.keys_in_open_iter(window.start(), window.end()) {
            self.add_occupy(k, space);
        }
    }

    pub fn free<Q>(
        &mut self,
        berth: &BerthOccupancy<T, Q>,
        window: TimeInterval<T>,
        space: SpaceInterval,
    ) where
        T: Zero + Copy,
        Q: QuayRead + QuayWrite + Clone + PartialEq,
    {
        if let Some(k0) = berth.predecessor_key(window.start()) {
            self.add_free(k0, space);
        }
        for k in berth.keys_in_open_iter(window.start(), window.end()) {
            self.add_free(k, space);
        }
    }
}

pub trait TimelineSlices<T: PrimInt + Signed, Q: QuayRead> {
    type KeyIter<'a>: Iterator<Item = TimePoint<T>>
    where
        Self: 'a;
    fn predecessor_key(&self, t: TimePoint<T>) -> Option<TimePoint<T>>;
    fn keys_in_open_iter(&self, start: TimePoint<T>, end: TimePoint<T>) -> Self::KeyIter<'_>;
    fn quay_at(&self, key: TimePoint<T>) -> &Q;
}

impl<T, Q> TimelineSlices<T, Q> for BerthOccupancy<T, Q>
where
    T: PrimInt + Signed + Zero + Copy,
    Q: QuayRead + QuayWrite + Clone + PartialEq,
{
    type KeyIter<'a>
        = std::vec::IntoIter<TimePoint<T>>
    where
        Self: 'a;

    #[inline]
    fn predecessor_key(&self, t: TimePoint<T>) -> Option<TimePoint<T>> {
        self.slice_predecessor_key(t)
    }

    #[inline]
    fn keys_in_open_iter(&self, start: TimePoint<T>, end: TimePoint<T>) -> Self::KeyIter<'_> {
        let mut v = Vec::new();
        self.slice_keys_in_open(start, end, &mut v);
        v.into_iter()
    }

    #[inline]
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
{
    pub fn new(berth: &'a BerthOccupancy<T, Q>, time_window: TimeInterval<T>) -> Self {
        let mut slice_keys = Vec::<TimePoint<T>>::new();
        if let Some(k0) = berth.predecessor_key(time_window.start()) {
            slice_keys.push(k0);
        }
        slice_keys.extend(berth.keys_in_open_iter(time_window.start(), time_window.end()));
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

    pub fn is_free_under(
        &self,
        space: SpaceInterval,
        overlay: Option<&BerthOccupancyOverlay<T>>,
    ) -> bool {
        for &key in &self.slice_keys {
            let q = self.berth.quay_at(key);

            if let Some(ov) = overlay {
                if ov.occupied_overlaps_at(key, space) {
                    return false;
                }
            }

            if q.check_free(space) {
                continue;
            }

            if let Some(ov) = overlay {
                let base =
                    SpaceIntervalSet::from_iter(q.iter_free_intervals(SpaceLength::new(1), space));
                let adjusted = ov.adjust_runs(key, base, space, SpaceLength::new(1));
                if adjusted.covers(space) {
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
        overlay: Option<&BerthOccupancyOverlay<T>>,
    ) -> Vec<SpaceInterval> {
        if self.slice_keys.is_empty() {
            return Vec::new();
        }

        let mut first = true;
        let mut acc = SpaceIntervalSet::new();
        let mut tmp = SpaceIntervalSet::new();

        for &key in &self.slice_keys {
            let q = self.berth.quay_at(key);

            let base = if overlay.is_some() {
                SpaceIntervalSet::from_iter(
                    q.iter_free_intervals(SpaceLength::new(1), search_space),
                )
            } else {
                SpaceIntervalSet::from_iter(q.iter_free_intervals(required_len, search_space))
            };

            let runs = if let Some(ov) = overlay {
                ov.adjust_runs(key, base, search_space, required_len)
            } else {
                base.filter_min_length(required_len)
            };

            if first {
                acc = runs;
                first = false;
            } else {
                tmp.clear();
                acc.intersection_into(&runs, &mut tmp);
                core::mem::swap(&mut acc, &mut tmp);
            }

            if acc.is_empty() {
                break;
            }
        }

        acc.into_vec()
    }
}

pub struct FreePlacementIter<T>
where
    T: PrimInt + Signed + Zero + Copy,
{
    proc_len: TimeDelta<T>,
    keys_all: Vec<TimePoint<T>>,
    runs_per_key: Vec<SpaceIntervalSet>,
    t0_keys: Vec<TimePoint<T>>,
    t0_to_ix: Vec<usize>,
    idx_t0: usize,
    idx_run: usize,
    current_t0: Option<TimePoint<T>>,
    buf_a: SpaceIntervalSet,
    buf_b: SpaceIntervalSet,
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
        overlay: Option<&'a BerthOccupancyOverlay<T>>,
    ) -> Self
    where
        Q: crate::quay::Quay + Clone + PartialEq,
        BerthOccupancy<T, Q>: TimelineSlices<T, Q>,
    {
        let mut keys_all = Vec::<TimePoint<T>>::new();
        if let Some(k0) = berth.predecessor_key(search_time.start()) {
            keys_all.push(k0);
        }
        keys_all.extend(berth.keys_in_open_iter(search_time.start(), search_time.end()));

        let mut runs_per_key: Vec<SpaceIntervalSet> = Vec::with_capacity(keys_all.len());
        for &key in &keys_all {
            let q = berth.quay_at(key);
            let base = if overlay.is_some() {
                SpaceIntervalSet::from_iter(
                    q.iter_free_intervals(SpaceLength::new(1), search_space),
                )
            } else {
                SpaceIntervalSet::from_iter(q.iter_free_intervals(len, search_space))
            };
            let runs = if let Some(ov) = overlay {
                ov.adjust_runs(key, base, search_space, len)
            } else {
                base.filter_min_length(len)
            };
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
            idx_run: 0,
            current_t0: None,
            buf_a: SpaceIntervalSet::new(),
            buf_b: SpaceIntervalSet::new(),
        }
    }

    #[inline]
    fn next_runs_for_next_t0(&mut self) -> bool {
        while self.idx_t0 < self.t0_keys.len() {
            let t0 = self.t0_keys[self.idx_t0];
            let ix0 = self.t0_to_ix[self.idx_t0];
            self.idx_t0 += 1;

            let t1 = t0 + self.proc_len;
            self.buf_a = self.runs_per_key[ix0].clone();

            let mut j = ix0 + 1;
            while j < self.keys_all.len() && self.keys_all[j] < t1 {
                if self.buf_a.is_empty() {
                    break;
                }
                self.buf_b.clear();
                self.buf_a
                    .intersection_into(&self.runs_per_key[j], &mut self.buf_b);
                core::mem::swap(&mut self.buf_a, &mut self.buf_b);
                j += 1;
            }

            if !self.buf_a.is_empty() {
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
            let cur = self.buf_a.as_slice();
            if self.idx_run < cur.len() {
                let run = cur[self.idx_run];
                self.idx_run += 1;
                let t0 = self
                    .current_t0
                    .expect("current_t0 set when cur runs available");
                return Some((t0, run));
            }
            if !self.next_runs_for_next_t0() {
                return None;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quay::BTreeMapQuay;
    use dock_alloc_core::domain::SpacePosition;

    type T = i64;
    type BO = BerthOccupancy<T, BTreeMapQuay>;

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

    #[test]
    fn set_from_vec_and_push_coalesced() {
        let s = SpaceIntervalSet::from_vec(vec![si(5, 7), si(1, 3), si(3, 4), si(2, 5)]);
        assert_eq!(s.as_slice(), &[si(1, 7)]);
        let mut s2 = SpaceIntervalSet::new();
        s2.push_coalesced(si(2, 4));
        s2.push_coalesced(si(6, 8));
        s2.push_coalesced(si(4, 6));
        assert_eq!(s2.as_slice(), &[si(2, 8)]);
    }

    #[test]
    fn set_union_subtract_intersection() {
        let a = SpaceIntervalSet::from_vec(vec![si(0, 2), si(6, 9)]);
        let b = SpaceIntervalSet::from_vec(vec![si(1, 5), si(9, 10)]);
        assert_eq!(a.union(&b).as_slice(), &[si(0, 5), si(6, 10)]);

        let a = SpaceIntervalSet::from_vec(vec![si(0, 10)]);
        let b = SpaceIntervalSet::from_vec(vec![si(2, 4), si(6, 12)]);
        assert_eq!(a.subtract(&b).as_slice(), &[si(0, 2), si(4, 6)]);

        let a = SpaceIntervalSet::from_vec(vec![si(0, 3), si(5, 10)]);
        let b = SpaceIntervalSet::from_vec(vec![si(2, 6), si(8, 12)]);
        assert_eq!(
            a.intersection(&b).as_slice(),
            &[si(2, 3), si(5, 6), si(8, 10)]
        );
    }

    #[test]
    fn set_covers_and_overlaps() {
        let s = SpaceIntervalSet::from_vec(vec![si(0, 2), si(4, 8)]);
        assert!(s.covers(si(4, 6)));
        assert!(!s.covers(si(1, 5)));
        assert!(s.overlaps(si(1, 3)));
        assert!(!s.overlaps(si(2, 4)));
    }

    #[test]
    fn timeline_slices_predecessor_and_interior_keys() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        berth.occupy(ti(5, 10), si(2, 4));

        assert_eq!(berth.slice_predecessor_key(tp(5)), Some(tp(5)));
        assert_eq!(berth.slice_predecessor_key(tp(6)), Some(tp(5)));
        assert_eq!(berth.slice_predecessor_key(tp(0)), Some(tp(0)));
        assert_eq!(berth.slice_predecessor_key(tp(-1)), None);

        let mut keys = Vec::new();
        berth.slice_keys_in_open(tp(4), tp(12), &mut keys);
        assert_eq!(keys, vec![tp(5), tp(10)]);
    }

    #[test]
    fn availability_is_free_without_overlay() {
        let quay_length = len(10);
        let berth = BO::new(quay_length);

        let view = AvailabilityView::new(&berth, ti(0, 10));
        assert!(view.is_free_under(si(0, 10), None));
        assert!(view.is_free_under(si(3, 7), None));
    }

    #[test]
    fn availability_overlay_occupy_blocks() {
        let quay_length = len(12);
        let berth = BO::new(quay_length);

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_occupy(tp(0), si(2, 5));

        let view = AvailabilityView::new(&berth, ti(0, 10));
        assert!(!view.is_free_under(si(2, 5), Some(&ov)));
        assert!(view.is_free_under(si(0, 2), Some(&ov)));
        assert!(view.is_free_under(si(5, 12), Some(&ov)));
    }

    #[test]
    fn availability_overlay_free_covers_base_occupied() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);

        berth.occupy(ti(5, 10), si(2, 6));
        let view = AvailabilityView::new(&berth, ti(5, 10));

        assert!(!view.is_free_under(si(2, 6), None));

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(2, 6));
        assert!(view.is_free_under(si(2, 6), Some(&ov)));
    }

    #[test]
    fn intersect_free_runs_overlay_union_and_subtract() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        berth.occupy(ti(5, 10), si(2, 6));
        let view = AvailabilityView::new(&berth, ti(5, 10));

        let mut ov = BerthOccupancyOverlay::new();
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

        assert_eq!(items, vec![(0, (0, 5))]);
    }

    #[test]
    fn intersect_free_runs_across_multiple_slices() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);

        berth.occupy(ti(5, 10), si(2, 6));
        berth.occupy(ti(10, 15), si(1, 3));

        let view = AvailabilityView::new(&berth, ti(5, 15));

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

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_occupy(tp(0), si(3, 5));

        let view = AvailabilityView::new(&berth, ti(2, 6));
        assert!(!view.is_free_under(si(3, 5), Some(&ov)));
        assert!(view.is_free_under(si(0, 3), Some(&ov)));
    }

    #[test]
    fn free_placement_iter_with_overlay_creates_slots() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);

        berth.occupy(ti(5, 10), si(0, 10));

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(2, 6));

        let it = FreePlacementIter::new(
            &berth,
            ti(5, 10),
            TimeDelta::new(3),
            len(3),
            si(0, 10),
            Some(&ov),
        );
        let items: Vec<(T, (usize, usize))> = it
            .map(|(t0, space)| (t0.value(), (space.start().value(), space.end().value())))
            .collect();
        assert_eq!(items, vec![(5, (2, 6))]);
    }

    #[test]
    fn overlay_key_population() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);

        berth.occupy(ti(5, 10), si(1, 2));
        let mut ov = BerthOccupancyOverlay::new();

        ov.occupy(&berth, ti(2, 9), si(3, 7));
        let keys_occ: Vec<T> = ov.occ_keys().map(|tp| tp.value()).collect();
        assert_eq!(keys_occ, vec![0, 5]);

        let mut ov2 = BerthOccupancyOverlay::new();
        ov2.free(&berth, ti(6, 12), si(2, 8));
        let keys_free: Vec<T> = ov2.free_keys().map(|tp| tp.value()).collect();
        assert_eq!(keys_free, vec![5, 10]);
    }

    #[test]
    fn fully_occupied_slice_made_feasible_by_overlay() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 10), si(0, 10));

        let view = AvailabilityView::new(&berth, ti(5, 10));
        assert!(!view.is_free_under(si(3, 7), None));

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(3, 7));
        assert!(view.is_free_under(si(3, 7), Some(&ov)));

        let runs: Vec<_> = view
            .intersect_free_runs(len(2), si(0, 10), Some(&ov))
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert_eq!(runs, vec![(3, 7)]);
    }

    #[test]
    fn subtract_touching_edges_half_open() {
        let a = SpaceIntervalSet::from_vec(vec![si(0, 2), si(4, 6)]);
        let b = SpaceIntervalSet::from_vec(vec![si(2, 4)]);
        let out = a.subtract(&b).into_vec();
        let pairs: Vec<(usize, usize)> = out
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert_eq!(pairs, vec![(0, 2), (4, 6)]);
    }

    #[test]
    fn space_interval_set_push_coalesced_edge_cases() {
        let mut s = SpaceIntervalSet::new();
        // Insert touching and overlapping in mixed order
        s.push_coalesced(si(5, 7));
        s.push_coalesced(si(1, 3));
        s.push_coalesced(si(3, 5)); // touches [1,3) and [5,7) through [3,5) ⇒ full coalesce
        s.push_coalesced(si(10, 12));
        s.push_coalesced(si(8, 10)); // touches [10,12)
        s.push_coalesced(si(7, 8)); // touches [5,7) and [8,10) transitively
        assert_eq!(s.as_slice(), &[si(1, 12)]);
    }

    #[test]
    fn overlaps_touching_and_crossing() {
        let s = SpaceIntervalSet::from_vec(vec![si(2, 5), si(7, 10)]);
        assert!(s.overlaps(si(4, 8))); // crosses both runs
        assert!(s.overlaps(si(4, 5))); // ends inside [2,5)
        assert!(s.overlaps(si(7, 8))); // starts inside [7,10)
        assert!(!s.overlaps(si(5, 7))); // touches at 5 and 7 only (half-open)
        assert!(!s.overlaps(si(1, 2))); // touches at 2 only
        assert!(!s.overlaps(si(10, 12))); // touches at 10 only
        assert!(!s.overlaps(si(0, 1))); // fully before
        assert!(!s.overlaps(si(12, 13))); // fully after
    }

    #[test]
    fn clamped_to_clips_disjoint_preserves_order() {
        let s = SpaceIntervalSet::from_vec(vec![si(0, 3), si(5, 9)]);
        let c = s.clamped_to(si(2, 7));
        assert_eq!(c.as_slice(), &[si(2, 3), si(5, 7)]);
    }

    #[test]
    fn adjust_runs_applies_min_len_filter() {
        let base = SpaceIntervalSet::from_vec(vec![si(0, 1), si(2, 4), si(6, 7)]);
        let ov: BerthOccupancyOverlay<i64> = BerthOccupancyOverlay::new();
        let out = ov.adjust_runs(tp(0), base, si(0, 10), len(2));
        assert_eq!(out.as_slice(), &[si(2, 4)]); // only length ≥ 2 remains
    }

    #[test]
    fn availability_partial_overlay_not_enough() {
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 10), si(2, 6)); // base occupied

        let view = AvailabilityView::new(&berth, ti(5, 10));
        assert!(!view.is_free_under(si(2, 6), None)); // baseline sanity

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(3, 5)); // frees only a sub-portion
        assert!(!view.is_free_under(si(2, 6), Some(&ov))); // still not fully free
    }

    #[test]
    fn overlay_free_then_occupy_precedence_same_key() {
        // Base fully occupied; overlay frees [2,7), but also occupies [4,6) → occupy wins inside
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 10), si(0, 10));

        let view = AvailabilityView::new(&berth, ti(5, 10));
        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(2, 7));
        ov.add_occupy(tp(5), si(4, 6)); // precedence: (base ∪ free) − occupy

        let runs = view
            .intersect_free_runs(len(1), si(0, 10), Some(&ov))
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect::<Vec<_>>();
        assert_eq!(runs, vec![(2, 4), (6, 7)]);
    }

    #[test]
    fn overlay_occupy_on_any_slice_blocks_is_free_under() {
        // Create slice keys 5 and 6; overlay occupies only at key=6
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 6), si(9, 10)); // just to create keys 5 and 6

        let view = AvailabilityView::new(&berth, ti(5, 7));
        // Without overlay the small rect is free
        assert!(view.is_free_under(si(0, 1), None));

        let mut ov = BerthOccupancyOverlay::new();
        ov.add_occupy(tp(6), si(0, 1)); // occupy only on the second slice
        assert!(!view.is_free_under(si(0, 1), Some(&ov))); // must be false across all slices
    }

    #[test]
    fn intersect_free_runs_three_slices_intersection() {
        // Slices ~ at 5 and 8. Intersection across [5,8) and [8,12) leaves two small runs.
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 8), si(2, 6)); // free: [0,2) ∪ [6,10)
        berth.occupy(ti(8, 12), si(6, 9)); // free: [0,6) ∪ [9,10)

        let view = AvailabilityView::new(&berth, ti(5, 12));
        let runs = view
            .intersect_free_runs(len(1), si(0, 10), None)
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect::<Vec<_>>();
        assert_eq!(runs, vec![(0, 2), (9, 10)]);
    }

    #[test]
    fn intersect_free_runs_empties_if_any_slice_has_no_space() {
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 6), si(0, 10)); // slice at 5 fully occupied, slice at 6 free

        let view = AvailabilityView::new(&berth, ti(5, 7));
        let runs = view.intersect_free_runs(len(1), si(0, 10), None);
        assert!(
            runs.is_empty(),
            "intersection across slices should be empty"
        );
    }

    #[test]
    fn free_placement_iter_multiple_t0s_with_slice_keys() {
        // Ensure we get multiple t0 values when there are multiple slice keys.
        let quay_length = len(10);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 6), si(9, 10)); // create keys 5 and 6; irrelevant to search_space

        let it = FreePlacementIter::new(
            &berth,
            ti(0, 10),         // search_time
            TimeDelta::new(3), // proc_len
            len(2),            // required length
            si(0, 5),          // search_space (keeps it independent from [9,10) occupancy)
            None,
        );

        let items: Vec<(T, (usize, usize))> = it
            .map(|(t0, space)| (t0.value(), (space.start().value(), space.end().value())))
            .collect();

        // keys_all ~ [0,5,6] → t0_keys ~ [0,5,6] since +3 ≤ 10 for each
        assert_eq!(items, vec![(0, (0, 5)), (5, (0, 5)), (6, (0, 5))]);
    }

    #[test]
    fn intersect_free_runs_overlay_creates_and_cuts_with_min_len() {
        // Base fully occupied; overlay frees two short runs, one is too short after subtract.
        let quay_length = len(12);
        let mut berth = BO::new(quay_length);
        berth.occupy(ti(5, 10), si(0, 12)); // block all

        let view = AvailabilityView::new(&berth, ti(5, 10));
        let mut ov = BerthOccupancyOverlay::new();
        ov.add_free(tp(5), si(1, 3)); // length 2
        ov.add_free(tp(5), si(7, 10)); // length 3
        ov.add_occupy(tp(5), si(8, 9)); // carve a hole inside second run → splits into [7,8) ∪ [9,10)

        // Require at least length 2: keeps [1,3) (ok), drops [7,8) and [9,10) (length 1 each)
        let runs = view
            .intersect_free_runs(len(2), si(0, 12), Some(&ov))
            .into_iter()
            .map(|r| (r.start().value(), r.end().value()))
            .collect::<Vec<_>>();
        assert_eq!(runs, vec![(1, 3)]);
    }
}
