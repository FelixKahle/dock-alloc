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

use dock_alloc_core::space::{SpaceInterval, SpaceLength, SpacePosition};
use std::{
    collections::BTreeMap,
    fmt::{Debug, Display},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct QuayOutOfBoundsError<T> {
    violation: T,
    capacity: SpaceLength,
}

impl<T> QuayOutOfBoundsError<T> {
    #[inline]
    pub fn new(violation: T, capacity: SpaceLength) -> Self {
        Self {
            violation,
            capacity,
        }
    }

    #[inline]
    pub fn violation(&self) -> &T {
        &self.violation
    }

    #[inline]
    pub fn capacity(&self) -> SpaceLength {
        self.capacity
    }
}

impl<T: Display> Display for QuayOutOfBoundsError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Quay request {} exceeds quay capacity {} (universe [0,{}))",
            self.violation, self.capacity, self.capacity
        )
    }
}

impl<T: Debug + Display> std::error::Error for QuayOutOfBoundsError<T> {}

pub type QuaySpaceIntervalOutOfBoundsError = QuayOutOfBoundsError<SpaceInterval>;

pub trait QuayRead: Eq + Clone {
    fn new(total_space: SpaceLength, initially_free: bool) -> Self
    where
        Self: Sized;

    type FreeIter<'a>: Iterator<Item = SpaceInterval> + 'a
    where
        Self: 'a;

    fn check_free(&self, space: SpaceInterval) -> Result<bool, QuaySpaceIntervalOutOfBoundsError>;

    fn check_occupied(
        &self,
        space: SpaceInterval,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError>;

    fn capacity(&self) -> SpaceLength;

    fn universe(&self) -> SpaceInterval {
        SpaceInterval::new(
            SpacePosition::zero(),
            SpacePosition::zero() + self.capacity(),
        )
    }

    fn iter_free_intervals(
        &self,
        required_space: SpaceLength,
        search_range: SpaceInterval,
    ) -> Self::FreeIter<'_>;
}

pub trait QuayWrite {
    fn free(&mut self, space: SpaceInterval) -> Result<(), QuaySpaceIntervalOutOfBoundsError>;
    fn occupy(&mut self, space: SpaceInterval) -> Result<(), QuaySpaceIntervalOutOfBoundsError>;
}

pub trait Quay: QuayRead + QuayWrite {}
impl<T: QuayRead + QuayWrite> Quay for T {}

#[inline]
fn normalize_in_range(
    capacity: SpaceLength,
    interval: SpaceInterval,
) -> Result<(SpacePosition, SpacePosition), QuaySpaceIntervalOutOfBoundsError> {
    let start = interval.start();
    let end = interval.end();

    let cap_end = SpacePosition::zero() + capacity;
    if end > cap_end {
        return Err(QuaySpaceIntervalOutOfBoundsError::new(interval, capacity));
    }
    Ok((start, end))
}

#[inline]
fn clamp(capacity: SpaceLength, interval: SpaceInterval) -> (SpacePosition, SpacePosition) {
    let (mut start, mut end) = (interval.start(), interval.end());

    if start > end {
        std::mem::swap(&mut start, &mut end);
    }

    let min = SpacePosition::zero();
    let max = min + capacity;

    start = start.max(min).min(max);
    end = end.max(min).min(max);

    (start, end)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BTreeMapQuay {
    total: SpaceLength,
    free: BTreeMap<SpacePosition, SpacePosition>,
}

impl BTreeMapQuay {
    #[inline]
    pub fn new(total_space: SpaceLength, initially_free: bool) -> Self {
        let mut free = BTreeMap::new();
        if initially_free && total_space > SpaceLength::zero() {
            free.insert(SpacePosition::zero(), SpacePosition::zero() + total_space);
        }
        Self {
            total: total_space,
            free,
        }
    }

    #[inline]
    pub fn capacity(&self) -> SpaceLength {
        self.total
    }

    #[inline]
    fn coalesce(&mut self, mut start_pos: SpacePosition, mut end_pos: SpacePosition) {
        let mut tail_map = self.free.split_off(&start_pos);
        if let Some((&prev_start, &prev_end)) = self.free.range(..=start_pos).next_back()
            && prev_end >= start_pos
        {
            start_pos = prev_start;
            if prev_end > end_pos {
                end_pos = prev_end;
            }
            self.free.remove(&prev_start);
        }

        while let Some((&next_start, &next_end)) = tail_map.iter().next() {
            if next_start > end_pos {
                break;
            }
            tail_map.remove(&next_start);
            if next_end > end_pos {
                end_pos = next_end;
            }
        }

        self.free.insert(start_pos, end_pos);
        self.free.append(&mut tail_map);
    }

    #[inline]
    fn split(&mut self, split_start: SpacePosition, split_end: SpacePosition) {
        if split_start >= split_end {
            return;
        }
        let mut tail_map = self.free.split_off(&split_start);
        let mut new_right_end: Option<SpacePosition> = None;
        if let Some((&prev_start, &prev_end)) = self.free.range(..=split_start).next_back()
            && prev_end > split_start
        {
            self.free.remove(&prev_start);
            if prev_start < split_start {
                self.free.insert(prev_start, split_start);
            }
            if prev_end > split_end {
                new_right_end = Some(prev_end);
            }
        }
        while let Some((&next_start, &next_end)) = tail_map.iter().next() {
            if next_start >= split_end {
                break;
            }
            tail_map.remove(&next_start);
            if next_end > split_end {
                new_right_end = Some(match new_right_end {
                    Some(current_right_end) => {
                        if next_end > current_right_end {
                            next_end
                        } else {
                            current_right_end
                        }
                    }
                    None => next_end,
                });
                break;
            }
        }
        if let Some(mut final_right_end) = new_right_end {
            if let Some(existing_end_at_split) = tail_map.remove(&split_end)
                && existing_end_at_split > final_right_end
            {
                final_right_end = existing_end_at_split;
            }
            tail_map.insert(split_end, final_right_end);
        }
        self.free.append(&mut tail_map);
    }
}

pub struct BTreeMapFreeIter<'a> {
    map_iter: std::collections::btree_map::Range<'a, SpacePosition, SpacePosition>,
    pending: Option<(SpacePosition, SpacePosition)>,
    search_end: SpacePosition,
    required_length: SpaceLength,
}

impl<'a> Iterator for BTreeMapFreeIter<'a> {
    type Item = SpaceInterval;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((start, original_end)) = self.pending.take() {
            let clamped_end = if original_end > self.search_end {
                self.search_end
            } else {
                original_end
            };
            if clamped_end > start && (clamped_end - start) >= self.required_length {
                return Some(SpaceInterval::new(start, clamped_end));
            }
        }

        for (&start, &original_end) in self.map_iter.by_ref() {
            if start >= self.search_end {
                return None;
            }
            let clamped_end = if original_end > self.search_end {
                self.search_end
            } else {
                original_end
            };
            if clamped_end > start && (clamped_end - start) >= self.required_length {
                return Some(SpaceInterval::new(start, clamped_end));
            }
        }
        None
    }
}

impl QuayRead for BTreeMapQuay {
    type FreeIter<'a>
        = BTreeMapFreeIter<'a>
    where
        Self: 'a;

    #[inline]
    fn new(total_space: SpaceLength, initially_free: bool) -> Self {
        Self::new(total_space, initially_free)
    }

    #[inline]
    fn capacity(&self) -> SpaceLength {
        self.total
    }

    #[inline]
    fn check_free(
        &self,
        interval: SpaceInterval,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        let (start, end) = normalize_in_range(self.capacity(), interval)?;
        if start >= end {
            return Ok(true);
        }

        let mut current_pos = start;
        if let Some((_, &prev_end)) = self.free.range(..=current_pos).next_back()
            && prev_end > current_pos
        {
            current_pos = prev_end.min(end);
            if current_pos >= end {
                return Ok(true);
            }
        }
        for (&next_start, &next_end) in self.free.range(current_pos..) {
            if current_pos >= end {
                break;
            }
            if next_start > current_pos {
                return Ok(false);
            }
            current_pos = next_end.min(end);
        }
        Ok(current_pos >= end)
    }

    #[inline]
    fn check_occupied(
        &self,
        interval: SpaceInterval,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        let (start, end) = normalize_in_range(self.capacity(), interval)?;
        if start >= end {
            return Ok(false);
        }
        if let Some((_, &prev_end)) = self.free.range(..=start).next_back()
            && prev_end > start
        {
            return Ok(false);
        }
        if let Some((&next_start, _)) = self.free.range(start..).next()
            && next_start < end
        {
            return Ok(false);
        }
        Ok(true)
    }

    fn iter_free_intervals(
        &self,
        required_space: SpaceLength,
        search_range: SpaceInterval,
    ) -> Self::FreeIter<'_> {
        let (search_start, search_end) = clamp(self.capacity(), search_range);

        let pending =
            self.free
                .range(..=search_start)
                .next_back()
                .and_then(|(&prev_start, &prev_end)| {
                    (prev_start < search_start && prev_end > search_start)
                        .then_some((search_start, prev_end.min(search_end)))
                });

        let map_iter = self.free.range(search_start..);

        BTreeMapFreeIter {
            map_iter,
            pending,
            search_end,
            required_length: required_space,
        }
    }
}

impl QuayWrite for BTreeMapQuay {
    #[inline]
    fn free(&mut self, interval: SpaceInterval) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        let (start, end) = normalize_in_range(self.capacity(), interval)?;
        if start >= end {
            return Ok(());
        }
        self.coalesce(start, end);
        Ok(())
    }

    #[inline]
    fn occupy(&mut self, interval: SpaceInterval) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        let (start, end) = normalize_in_range(self.capacity(), interval)?;
        if start >= end {
            return Ok(());
        }
        self.split(start, end);
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BooleanVecQuay {
    total: SpaceLength,
    free: Vec<bool>, // true = free, false = occupied
}

impl BooleanVecQuay {
    #[inline]
    pub fn new(total_space: SpaceLength, initially_free: bool) -> Self {
        let size = total_space.value();
        let mut free = Vec::with_capacity(size);
        free.resize(size, initially_free);
        Self {
            total: total_space,
            free,
        }
    }

    #[inline]
    fn to_indices((start, end): (SpacePosition, SpacePosition)) -> (usize, usize) {
        (start.value(), end.value())
    }
}

pub struct BooleanVecFreeIter<'a> {
    slice: &'a [bool],
    cur: usize,
    end: usize,
    required_len: SpaceLength,
}

impl<'a> Iterator for BooleanVecFreeIter<'a> {
    type Item = SpaceInterval;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut i = self.cur;

        while i < self.end && !self.slice[i] {
            i += 1;
        }
        if i >= self.end {
            self.cur = i;
            return None;
        }

        let run_start = i;
        i += 1;
        while i < self.end && self.slice[i] {
            i += 1;
        }
        let run_end = i;

        self.cur = run_end;

        let run_len = SpaceLength::new(run_end - run_start);
        if run_len >= self.required_len {
            Some(SpaceInterval::new(
                SpacePosition::new(run_start),
                SpacePosition::new(run_end),
            ))
        } else {
            self.next()
        }
    }
}

impl QuayRead for BooleanVecQuay {
    type FreeIter<'a>
        = BooleanVecFreeIter<'a>
    where
        Self: 'a;

    #[inline]
    fn new(total_space: SpaceLength, initially_free: bool) -> Self {
        Self::new(total_space, initially_free)
    }

    #[inline]
    fn capacity(&self) -> SpaceLength {
        self.total
    }

    #[inline]
    fn check_free(
        &self,
        interval: SpaceInterval,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        let (start_pos, end_pos) = normalize_in_range(self.capacity(), interval)?;
        if start_pos >= end_pos {
            return Ok(true);
        }
        let (s, e) = Self::to_indices((start_pos, end_pos));
        Ok(self.free[s..e].iter().all(|&b| b))
    }

    #[inline]
    fn check_occupied(
        &self,
        interval: SpaceInterval,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        let (start_pos, end_pos) = normalize_in_range(self.capacity(), interval)?;
        if start_pos >= end_pos {
            return Ok(false);
        }
        let (s, e) = Self::to_indices((start_pos, end_pos));
        Ok(self.free[s..e].iter().all(|&b| !b))
    }

    #[inline]
    fn iter_free_intervals(
        &self,
        required_space: SpaceLength,
        search_range: SpaceInterval,
    ) -> Self::FreeIter<'_> {
        let (search_start, search_end) = clamp(self.capacity(), search_range);
        let (s, e) = Self::to_indices((search_start, search_end));

        BooleanVecFreeIter {
            slice: &self.free,
            cur: s,
            end: e,
            required_len: required_space,
        }
    }
}

impl QuayWrite for BooleanVecQuay {
    #[inline]
    fn free(&mut self, space: SpaceInterval) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        let (start_pos, end_pos) = normalize_in_range(self.capacity(), space)?;
        if start_pos >= end_pos {
            return Ok(());
        }
        let (s, e) = Self::to_indices((start_pos, end_pos));
        self.free[s..e].fill(true);
        Ok(())
    }

    #[inline]
    fn occupy(&mut self, space: SpaceInterval) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        let (start_pos, end_pos) = normalize_in_range(self.capacity(), space)?;
        if start_pos >= end_pos {
            return Ok(());
        }
        let (s, e) = Self::to_indices((start_pos, end_pos));
        self.free[s..e].fill(false);
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitPackedQuay {
    total: SpaceLength,
    words: Vec<u64>,
}

impl BitPackedQuay {
    const WORD_BITS: usize = u64::BITS as usize;

    #[inline]
    pub fn new(total_space: SpaceLength, initially_free: bool) -> Self {
        let nbits = total_space.value();
        let nwords = nbits.div_ceil(Self::WORD_BITS);
        let mut words = vec![if initially_free { !0u64 } else { 0u64 }; nwords];

        if let Some(last) = words.last_mut() {
            let last_bits = nbits % Self::WORD_BITS;
            if last_bits != 0 {
                *last &= Self::hi_mask(last_bits);
            }
        }

        Self {
            total: total_space,
            words,
        }
    }

    #[inline(always)]
    fn word_ix(pos: SpacePosition) -> usize {
        pos.value() / Self::WORD_BITS
    }

    #[inline(always)]
    fn bit_off(pos: SpacePosition) -> usize {
        pos.value() % Self::WORD_BITS
    }

    #[inline(always)]
    fn hi_mask(end: usize) -> u64 {
        if end == 0 {
            0
        } else if end >= Self::WORD_BITS {
            !0
        } else {
            (!0u64) >> (Self::WORD_BITS - end)
        }
    }

    #[inline(always)]
    fn lo_mask(start: usize) -> u64 {
        if start >= Self::WORD_BITS {
            0
        } else {
            (!0u64) << start
        }
    }

    #[inline(always)]
    fn range_mask(start: usize, end: usize) -> u64 {
        Self::lo_mask(start) & Self::hi_mask(end)
    }

    #[inline]
    fn set_range(&mut self, interval: SpaceInterval, make_free: bool) {
        let (start, end) = clamp(self.capacity(), interval);
        if start >= end {
            return;
        }

        let sw = Self::word_ix(start);
        let sb = Self::bit_off(start);
        let ew = Self::word_ix(end);
        let eb = Self::bit_off(end);

        if sw == ew {
            let mask = Self::range_mask(sb, eb);
            if let Some(w) = self.words.get_mut(sw) {
                if make_free {
                    *w |= mask;
                } else {
                    *w &= !mask;
                }
            }
        } else {
            if let Some(w) = self.words.get_mut(sw) {
                let left_mask = Self::lo_mask(sb);
                if make_free {
                    *w |= left_mask;
                } else {
                    *w &= !left_mask;
                }
            }

            let mid_end_excl = if eb == 0 { ew } else { ew.saturating_sub(1) };
            if mid_end_excl > sw + 1 {
                let fill = if make_free { !0u64 } else { 0u64 };
                for w in &mut self.words[sw + 1..mid_end_excl] {
                    *w = fill;
                }
            }

            if eb > 0
                && let Some(w) = self.words.get_mut(ew)
            {
                let right_mask = Self::hi_mask(eb);
                if make_free {
                    *w |= right_mask;
                } else {
                    *w &= !right_mask;
                }
            }
        }

        if let Some(last) = self.words.last_mut() {
            let last_bits = self.total.value() % Self::WORD_BITS;
            if last_bits != 0 {
                *last &= Self::hi_mask(last_bits);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitPackedFreeIter<'a> {
    quay: &'a BitPackedQuay,
    cur: SpacePosition,
    end: SpacePosition,
    required: SpaceLength,
}

impl<'a> Iterator for BitPackedFreeIter<'a> {
    type Item = SpaceInterval;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let bits = BitPackedQuay::WORD_BITS;

        while self.cur < self.end {
            let w_ix = BitPackedQuay::word_ix(self.cur);
            let off = BitPackedQuay::bit_off(self.cur);
            let mut word = *self.quay.words.get(w_ix).unwrap_or(&0);
            word &= BitPackedQuay::lo_mask(off);

            let end_ix = BitPackedQuay::word_ix(self.end);
            let end_off = BitPackedQuay::bit_off(self.end);
            if w_ix == end_ix {
                word &= BitPackedQuay::hi_mask(end_off);
            }

            if word == 0 {
                let next_word_base = ((w_ix + 1) * bits).min(self.end.value());
                self.cur = SpacePosition::new(next_word_base);
                continue;
            }

            let tz = word.trailing_zeros() as usize;
            let start_bit = tz;
            let run_start = SpacePosition::new(w_ix * bits + start_bit);
            let tail = word >> start_bit;
            let mut run_len = (!tail).trailing_zeros() as usize;
            if start_bit + run_len == bits {
                let mut ix = w_ix + 1;
                while SpacePosition::new(ix * bits) < self.end {
                    let mut w = *self.quay.words.get(ix).unwrap_or(&0);
                    if ix == end_ix {
                        w &= BitPackedQuay::hi_mask(end_off);
                    }
                    if w == !0u64 {
                        run_len += bits;
                        ix += 1;
                        if ix > end_ix {
                            break;
                        }
                    } else {
                        run_len += (!w).trailing_zeros() as usize;
                        break;
                    }
                }
            }

            let max_len = (self.end - run_start).value();
            if run_len > max_len {
                run_len = max_len;
            }

            if SpaceLength::new(run_len) >= self.required {
                let run_end = run_start + SpaceLength::new(run_len);
                self.cur = run_end; // continue after this run next time
                return Some(SpaceInterval::new(run_start, run_end));
            } else {
                self.cur = run_start + SpaceLength::new(run_len.max(1));
            }
        }

        None
    }
}

impl QuayRead for BitPackedQuay {
    type FreeIter<'a>
        = BitPackedFreeIter<'a>
    where
        Self: 'a;

    #[inline]
    fn new(total_space: SpaceLength, initially_free: bool) -> Self {
        Self::new(total_space, initially_free)
    }

    #[inline]
    fn capacity(&self) -> SpaceLength {
        self.total
    }

    #[inline]
    fn check_free(
        &self,
        interval: SpaceInterval,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        let (start, end) = normalize_in_range(self.capacity(), interval)?;
        if start >= end {
            return Ok(true);
        }

        let sw = Self::word_ix(start);
        let sb = Self::bit_off(start);
        let ew = Self::word_ix(end);
        let eb = Self::bit_off(end);

        if sw == ew {
            let mask = Self::range_mask(sb, eb);
            return Ok((self.words.get(sw).copied().unwrap_or(0) & mask) == mask);
        }
        let left_mask = Self::lo_mask(sb);
        if (self.words.get(sw).copied().unwrap_or(0) & left_mask) != left_mask {
            return Ok(false);
        }
        for &w in &self.words[sw + 1..ew] {
            if w != !0u64 {
                return Ok(false);
            }
        }
        if eb == 0 {
            Ok(true)
        } else {
            let right_mask = Self::hi_mask(eb);
            Ok((self.words.get(ew).copied().unwrap_or(0) & right_mask) == right_mask)
        }
    }

    #[inline]
    fn check_occupied(
        &self,
        interval: SpaceInterval,
    ) -> Result<bool, QuaySpaceIntervalOutOfBoundsError> {
        let (start, end) = normalize_in_range(self.capacity(), interval)?;
        if start >= end {
            return Ok(false);
        }

        let sw = Self::word_ix(start);
        let sb = Self::bit_off(start);
        let ew = Self::word_ix(end);
        let eb = Self::bit_off(end);

        if sw == ew {
            let mask = Self::range_mask(sb, eb);
            return Ok((self.words.get(sw).copied().unwrap_or(0) & mask) == 0);
        }
        let left_mask = Self::lo_mask(sb);
        if (self.words.get(sw).copied().unwrap_or(0) & left_mask) != 0 {
            return Ok(false);
        }
        for &w in &self.words[sw + 1..ew] {
            if w != 0 {
                return Ok(false);
            }
        }
        if eb == 0 {
            Ok(true)
        } else {
            let right_mask = Self::hi_mask(eb);
            Ok((self.words.get(ew).copied().unwrap_or(0) & right_mask) == 0)
        }
    }

    #[inline]
    fn iter_free_intervals(
        &self,
        required_space: SpaceLength,
        search_range: SpaceInterval,
    ) -> Self::FreeIter<'_> {
        let (start, end) = clamp(self.capacity(), search_range);
        BitPackedFreeIter {
            quay: self,
            cur: start,
            end,
            required: required_space,
        }
    }
}

impl QuayWrite for BitPackedQuay {
    #[inline]
    fn free(&mut self, space: SpaceInterval) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        let (start, end) = normalize_in_range(self.capacity(), space)?;
        if start >= end {
            return Ok(());
        }
        self.set_range(SpaceInterval::new(start, end), true);
        Ok(())
    }

    #[inline]
    fn occupy(&mut self, space: SpaceInterval) -> Result<(), QuaySpaceIntervalOutOfBoundsError> {
        let (start, end) = normalize_in_range(self.capacity(), space)?;
        if start >= end {
            return Ok(());
        }
        self.set_range(SpaceInterval::new(start, end), false);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn interval(start: usize, end: usize) -> SpaceInterval {
        SpaceInterval::new(SpacePosition::new(start), SpacePosition::new(end))
    }

    fn assert_not_free_ok<Q: QuayRead>(quay: &Q, i: SpaceInterval) {
        assert!(
            !quay.check_free(i).unwrap(),
            "expected {:?} to be not free",
            i
        );
    }

    fn assert_occupied_ok<Q: QuayRead>(quay: &Q, i: SpaceInterval) {
        assert!(
            quay.check_occupied(i).unwrap(),
            "expected {:?} to be occupied",
            i
        );
    }

    fn runs_of<Q: QuayRead>(quay: &Q, total: SpaceLength) -> Vec<(usize, usize)> {
        let search = SpaceInterval::new(SpacePosition::zero(), SpacePosition::zero() + total);
        quay.iter_free_intervals(SpaceLength::new(1), search)
            .map(|run| (run.start().value(), run.end().value()))
            .collect()
    }

    fn assert_runs<Q: QuayRead>(quay: &Q, total: SpaceLength, expected: &[(usize, usize)]) {
        let actual_runs = runs_of(quay, total);
        assert_eq!(
            actual_runs, expected,
            "expected runs {:?}, got {:?}",
            expected, actual_runs
        );
    }

    #[derive(Clone)]
    struct RefModel {
        size: usize,
        free: Vec<bool>, // true = free, false = occupied
    }

    impl RefModel {
        fn new(size: usize, initially_free: bool) -> Self {
            Self {
                size,
                free: vec![initially_free; size],
            }
        }

        fn clamp(&self, mut start: usize, mut end: usize) -> (usize, usize) {
            if start > end {
                std::mem::swap(&mut start, &mut end);
            }
            start = start.min(self.size);
            end = end.min(self.size);
            (start, end)
        }

        fn free(&mut self, start: usize, end: usize) {
            let (s, e) = self.clamp(start, end);
            for i in s..e {
                self.free[i] = true;
            }
        }

        fn occupy(&mut self, start: usize, end: usize) {
            let (s, e) = self.clamp(start, end);
            for i in s..e {
                self.free[i] = false;
            }
        }

        fn runs(&self) -> Vec<(usize, usize)> {
            let mut runs = Vec::new();
            let mut i = 0;
            while i < self.size {
                if self.free[i] {
                    let mut j = i + 1;
                    while j < self.size && self.free[j] {
                        j += 1;
                    }
                    runs.push((i, j));
                    i = j;
                } else {
                    i += 1;
                }
            }
            runs
        }

        fn check_free(&self, start: usize, end: usize) -> bool {
            let (s, e) = self.clamp(start, end);
            if s >= e {
                return true;
            }
            self.free[s..e].iter().all(|&b| b)
        }

        fn check_occupied(&self, start: usize, end: usize) -> bool {
            let (s, e) = self.clamp(start, end);
            if s >= e {
                return false;
            }
            self.free[s..e].iter().all(|&b| !b)
        }
    }

    fn assert_matches_model<Q: QuayRead>(quay: &Q, total: SpaceLength, model: &RefModel) {
        let actual_runs = runs_of(quay, total);
        let expected_runs = model.runs();
        assert_eq!(
            actual_runs, expected_runs,
            "runs mismatch: impl={:?} model={:?}",
            actual_runs, expected_runs
        );
    }

    macro_rules! test_quay_impl {
        ($modname:ident, $Q:ty) => {
            mod $modname {
                use super::*;

                type Q = $Q;

                #[test]
                fn test_new_initially_occupied() {
                    let total = SpaceLength::new(10);
                    let quay = Q::new(total, false);
                    assert_runs(&quay, total, &[]);
                    assert_occupied_ok(&quay, interval(0, 10));
                    assert_not_free_ok(&quay, interval(0, 10));
                }

                #[test]
                fn test_new_initially_free() {
                    let total = SpaceLength::new(10);
                    let quay = Q::new(total, true);
                    assert_runs(&quay, total, &[(0, 10)]);
                    assert!(quay.check_free(interval(0, 10)).unwrap());
                    assert!(!quay.check_occupied(interval(0, 10)).unwrap());
                }

                #[test]
                fn test_zero_capacity() {
                    let total = SpaceLength::new(0);
                    let quay = Q::new(total, true);
                    assert_runs(&quay, total, &[]);
                    assert_eq!(quay.check_free(interval(0, 0)).unwrap(), true);
                    assert_eq!(quay.check_occupied(interval(0, 0)).unwrap(), false);
                }

                #[test]
                fn test_clamp_reversed_and_oob() {
                    let total = SpaceLength::new(10);
                    let mut quay = Q::new(total, false);

                    // OOB reversed -> error, and quay unchanged
                    assert!(quay.free(interval(12, 5)).is_err());
                    assert_runs(&quay, total, &[]);

                    // Empty but OOB -> error
                    assert!(quay.check_free(interval(100, 100)).is_err());
                    assert!(quay.occupy(interval(100, 100)).is_err());
                    assert_runs(&quay, total, &[]);

                    // Empty in-range -> allowed and no-op
                    assert!(quay.check_free(interval(7, 7)).unwrap());
                    assert!(!quay.check_occupied(interval(7, 7)).unwrap());

                    // Reversed but in-range -> normalize and apply
                    quay.free(interval(8, 5)).unwrap(); // becomes [5,8)
                    assert_runs(&quay, total, &[(5, 8)]);
                }

                #[test]
                fn test_coalesce_adjacent_left() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(5, 10)).unwrap();
                    quay.free(interval(0, 5)).unwrap(); // adjacent left
                    assert_runs(&quay, total, &[(0, 10)]);
                }

                #[test]
                fn test_coalesce_adjacent_right() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(5, 10)).unwrap();
                    quay.free(interval(10, 15)).unwrap(); // adjacent right
                    assert_runs(&quay, total, &[(5, 15)]);
                }

                #[test]
                fn test_coalesce_overlap_left() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(5, 10)).unwrap();
                    quay.free(interval(0, 7)).unwrap(); // overlaps predecessor
                    assert_runs(&quay, total, &[(0, 10)]);
                }

                #[test]
                fn test_coalesce_overlap_right() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(5, 10)).unwrap();
                    quay.free(interval(7, 15)).unwrap(); // overlaps successor
                    assert_runs(&quay, total, &[(5, 15)]);
                }

                #[test]
                fn test_coalesce_bridge_two_runs() {
                    let total = SpaceLength::new(30);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(0, 5)).unwrap();
                    quay.free(interval(10, 15)).unwrap();
                    quay.free(interval(5, 10)).unwrap(); // bridge both -> single [0,15)
                    assert_runs(&quay, total, &[(0, 15)]);
                }

                #[test]
                fn test_coalesce_redundant_free_is_idempotent() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(2, 18)).unwrap();
                    assert_runs(&quay, total, &[(2, 18)]);
                    quay.free(interval(4, 16)).unwrap();
                    assert_runs(&quay, total, &[(2, 18)]);
                    quay.free(interval(0, 20)).unwrap();
                    assert_runs(&quay, total, &[(0, 20)]);
                }

                #[test]
                fn test_occupy_middle_splits_in_two() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, true);
                    quay.occupy(interval(5, 10)).unwrap();
                    assert_runs(&quay, total, &[(0, 5), (10, 20)]);
                }

                #[test]
                fn test_occupy_prefix_trims_left() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, true);
                    quay.occupy(interval(0, 7)).unwrap();
                    assert_runs(&quay, total, &[(7, 20)]);
                }

                #[test]
                fn test_occupy_suffix_trims_right() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, true);
                    quay.occupy(interval(12, 20)).unwrap();
                    assert_runs(&quay, total, &[(0, 12)]);
                }

                #[test]
                fn test_occupy_all_clears_all_free() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, true);
                    quay.occupy(interval(0, 20)).unwrap();
                    assert_runs(&quay, total, &[]);
                    assert_occupied_ok(&quay, interval(0, 20));
                }

                #[test]
                fn test_occupy_spans_multiple_runs() {
                    let total = SpaceLength::new(30);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(0, 5)).unwrap();
                    quay.free(interval(10, 15)).unwrap();
                    quay.free(interval(20, 30)).unwrap();
                    quay.occupy(interval(3, 22)).unwrap();
                    assert_runs(&quay, total, &[(0, 3), (22, 30)]);
                }

                #[test]
                fn test_occupy_inside_hole_is_noop() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(0, 5)).unwrap();
                    quay.free(interval(10, 15)).unwrap();
                    quay.occupy(interval(6, 9)).unwrap();
                    assert_runs(&quay, total, &[(0, 5), (10, 15)]);
                }

                #[test]
                fn test_occupy_redundant_is_idempotent() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, true);
                    quay.occupy(interval(5, 10)).unwrap();
                    quay.occupy(interval(6, 9)).unwrap();
                    quay.occupy(interval(5, 10)).unwrap();
                    assert_runs(&quay, total, &[(0, 5), (10, 20)]);
                }

                #[test]
                fn test_check_free_covered_by_single_run() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(3, 17)).unwrap();
                    assert!(quay.check_free(interval(5, 10)).unwrap());
                    assert_not_free_ok(&quay, interval(0, 10));
                    assert!(!quay.check_free(interval(10, 20)).unwrap());
                }

                #[test]
                fn test_check_free_gap_between_runs() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(0, 5)).unwrap();
                    quay.free(interval(10, 15)).unwrap();
                    assert!(!quay.check_free(interval(4, 11)).unwrap());
                    assert!(quay.check_free(interval(10, 15)).unwrap());
                    assert!(quay.check_free(interval(0, 5)).unwrap());
                }

                #[test]
                fn test_check_occupied_true_when_fully_occupied() {
                    let total = SpaceLength::new(12);
                    let mut quay = Q::new(total, true);
                    quay.occupy(interval(2, 10)).unwrap();
                    assert!(quay.check_occupied(interval(5, 9)).unwrap());
                    assert!(!quay.check_occupied(interval(1, 3)).unwrap());
                }

                #[test]
                fn test_iter_clips_to_search_range_and_filters_required() {
                    let total = SpaceLength::new(30);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(0, 7)).unwrap();
                    quay.free(interval(9, 12)).unwrap();
                    quay.free(interval(14, 18)).unwrap();
                    quay.free(interval(20, 29)).unwrap();

                    let actual_runs: Vec<(usize, usize)> = quay
                        .iter_free_intervals(SpaceLength::new(3), interval(5, 22))
                        .map(|r| (r.start().value(), r.end().value()))
                        .collect();
                    assert_eq!(actual_runs, vec![(9, 12), (14, 18)]);

                    let actual_runs_2: Vec<(usize, usize)> = quay
                        .iter_free_intervals(SpaceLength::new(5), interval(5, 22))
                        .map(|r| (r.start().value(), r.end().value()))
                        .collect();
                    assert!(actual_runs_2.is_empty());
                }

                #[test]
                fn test_iter_handles_predecessor_overlap_pending() {
                    let total = SpaceLength::new(25);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(0, 10)).unwrap();
                    quay.free(interval(12, 20)).unwrap();

                    let actual_runs: Vec<(usize, usize)> = quay
                        .iter_free_intervals(SpaceLength::new(1), interval(5, 15))
                        .map(|r| (r.start().value(), r.end().value()))
                        .collect();
                    assert_eq!(actual_runs, vec![(5, 10), (12, 15)]);
                }

                #[test]
                fn test_iter_yields_nothing_outside_search_or_required() {
                    let total = SpaceLength::new(20);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(0, 3)).unwrap();
                    quay.free(interval(17, 20)).unwrap();

                    let actual_runs: Vec<_> = quay
                        .iter_free_intervals(SpaceLength::new(1), interval(5, 7))
                        .collect();
                    assert!(actual_runs.is_empty());

                    let actual_runs_2: Vec<_> = quay
                        .iter_free_intervals(SpaceLength::new(10), interval(0, 20))
                        .collect();
                    assert!(actual_runs_2.is_empty());
                }

                #[test]
                fn test_interleaved_free_then_occupy_then_free_coalesces_back() {
                    let total = SpaceLength::new(50);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(5, 10)).unwrap();
                    quay.free(interval(15, 20)).unwrap();
                    quay.free(interval(25, 35)).unwrap();
                    quay.free(interval(40, 45)).unwrap();
                    assert_runs(&quay, total, &[(5, 10), (15, 20), (25, 35), (40, 45)]);

                    quay.free(interval(10, 40)).unwrap();
                    assert_runs(&quay, total, &[(5, 45)]);

                    quay.occupy(interval(22, 28)).unwrap();
                    assert_runs(&quay, total, &[(5, 22), (28, 45)]);

                    quay.free(interval(20, 30)).unwrap();
                    assert_runs(&quay, total, &[(5, 45)]);
                }

                #[test]
                fn test_free_idempotent_and_occupy_idempotent() {
                    let total = SpaceLength::new(30);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(10, 20)).unwrap();
                    quay.free(interval(10, 20)).unwrap();
                    assert_runs(&quay, total, &[(10, 20)]);

                    quay.occupy(interval(12, 18)).unwrap();
                    quay.occupy(interval(12, 18)).unwrap();
                    assert_runs(&quay, total, &[(10, 12), (18, 20)]);
                }

                struct Lcg(u64);
                impl Lcg {
                    fn new(seed: u64) -> Self {
                        Self(seed)
                    }
                    fn next(&mut self) -> u64 {
                        self.0 = self.0.wrapping_mul(1103515245).wrapping_add(12345);
                        self.0
                    }
                    fn gen_range(&mut self, upper_bound: usize) -> usize {
                        if upper_bound == 0 {
                            0
                        } else {
                            (self.next() as usize) % upper_bound
                        }
                    }
                    fn flip(&mut self) -> bool {
                        (self.next() & 1) == 1
                    }
                }

                #[test]
                fn test_randomized_model_vs_impl_small() {
                    let size = 64usize;
                    let total = SpaceLength::new(size);
                    let mut rng = Lcg::new(0xDEADBEEFCAFEBABE);
                    for &init_free in &[false, true] {
                        let mut quay = Q::new(total, init_free);
                        let mut model = RefModel::new(size, init_free);
                        assert_matches_model(&quay, total, &model);

                        for _ in 0..4000 {
                            let op_is_free = rng.flip();
                            let start = rng.gen_range(size + 10);
                            let end = rng.gen_range(size + 10);

                            if op_is_free {
                                let res = quay.free(interval(start, end));
                                if res.is_ok() {
                                    model.free(start, end);
                                } else {
                                    // OOB by policy: do not mutate model
                                }
                            } else {
                                let res = quay.occupy(interval(start, end));
                                if res.is_ok() {
                                    model.occupy(start, end);
                                }
                            }

                            assert_matches_model(&quay, total, &model);

                            // Queries: treat OOB as error (already handled in your new code below)
                            let start2 = rng.gen_range(size + 10);
                            let end2 = rng.gen_range(size + 10);
                            let (_, b) = if start2 <= end2 {
                                (start2, end2)
                            } else {
                                (end2, start2)
                            };
                            let in_range = b <= size;
                            let r_free = quay.check_free(interval(start2, end2));
                            let r_occ = quay.check_occupied(interval(start2, end2));

                            if in_range {
                                assert_eq!(r_free.unwrap(), model.check_free(start2, end2));
                                assert_eq!(r_occ.unwrap(), model.check_occupied(start2, end2));
                            } else {
                                assert!(r_free.is_err());
                                assert!(r_occ.is_err());
                            }

                            // Iteration test can stay as-is; iter_free_intervals clamps the search range.
                            let search_start = rng.gen_range(size + 10);
                            let search_end = rng.gen_range(size + 10);
                            let _ = quay
                                .iter_free_intervals(
                                    SpaceLength::new(2),
                                    interval(search_start, search_end),
                                )
                                .for_each(|_| {});
                        }
                    }
                }

                #[test]
                fn test_free_then_occupy_same_range_roundtrips() {
                    let total = SpaceLength::new(40);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(10, 30)).unwrap();
                    assert_runs(&quay, total, &[(10, 30)]);
                    quay.occupy(interval(10, 30)).unwrap();
                    assert_runs(&quay, total, &[]);
                    quay.free(interval(10, 30)).unwrap();
                    assert_runs(&quay, total, &[(10, 30)]);
                }

                #[test]
                fn test_free_overlapping_multiple_nonadjacent_runs_merges_all() {
                    let total = SpaceLength::new(100);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(10, 20)).unwrap();
                    quay.free(interval(30, 35)).unwrap();
                    quay.free(interval(40, 50)).unwrap();
                    quay.free(interval(60, 65)).unwrap();
                    quay.free(interval(15, 62)).unwrap();
                    assert_runs(&quay, total, &[(10, 65)]);
                }

                #[test]
                fn test_occupy_partial_head_and_tail_over_across_runs() {
                    let total = SpaceLength::new(40);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(0, 5)).unwrap();
                    quay.free(interval(8, 15)).unwrap();
                    quay.free(interval(20, 30)).unwrap();
                    quay.free(interval(32, 40)).unwrap();
                    quay.occupy(interval(3, 33)).unwrap();
                    assert_runs(&quay, total, &[(0, 3), (33, 40)]);
                }

                #[test]
                fn test_iterator_exact_required_length_boundary() {
                    let total = SpaceLength::new(30);
                    let mut quay = Q::new(total, false);
                    quay.free(interval(0, 3)).unwrap(); // len 3
                    quay.free(interval(5, 7)).unwrap(); // len 2
                    quay.free(interval(10, 16)).unwrap(); // len 6

                    let actual_runs: Vec<_> = quay
                        .iter_free_intervals(SpaceLength::new(3), interval(0, 30))
                        .map(|r| (r.start().value(), r.end().value()))
                        .collect();
                    assert_eq!(actual_runs, vec![(0, 3), (10, 16)]);
                }

                #[test]
                fn test_check_free_and_occupied_on_bounds() {
                    let total = SpaceLength::new(10);
                    let mut quay = Q::new(total, true);
                    assert!(quay.check_free(interval(0, 10)).unwrap());
                    assert!(!quay.check_occupied(interval(0, 10)).unwrap());

                    quay.occupy(interval(0, 10)).unwrap();
                    assert_not_free_ok(&quay, interval(0, 10));
                    assert_occupied_ok(&quay, interval(0, 10));

                    quay.free(interval(0, 0)).unwrap();
                    assert_occupied_ok(&quay, interval(0, 10));

                    quay.free(interval(0, 10)).unwrap();
                    assert!(quay.check_free(interval(0, 10)).unwrap());
                }
            }
        };
    }

    test_quay_impl!(btree_quay_tests, BTreeMapQuay);
    test_quay_impl!(boolvec_quay_tests, BooleanVecQuay);
    test_quay_impl!(bitpacked_quay_tests, BitPackedQuay);
}
