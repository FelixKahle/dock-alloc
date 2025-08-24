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

use dock_alloc_core::domain::{SpaceInterval, SpaceLength, SpacePosition};
use std::collections::BTreeMap;

pub trait QuayRead {
    type FreeIter<'a>: Iterator<Item = SpaceInterval> + 'a
    where
        Self: 'a;

    fn check_free(&self, space: SpaceInterval) -> bool;
    fn check_occupied(&self, space: SpaceInterval) -> bool;

    fn iter_free_intervals(
        &self,
        required_space: SpaceLength,
        search_range: SpaceInterval,
    ) -> Self::FreeIter<'_>;
}

pub trait QuayWrite {
    fn free(&mut self, space: SpaceInterval);
    fn occupy(&mut self, space: SpaceInterval);
}

pub trait Quay: QuayRead + QuayWrite {}
impl<T: QuayRead + QuayWrite> Quay for T {}

pub struct BTreeMapQuay {
    total: usize,
    free: BTreeMap<SpacePosition, SpacePosition>,
}

impl BTreeMapQuay {
    #[inline]
    pub fn new(total_space: SpaceLength, initially_free: bool) -> Self {
        let total = total_space.value();
        let mut free = BTreeMap::new();
        if initially_free && total > 0 {
            free.insert(SpacePosition::new(0), SpacePosition::new(total));
        }
        Self { total, free }
    }

    #[inline]
    pub fn capacity(&self) -> SpaceLength {
        SpaceLength::new(self.total)
    }

    #[inline]
    fn clamp(&self, interval: SpaceInterval) -> (SpacePosition, SpacePosition) {
        let mut start = interval.start().value();
        let mut end = interval.end().value();
        if start > end {
            std::mem::swap(&mut start, &mut end);
        }
        if start > self.total {
            start = self.total;
        }
        if end > self.total {
            end = self.total;
        }
        (SpacePosition::new(start), SpacePosition::new(end))
    }

    #[inline]
    fn coalesce(&mut self, mut start_pos: SpacePosition, mut end_pos: SpacePosition) {
        let mut tail_map = self.free.split_off(&start_pos);
        if let Some((&prev_start, &prev_end)) = self.free.range(..=start_pos).next_back()
            && prev_end >= start_pos {
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
            && prev_end > split_start {
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
                && existing_end_at_split > final_right_end {
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
    required_length: usize,
}

impl<'a> Iterator for BTreeMapFreeIter<'a> {
    type Item = SpaceInterval;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((start, original_end)) = self.pending.take() {
            let clamped_end = if original_end > self.search_end {
                self.search_end
            } else {
                original_end
            };
            if clamped_end > start && (clamped_end - start).value() >= self.required_length {
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
            if clamped_end > start && (clamped_end - start).value() >= self.required_length {
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
    fn check_free(&self, interval: SpaceInterval) -> bool {
        let (start, end) = self.clamp(interval);
        if start >= end {
            return true;
        }

        let mut current_pos = start;
        if let Some((_, &prev_end)) = self.free.range(..=current_pos).next_back()
            && prev_end > current_pos {
                current_pos = prev_end.min(end);
                if current_pos >= end {
                    return true;
                }
            }

        for (&next_start, &next_end) in self.free.range(current_pos..) {
            if current_pos >= end {
                break;
            }
            if next_start > current_pos {
                return false;
            }
            current_pos = next_end.min(end);
        }

        current_pos >= end
    }

    #[inline]
    fn check_occupied(&self, interval: SpaceInterval) -> bool {
        let (start, end) = self.clamp(interval);
        if start >= end {
            return false;
        }
        if let Some((_, &prev_end)) = self.free.range(..=start).next_back()
            && prev_end > start {
                return false;
            }
        if let Some((&next_start, _)) = self.free.range(start..).next()
            && next_start < end {
                return false;
            }
        true
    }

    fn iter_free_intervals(
        &self,
        required_space: SpaceLength,
        search_range: SpaceInterval,
    ) -> Self::FreeIter<'_> {
        let (search_start, search_end) = self.clamp(search_range);
        let required_length = required_space.value();

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
            required_length,
        }
    }
}

impl QuayWrite for BTreeMapQuay {
    #[inline]
    fn free(&mut self, interval: SpaceInterval) {
        let (start, end) = self.clamp(interval);
        if start < end {
            self.coalesce(start, end);
        }
    }

    #[inline]
    fn occupy(&mut self, interval: SpaceInterval) {
        let (start, end) = self.clamp(interval);
        if start < end {
            self.split(start, end);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dock_alloc_core::domain::{SpaceInterval, SpaceLength, SpacePosition};

    fn interval(start: usize, end: usize) -> SpaceInterval {
        SpaceInterval::new(SpacePosition::new(start), SpacePosition::new(end))
    }

    fn full_range(quay: &BTreeMapQuay) -> SpaceInterval {
        interval(0, quay.capacity().value())
    }

    fn runs_of(quay: &BTreeMapQuay) -> Vec<(usize, usize)> {
        quay.iter_free_intervals(SpaceLength::new(1), full_range(quay))
            .map(|run| (run.start().value(), run.end().value()))
            .collect()
    }

    fn assert_runs(quay: &BTreeMapQuay, expected: &[(usize, usize)]) {
        let actual_runs = runs_of(quay);
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
            let (clamped_start, clamped_end) = self.clamp(start, end);
            for index in clamped_start..clamped_end {
                self.free[index] = true;
            }
        }

        fn occupy(&mut self, start: usize, end: usize) {
            let (clamped_start, clamped_end) = self.clamp(start, end);
            for index in clamped_start..clamped_end {
                self.free[index] = false;
            }
        }

        fn runs(&self) -> Vec<(usize, usize)> {
            let mut runs = Vec::new();
            let mut index = 0;
            while index < self.size {
                if self.free[index] {
                    let mut end_index = index + 1;
                    while end_index < self.size && self.free[end_index] {
                        end_index += 1;
                    }
                    runs.push((index, end_index));
                    index = end_index;
                } else {
                    index += 1;
                }
            }
            runs
        }

        fn check_free(&self, start: usize, end: usize) -> bool {
            let (clamped_start, clamped_end) = self.clamp(start, end);
            if clamped_start >= clamped_end {
                return true;
            }
            self.free[clamped_start..clamped_end]
                .iter()
                .all(|&is_free| is_free)
        }

        fn check_occupied(&self, start: usize, end: usize) -> bool {
            let (clamped_start, clamped_end) = self.clamp(start, end);
            if clamped_start >= clamped_end {
                return false;
            }
            self.free[clamped_start..clamped_end]
                .iter()
                .all(|&is_free| !is_free)
        }
    }

    fn assert_matches_model(quay: &BTreeMapQuay, model: &RefModel) {
        let actual_runs = runs_of(quay);
        let expected_runs = model.runs();
        assert_eq!(
            actual_runs, expected_runs,
            "runs mismatch: impl={:?} model={:?}",
            actual_runs, expected_runs
        );
    }

    #[test]
    fn new_initially_occupied() {
        let quay = BTreeMapQuay::new(SpaceLength::new(10), false);
        assert_eq!(quay.capacity().value(), 10);
        assert_runs(&quay, &[]);
        assert!(quay.check_occupied(interval(0, 10)));
        assert!(!quay.check_free(interval(0, 10)));
    }

    #[test]
    fn new_initially_free() {
        let quay = BTreeMapQuay::new(SpaceLength::new(10), true);
        assert_runs(&quay, &[(0, 10)]);
        assert!(quay.check_free(interval(0, 10)));
        assert!(!quay.check_occupied(interval(0, 10)));
    }

    #[test]
    fn zero_capacity() {
        let quay = BTreeMapQuay::new(SpaceLength::new(0), true);
        assert_runs(&quay, &[]);
        assert!(quay.check_free(interval(0, 0)));
        assert!(!quay.check_occupied(interval(0, 0)));
    }

    #[test]
    fn clamp_reversed_and_oob() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(10), false);
        quay.free(interval(12, 5)); // reversed + OOB -> treated as [5,10)
        assert_runs(&quay, &[(5, 10)]);

        quay.occupy(interval(100, 100)); // empty, no-op
        assert_runs(&quay, &[(5, 10)]);

        assert!(quay.check_free(interval(7, 7)));
        assert!(!quay.check_occupied(interval(7, 7)));
    }

    #[test]
    fn coalesce_adjacent_left() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), false);
        quay.free(interval(5, 10));
        quay.free(interval(0, 5)); // adjacent left
        assert_runs(&quay, &[(0, 10)]);
    }

    #[test]
    fn coalesce_adjacent_right() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), false);
        quay.free(interval(5, 10));
        quay.free(interval(10, 15)); // adjacent right
        assert_runs(&quay, &[(5, 15)]);
    }

    #[test]
    fn coalesce_overlap_left() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), false);
        quay.free(interval(5, 10));
        quay.free(interval(0, 7)); // overlaps predecessor
        assert_runs(&quay, &[(0, 10)]);
    }

    #[test]
    fn coalesce_overlap_right() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), false);
        quay.free(interval(5, 10));
        quay.free(interval(7, 15)); // overlaps successor
        assert_runs(&quay, &[(5, 15)]);
    }

    #[test]
    fn coalesce_bridge_two_runs() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(30), false);
        quay.free(interval(0, 5));
        quay.free(interval(10, 15));
        quay.free(interval(5, 10)); // bridge both -> single [0,15)
        assert_runs(&quay, &[(0, 15)]);
    }

    #[test]
    fn coalesce_redundant_free_is_idempotent() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), false);
        quay.free(interval(2, 18));
        assert_runs(&quay, &[(2, 18)]);
        quay.free(interval(4, 16));
        assert_runs(&quay, &[(2, 18)]);
        quay.free(interval(0, 20));
        assert_runs(&quay, &[(0, 20)]);
    }

    #[test]
    fn occupy_middle_splits_in_two() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), true);
        quay.occupy(interval(5, 10));
        assert_runs(&quay, &[(0, 5), (10, 20)]);
    }

    #[test]
    fn occupy_prefix_trims_left() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), true);
        quay.occupy(interval(0, 7));
        assert_runs(&quay, &[(7, 20)]);
    }

    #[test]
    fn occupy_suffix_trims_right() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), true);
        quay.occupy(interval(12, 20));
        assert_runs(&quay, &[(0, 12)]);
    }

    #[test]
    fn occupy_all_clears_all_free() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), true);
        quay.occupy(interval(0, 20));
        assert_runs(&quay, &[]);
        assert!(quay.check_occupied(interval(0, 20)));
    }

    #[test]
    fn occupy_spans_multiple_runs() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(30), false);
        quay.free(interval(0, 5));
        quay.free(interval(10, 15));
        quay.free(interval(20, 30));
        quay.occupy(interval(3, 22));
        assert_runs(&quay, &[(0, 3), (22, 30)]);
    }

    #[test]
    fn occupy_inside_hole_is_noop() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), false);
        quay.free(interval(0, 5));
        quay.free(interval(10, 15));
        quay.occupy(interval(6, 9));
        assert_runs(&quay, &[(0, 5), (10, 15)]);
    }

    #[test]
    fn occupy_redundant_is_idempotent() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), true);
        quay.occupy(interval(5, 10));
        quay.occupy(interval(6, 9));
        quay.occupy(interval(5, 10));
        assert_runs(&quay, &[(0, 5), (10, 20)]);
    }

    #[test]
    fn check_free_covered_by_single_run() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), false);
        quay.free(interval(3, 17));
        assert!(quay.check_free(interval(5, 10)));
        assert!(!quay.check_free(interval(0, 10)));
        assert!(!quay.check_free(interval(10, 20)));
    }

    #[test]
    fn check_free_gap_between_runs() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), false);
        quay.free(interval(0, 5));
        quay.free(interval(10, 15));
        assert!(!quay.check_free(interval(4, 11)));
        assert!(quay.check_free(interval(10, 15)));
        assert!(quay.check_free(interval(0, 5)));
    }

    #[test]
    fn check_occupied_true_when_fully_occupied() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(12), true);
        quay.occupy(interval(2, 10));
        assert!(quay.check_occupied(interval(5, 9)));
        assert!(!quay.check_occupied(interval(1, 3)));
    }

    #[test]
    fn iter_clips_to_search_range_and_filters_required() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(30), false);
        quay.free(interval(0, 7));
        quay.free(interval(9, 12));
        quay.free(interval(14, 18));
        quay.free(interval(20, 29));

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
    fn iter_handles_predecessor_overlap_pending() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(25), false);
        quay.free(interval(0, 10));
        quay.free(interval(12, 20));

        let actual_runs: Vec<(usize, usize)> = quay
            .iter_free_intervals(SpaceLength::new(1), interval(5, 15))
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert_eq!(actual_runs, vec![(5, 10), (12, 15)]);
    }

    #[test]
    fn iter_yields_nothing_outside_search_or_required() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(20), false);
        quay.free(interval(0, 3));
        quay.free(interval(17, 20));

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
    fn interleaved_free_then_occupy_then_free_coalesces_back() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(50), false);
        quay.free(interval(5, 10));
        quay.free(interval(15, 20));
        quay.free(interval(25, 35));
        quay.free(interval(40, 45));
        assert_runs(&quay, &[(5, 10), (15, 20), (25, 35), (40, 45)]);

        quay.free(interval(10, 40));
        assert_runs(&quay, &[(5, 45)]);

        quay.occupy(interval(22, 28));
        assert_runs(&quay, &[(5, 22), (28, 45)]);

        quay.free(interval(20, 30));
        assert_runs(&quay, &[(5, 45)]);
    }

    #[test]
    fn free_idempotent_and_occupy_idempotent() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(30), false);
        quay.free(interval(10, 20));
        quay.free(interval(10, 20));
        assert_runs(&quay, &[(10, 20)]);

        quay.occupy(interval(12, 18));
        quay.occupy(interval(12, 18));
        assert_runs(&quay, &[(10, 12), (18, 20)]);
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
    fn randomized_model_vs_impl_small() {
        let size = 64usize;
        let mut rng = Lcg::new(0xDEADBEEFCAFEBABE);
        for &init_free in &[false, true] {
            let mut quay = BTreeMapQuay::new(SpaceLength::new(size), init_free);
            let mut model = RefModel::new(size, init_free);
            assert_matches_model(&quay, &model);

            for _ in 0..4000 {
                let op_is_free = rng.flip();
                let start = rng.gen_range(size + 10);
                let end = rng.gen_range(size + 10);
                if op_is_free {
                    quay.free(interval(start, end));
                    model.free(start, end);
                } else {
                    quay.occupy(interval(start, end));
                    model.occupy(start, end);
                }

                assert_matches_model(&quay, &model);

                let start2 = rng.gen_range(size + 10);
                let end2 = rng.gen_range(size + 10);
                assert_eq!(
                    quay.check_free(interval(start2, end2)),
                    model.check_free(start2, end2),
                    "check_free mismatch for [{},{})",
                    start2,
                    end2
                );
                assert_eq!(
                    quay.check_occupied(interval(start2, end2)),
                    model.check_occupied(start2, end2),
                    "check_occupied mismatch for [{},{})",
                    start2,
                    end2
                );

                let search_start = rng.gen_range(size + 10);
                let search_end = rng.gen_range(size + 10);
                let _ = quay
                    .iter_free_intervals(SpaceLength::new(2), interval(search_start, search_end))
                    .for_each(|_| {});
            }
        }
    }

    #[test]
    fn free_then_occupy_same_range_roundtrips() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(40), false);
        quay.free(interval(10, 30));
        assert_runs(&quay, &[(10, 30)]);
        quay.occupy(interval(10, 30));
        assert_runs(&quay, &[]);
        quay.free(interval(10, 30));
        assert_runs(&quay, &[(10, 30)]);
    }

    #[test]
    fn free_overlapping_multiple_nonadjacent_runs_merges_all() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(100), false);
        quay.free(interval(10, 20));
        quay.free(interval(30, 35));
        quay.free(interval(40, 50));
        quay.free(interval(60, 65));
        quay.free(interval(15, 62));
        assert_runs(&quay, &[(10, 65)]);
    }

    #[test]
    fn occupy_partial_head_and_tail_over_across_runs() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(40), false);
        quay.free(interval(0, 5));
        quay.free(interval(8, 15));
        quay.free(interval(20, 30));
        quay.free(interval(32, 40));
        quay.occupy(interval(3, 33));
        assert_runs(&quay, &[(0, 3), (33, 40)]);
    }

    #[test]
    fn iterator_exact_required_length_boundary() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(30), false);
        quay.free(interval(0, 3)); // len 3
        quay.free(interval(5, 7)); // len 2
        quay.free(interval(10, 16)); // len 6
        let actual_runs: Vec<_> = quay
            .iter_free_intervals(SpaceLength::new(3), interval(0, 30))
            .map(|r| (r.start().value(), r.end().value()))
            .collect();
        assert_eq!(actual_runs, vec![(0, 3), (10, 16)]);
    }

    #[test]
    fn check_free_and_occupied_on_bounds() {
        let mut quay = BTreeMapQuay::new(SpaceLength::new(10), true);
        assert!(quay.check_free(interval(0, 10)));
        assert!(!quay.check_occupied(interval(0, 10)));

        quay.occupy(interval(0, 10));
        assert!(!quay.check_free(interval(0, 10)));
        assert!(quay.check_occupied(interval(0, 10)));

        quay.free(interval(0, 0));
        assert!(quay.check_occupied(interval(0, 10)));

        quay.free(interval(0, 10));
        assert!(quay.check_free(interval(0, 10)));
    }
}
