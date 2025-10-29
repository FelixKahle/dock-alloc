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

use crate::berth::{
    domain::{FreeRegion, FreeSlot},
    iter::{FeasibleRegionIter, FreeSlotIter},
    overlay::{BerthOccupancyOverlay, BrandedFreeRegion, BrandedFreeSlot},
    quay::QuayRead,
};
use dock_alloc_core::{
    SolverVariable,
    space::{SpaceInterval, SpaceLength},
    time::{TimeDelta, TimeInterval},
};

type SlotsInner<'ov, 'b, 'bo, T, Q> = core::iter::Map<
    FreeSlotIter<'ov, T, BerthOccupancyOverlay<'b, 'bo, T, Q>>,
    fn(FreeSlot<T>) -> BrandedFreeSlot<'b, T>,
>;

type RegionsInner<'ov, 'b, 'bo, T, Q> = core::iter::Map<
    FeasibleRegionIter<'ov, T, BerthOccupancyOverlay<'b, 'bo, T, Q>>,
    fn(FreeRegion<T>) -> BrandedFreeRegion<'b, T>,
>;

pub struct SlotsForRequestIter<'ov, 'alw, 'b, 'bo, T, Q>
where
    T: SolverVariable,
    Q: QuayRead,
{
    berth: &'ov BerthOccupancyOverlay<'b, 'bo, T, Q>,
    windows: &'alw [SpaceInterval],
    idx: usize,
    time_interval: TimeInterval<T>,
    processing_time: TimeDelta<T>,
    len: SpaceLength,
    space_search: SpaceInterval,
    current: Option<SlotsInner<'ov, 'b, 'bo, T, Q>>,
}

impl<'ov, 'alw, 'b, 'bo, T, Q> SlotsForRequestIter<'ov, 'alw, 'b, 'bo, T, Q>
where
    T: SolverVariable,
    Q: QuayRead,
{
    pub fn new(
        berth: &'ov BerthOccupancyOverlay<'b, 'bo, T, Q>,
        windows: &'alw [SpaceInterval],
        time_interval: TimeInterval<T>,
        processing_time: TimeDelta<T>,
        len: SpaceLength,
        space_search: SpaceInterval,
    ) -> Self {
        Self {
            berth,
            windows,
            idx: 0,
            time_interval,
            processing_time,
            len,
            space_search,
            current: None,
        }
    }
}

pub struct RegionsForRequestIter<'ov, 'alw, 'b, 'bo, T, Q>
where
    T: SolverVariable,
    Q: QuayRead,
{
    berth: &'ov BerthOccupancyOverlay<'b, 'bo, T, Q>,
    windows: &'alw [SpaceInterval],
    idx: usize,
    time_interval: TimeInterval<T>,
    processing_time: TimeDelta<T>,
    len: SpaceLength,
    space_search: SpaceInterval,
    current: Option<RegionsInner<'ov, 'b, 'bo, T, Q>>,
}

impl<'ov, 'alw, 'b, 'bo, T, Q> RegionsForRequestIter<'ov, 'alw, 'b, 'bo, T, Q>
where
    T: SolverVariable,
    Q: QuayRead,
{
    pub fn new(
        berth: &'ov BerthOccupancyOverlay<'b, 'bo, T, Q>,
        windows: &'alw [SpaceInterval],
        twin: TimeInterval<T>,
        p: TimeDelta<T>,
        len: SpaceLength,
        space_search: SpaceInterval,
    ) -> Self {
        Self {
            berth,
            windows,
            idx: 0,
            time_interval: twin,
            processing_time: p,
            len,
            space_search,
            current: None,
        }
    }
}

impl<'ov, 'alw, 'b, 'bo, T, Q> Iterator for SlotsForRequestIter<'ov, 'alw, 'b, 'bo, T, Q>
where
    T: SolverVariable + Copy,
    Q: QuayRead,
{
    type Item = BrandedFreeSlot<'b, T>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(iter) = &mut self.current {
                if let Some(x) = iter.next() {
                    return Some(x);
                }
                self.current = None;
            }

            while self.idx < self.windows.len() {
                let wf = self.windows[self.idx];
                self.idx += 1;

                if let Some(swin) = self.space_search.intersection(&wf)
                    && self.time_interval.duration() >= self.processing_time
                    && swin.measure() >= self.len
                {
                    self.current = Some(self.berth.iter_free_slots(
                        self.time_interval,
                        self.processing_time,
                        self.len,
                        swin,
                    ));
                    break;
                }
            }

            self.current.as_ref()?;
        }
    }
}

impl<'ov, 'alw, 'b, 'bo, T, Q> Iterator for RegionsForRequestIter<'ov, 'alw, 'b, 'bo, T, Q>
where
    T: SolverVariable + Copy,
    Q: QuayRead,
{
    type Item = BrandedFreeRegion<'b, T>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(iter) = &mut self.current {
                if let Some(x) = iter.next() {
                    return Some(x);
                }
                self.current = None;
            }

            while self.idx < self.windows.len() {
                let wf = self.windows[self.idx];
                self.idx += 1;

                if let Some(swin) = self.space_search.intersection(&wf)
                    && self.time_interval.duration() >= self.processing_time
                    && swin.measure() >= self.len
                {
                    self.current = Some(self.berth.iter_free_regions(
                        self.time_interval,
                        self.processing_time,
                        self.len,
                        swin,
                    ));
                    break;
                }
            }

            self.current.as_ref()?;
        }
    }
}
