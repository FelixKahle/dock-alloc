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

use dock_alloc_core::domain::{SpaceInterval, TimeInterval};
use dock_alloc_model::RequestId;
use num_traits::{PrimInt, Signed};

use crate::scheduling_read::ModelAccess;

pub trait ConstraintSystem<T, C, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    M: ModelAccess<T, C>,
{
    type Violation: Clone + Eq + core::fmt::Debug + core::fmt::Display + 'static;

    // Effective windows (may narrow model’s feasible windows)
    fn job_time_window(&self, id: RequestId) -> TimeInterval<T>;
    fn job_space_window(&self, id: RequestId) -> SpaceInterval;

    // Policy gates
    fn allowed_remove(&self, id: RequestId) -> Result<(), Self::Violation>;
    fn allowed_job_edit(
        &self,
        id: RequestId,
        time: &TimeInterval<T>,
        space: &SpaceInterval,
    ) -> Result<(), Self::Violation>;

    // Map planner physics failures
    fn map_overlap(&self) -> Self::Violation;
    fn map_slot_stale(&self) -> Self::Violation;
}

pub struct ConstraintsView<'a, T, C, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    M: ModelAccess<T, C>,
{
    model: &'a M,
    _phantom: core::marker::PhantomData<(T, C)>,
}

impl<'a, T, C, M> ConstraintsView<'a, T, C, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    M: ModelAccess<T, C>,
{
    pub fn new(model: &'a M) -> Self {
        Self {
            model,
            _phantom: Default::default(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefaultViolation {
    Locked,
    TimeWindow,
    SpaceWindow,
    Overlap,
    SlotStale,
}

impl core::fmt::Display for DefaultViolation {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        use DefaultViolation::*;
        match self {
            Locked => write!(f, "locked"),
            TimeWindow => write!(f, "time-window"),
            SpaceWindow => write!(f, "space-window"),
            Overlap => write!(f, "overlap"),
            SlotStale => write!(f, "slot-stale"),
        }
    }
}

impl<'a, T, C, M> ConstraintSystem<T, C, M> for ConstraintsView<'a, T, C, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    M: ModelAccess<T, C>,
{
    type Violation = DefaultViolation;

    fn job_time_window(&self, id: RequestId) -> TimeInterval<T> {
        self.model.request(id).feasible_time_window()
    }
    fn job_space_window(&self, id: RequestId) -> SpaceInterval {
        self.model.request(id).feasible_space_window()
    }

    fn allowed_remove(&self, id: RequestId) -> Result<(), Self::Violation> {
        if self.model.is_locked(id) {
            Err(DefaultViolation::Locked)
        } else {
            Ok(())
        }
    }

    fn allowed_job_edit(
        &self,
        id: RequestId,
        time: &TimeInterval<T>,
        space: &SpaceInterval,
    ) -> Result<(), Self::Violation> {
        if self.model.is_locked(id) {
            return Err(DefaultViolation::Locked);
        }
        let tw = self.job_time_window(id);
        let sw = self.job_space_window(id);
        if time.start() < tw.start() || time.end() > tw.end() {
            return Err(DefaultViolation::TimeWindow);
        }
        if space.start() < sw.start() || space.end() > sw.end() {
            return Err(DefaultViolation::SpaceWindow);
        }
        Ok(())
    }

    fn map_overlap(&self) -> Self::Violation {
        DefaultViolation::Overlap
    }
    fn map_slot_stale(&self) -> Self::Violation {
        DefaultViolation::SlotStale
    }
}
