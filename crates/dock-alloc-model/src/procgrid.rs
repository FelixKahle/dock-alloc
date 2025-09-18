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

use crate::err::{EmptyProcessingTimeGridError, ProcessingTimeGridOutOfBoundsError};
use dock_alloc_core::{
    SolverVariable,
    space::{SpaceLength, SpacePosition},
    time::TimeDelta,
};
use std::ops::Index;

#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PerSegmentVec<T: SolverVariable>(Vec<TimeDelta<T>>);

impl<T: SolverVariable> PerSegmentVec<T> {
    #[inline]
    pub fn as_slice(&self) -> &[TimeDelta<T>] {
        &self.0
    }

    #[inline]
    pub fn len(&self) -> SpaceLength {
        self.0.len().into()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    pub fn get(&self, pos: SpacePosition) -> Option<&TimeDelta<T>> {
        self.0.get(pos.value())
    }

    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, TimeDelta<T>> {
        self.0.iter()
    }
}

impl<T: SolverVariable> Index<SpacePosition> for PerSegmentVec<T> {
    type Output = TimeDelta<T>;

    fn index(&self, index: SpacePosition) -> &Self::Output {
        &self.0[index.value()]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProcessingTimeGrid<T: SolverVariable> {
    Constant(TimeDelta<T>),
    PerSegment(PerSegmentVec<T>),
}

impl<T: SolverVariable> ProcessingTimeGrid<T> {
    #[inline]
    pub fn constant(d: TimeDelta<T>) -> Self {
        Self::Constant(d)
    }

    #[inline]
    pub fn per_segment(v: Vec<TimeDelta<T>>) -> Result<Self, EmptyProcessingTimeGridError> {
        if v.is_empty() {
            return Err(EmptyProcessingTimeGridError);
        }
        Ok(Self::PerSegment(PerSegmentVec(v)))
    }

    #[inline]
    pub fn duration_at(
        &self,
        pos: SpacePosition,
    ) -> Result<TimeDelta<T>, ProcessingTimeGridOutOfBoundsError> {
        match self {
            ProcessingTimeGrid::Constant(d) => Ok(*d),
            ProcessingTimeGrid::PerSegment(v) => v
                .get(pos)
                .copied()
                .ok_or(ProcessingTimeGridOutOfBoundsError::new(pos, v.len())),
        }
    }
}

impl<T: SolverVariable> std::fmt::Display for ProcessingTimeGrid<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProcessingTimeGrid::Constant(d) => write!(f, "Constant({})", d),
            ProcessingTimeGrid::PerSegment(v) => {
                let segments_str = v
                    .iter()
                    .map(|d| d.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "PerSegment([{}])", segments_str)
            }
        }
    }
}
