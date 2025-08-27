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

use crate::model_access::ModelAccess;
use crate::occ::BerthOccupancy;
use crate::quay::Quay;
use dock_alloc_core::domain::{SpaceInterval, TimeInterval};
use dock_alloc_model::RequestId;
use num_traits::{PrimInt, Signed};
use std::marker::PhantomData;

pub struct ConstraintsView<
    'a,
    T: PrimInt + Signed,
    Q: Quay,
    M: ModelAccess<T, C>,
    C: PrimInt + Signed,
> {
    pub berth: &'a BerthOccupancy<T, Q>,
    pub model: &'a M,
    _phantom: PhantomData<C>,
}

impl<'a, T: PrimInt + Signed, Q, M, C: PrimInt + Signed> ConstraintsView<'a, T, Q, M, C>
where
    T: Copy + Ord,
    Q: Quay,
    M: ModelAccess<T, C>,
{
    #[inline]
    pub fn new(berth: &'a BerthOccupancy<T, Q>, model: &'a M) -> Self {
        Self {
            berth,
            model,
            _phantom: PhantomData,
        }
    }

    #[inline]
    pub fn allowed_job_edit(
        &self,
        id: RequestId,
        _time: &TimeInterval<T>,
        _space: &SpaceInterval,
    ) -> bool {
        !self.model.is_locked(id)
    }

    #[inline]
    pub fn job_time_window(&self, id: RequestId) -> TimeInterval<T> {
        self.model.request(id).feasible_time_window()
    }

    #[inline]
    pub fn job_space_window(&self, id: RequestId) -> SpaceInterval {
        self.model.request(id).feasible_space_window()
    }
}
