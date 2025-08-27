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
use dock_alloc_core::domain::{SpaceInterval, TimeInterval};
use dock_alloc_model::RequestId;
use num_traits::{PrimInt, Signed};

pub struct ConstraintsView<'a, T, C, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    M: ModelAccess<T, C>,
{
    model: &'a M,
    _phantom: std::marker::PhantomData<(T, C)>,
}

impl<'a, T, C, M> ConstraintsView<'a, T, C, M>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    M: ModelAccess<T, C>,
{
    #[inline]
    pub fn new(model: &'a M) -> Self {
        Self {
            model,
            _phantom: std::marker::PhantomData,
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
