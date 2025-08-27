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

use dock_alloc_core::domain::{SpaceLength, SpacePosition, TimeDelta, TimePoint};
use dock_alloc_model::{Assignment, Problem, ProblemEntry, Request, RequestId};
use num_traits::{PrimInt, Signed};

pub trait ModelAccess<T: PrimInt + Signed, C: PrimInt + Signed> {
    fn request(&self, id: RequestId) -> &Request<T, C>;
    fn requests(&self) -> &[Request<T, C>];
    fn assignment(&self, id: RequestId) -> Option<&Assignment<T, C>>;
    fn is_locked(&self, id: RequestId) -> bool;
}

pub trait ModelMut<T: PrimInt + Signed, C: PrimInt + Signed>: ModelAccess<T, C> {
    fn set_assignment(&mut self, id: RequestId, start_pos: SpacePosition, start_time: TimePoint<T>);
    fn clear_assignment(&mut self, id: RequestId);
    fn set_locked(&mut self, id: RequestId, locked: bool);
}

pub struct InMemoryModel<T: PrimInt + Signed, C: PrimInt + Signed> {
    requests: Vec<Request<T, C>>,           // sorted by id
    assigns: Vec<Option<Assignment<T, C>>>, // index-aligned with requests
    locked: Vec<bool>,                      // index-aligned with requests
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> InMemoryModel<T, C> {
    pub fn from_problem(problem: &Problem<T, C>) -> Self {
        let mut requests = Vec::<Request<T, C>>::new();
        for entry in problem.entries() {
            match *entry {
                ProblemEntry::Unassigned(r) => requests.push(r),
                ProblemEntry::PreAssigned(a) => requests.push(*a.request()),
            }
        }
        requests.sort_by_key(|r| r.id());
        let mut assigns = vec![None; requests.len()];
        let mut locked = vec![false; requests.len()];
        for entry in problem.entries() {
            if let ProblemEntry::PreAssigned(a) = *entry {
                let r = *a.request();
                let idx = requests
                    .binary_search_by_key(&r.id(), |x| x.id())
                    .expect("unknown RequestId during init");
                assigns[idx] = Some(a);
                locked[idx] = true;
            }
        }

        Self {
            requests,
            assigns,
            locked,
        }
    }

    #[inline]
    fn idx(&self, id: RequestId) -> usize {
        self.requests
            .binary_search_by_key(&id, |r| r.id())
            .expect("unknown RequestId")
    }

    #[inline]
    pub fn request_len(&self, id: RequestId) -> SpaceLength {
        self.request(id).length()
    }

    #[inline]
    pub fn request_proc(&self, id: RequestId) -> TimeDelta<T> {
        self.request(id).processing_duration()
    }

    #[inline]
    pub fn request_arrival(&self, id: RequestId) -> TimePoint<T> {
        self.request(id).arrival_time()
    }
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> From<&Problem<T, C>> for InMemoryModel<T, C> {
    fn from(problem: &Problem<T, C>) -> Self {
        Self::from_problem(problem)
    }
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> ModelAccess<T, C> for InMemoryModel<T, C> {
    #[inline]
    fn request(&self, id: RequestId) -> &Request<T, C> {
        &self.requests[self.idx(id)]
    }

    #[inline]
    fn requests(&self) -> &[Request<T, C>] {
        &self.requests
    }

    #[inline]
    fn assignment(&self, id: RequestId) -> Option<&Assignment<T, C>> {
        self.assigns[self.idx(id)].as_ref()
    }

    #[inline]
    fn is_locked(&self, id: RequestId) -> bool {
        self.locked[self.idx(id)]
    }
}

impl<T, C> ModelMut<T, C> for InMemoryModel<T, C>
where
    T: num_traits::PrimInt + num_traits::Signed,
    C: num_traits::PrimInt + num_traits::Signed,
{
    #[inline]
    fn set_assignment(
        &mut self,
        id: RequestId,
        start_pos: SpacePosition,
        start_time: TimePoint<T>,
    ) {
        let idx = self.idx(id);
        let r = self.requests[idx];
        self.assigns[idx] = Some(Assignment::new(r, start_pos, start_time));
    }

    #[inline]
    fn clear_assignment(&mut self, id: RequestId) {
        let idx = self.idx(id);
        self.assigns[idx] = None;
    }

    #[inline]
    fn set_locked(&mut self, id: RequestId, locked: bool) {
        let idx = self.idx(id);
        self.locked[idx] = locked;
    }
}
