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

use dock_alloc_core::domain::{
    SpaceInterval, SpaceLength, SpacePosition, TimeDelta, TimeInterval, TimePoint,
};
use dock_alloc_model::{Assignment, Problem, ProblemEntry, Request, RequestId};
use num_traits::{PrimInt, Signed};
use std::fmt::Display;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AssignmentView<T: PrimInt + Signed> {
    start_pos: SpacePosition,
    start_time: TimePoint<T>,
}

impl<T: PrimInt + Signed + Display> Display for AssignmentView<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "AssignmentView(start_pos: {}, start_time: {})",
            self.start_pos, self.start_time
        )
    }
}

impl<T: PrimInt + Signed> AssignmentView<T> {
    #[inline]
    pub fn new(start_pos: SpacePosition, start_time: TimePoint<T>) -> Self {
        Self {
            start_pos,
            start_time,
        }
    }
    #[inline]
    pub fn start_pos(&self) -> SpacePosition {
        self.start_pos
    }
    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }
}

pub trait SchedulingRead<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    fn request_length(&self, id: RequestId) -> SpaceLength;
    fn request_processing_duration(&self, id: RequestId) -> TimeDelta<T>;
    fn request_feasible_time_window(&self, id: RequestId) -> TimeInterval<T>;
    fn request_feasible_space_window(&self, id: RequestId) -> SpaceInterval;
    fn current_assignment_of_request(&self, id: RequestId) -> Option<AssignmentView<T>>;
    fn is_request_locked(&self, id: RequestId) -> bool;
}

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
    pub fn request_arrival_time(&self, id: RequestId) -> TimePoint<T> {
        self.requests[self.idx(id)].arrival_time()
    }
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> From<&Problem<T, C>> for InMemoryModel<T, C> {
    fn from(problem: &Problem<T, C>) -> Self {
        Self::from_problem(problem)
    }
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> SchedulingRead<T, C> for InMemoryModel<T, C> {
    #[inline]
    fn request_length(&self, id: RequestId) -> SpaceLength {
        self.requests[self.idx(id)].length()
    }

    #[inline]
    fn request_processing_duration(&self, id: RequestId) -> TimeDelta<T> {
        self.requests[self.idx(id)].processing_duration()
    }

    #[inline]
    fn request_feasible_time_window(&self, id: RequestId) -> TimeInterval<T> {
        self.requests[self.idx(id)].feasible_time_window()
    }

    #[inline]
    fn request_feasible_space_window(&self, id: RequestId) -> SpaceInterval {
        self.requests[self.idx(id)].feasible_space_window()
    }

    #[inline]
    fn current_assignment_of_request(&self, id: RequestId) -> Option<AssignmentView<T>> {
        self.assigns[self.idx(id)]
            .as_ref()
            .map(|a| AssignmentView::new(a.start_position(), a.start_time()))
    }

    #[inline]
    fn is_request_locked(&self, id: RequestId) -> bool {
        self.locked[self.idx(id)]
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
    T: PrimInt + Signed,
    C: PrimInt + Signed,
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
