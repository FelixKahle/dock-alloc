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

use std::fmt::Display;

use dock_alloc_core::{
    SolverVariable,
    cost::Cost,
    space::{SpaceLength, SpacePosition},
    time::{TimeDelta, TimePoint},
};

use crate::{
    id::RequestId,
    req::{AnyRequest, AnyRequestRef, Fixed, Kind, Movable, Request},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assignment<K: Kind, T = i64, C = i64>
where
    T: SolverVariable,
    C: SolverVariable,
{
    request: Request<K, T, C>,
    start_position: SpacePosition,
    start_time: TimePoint<T>,
}

impl<K: Kind, T: SolverVariable, C: SolverVariable> Assignment<K, T, C> {
    #[inline]
    pub fn new(
        request: Request<K, T, C>,
        start_position: SpacePosition,
        start_time: TimePoint<T>,
    ) -> Self {
        Self {
            request,
            start_position,
            start_time,
        }
    }

    #[inline]
    pub fn request(&self) -> &Request<K, T, C> {
        &self.request
    }

    #[inline]
    pub fn start_position(&self) -> SpacePosition {
        self.start_position
    }

    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.request.id()
    }

    #[inline]
    pub fn typed_id(&self) -> K::Id {
        self.request.typed_id()
    }

    #[inline]
    pub fn waiting_time(&self) -> TimeDelta<T> {
        (self.start_time() - self.request.arrival_time()).max(TimeDelta::zero())
    }

    #[inline]
    pub fn waiting_cost(&self) -> Cost<C>
    where
        C: TryFrom<T>,
    {
        let waiting_time = self.waiting_time();
        let scalar: C = C::try_from(waiting_time.value())
            .ok()
            .expect("waiting time does not fit in C");
        self.request().cost_per_delay() * scalar
    }

    #[inline]
    pub fn position_deviation(&self) -> SpaceLength {
        (self.start_position() - self.request.target_position()).abs()
    }

    #[inline]
    pub fn position_deviation_cost(&self) -> Cost<C>
    where
        C: TryFrom<usize>,
    {
        let deviation = self.position_deviation();
        let scalar: C = C::try_from(deviation.value())
            .ok()
            .expect("deviation does not fit in C");
        self.request().cost_per_position_deviation() * scalar
    }

    #[inline]
    pub fn cost(&self) -> Cost<C>
    where
        C: TryFrom<T> + TryFrom<usize>,
    {
        self.waiting_cost() + self.position_deviation_cost()
    }

    #[inline]
    pub fn as_ref(&self) -> AssignmentRef<'_, K, T, C> {
        AssignmentRef::new(&self.request, self.start_position, self.start_time)
    }
}

impl<K: Kind, T: SolverVariable + Display, C: SolverVariable + Display> Display
    for Assignment<K, T, C>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} Assignment(request_id: {}, start_position: {}, start_time: {})",
            K::NAME,
            self.request.id(),
            self.start_position,
            self.start_time
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentRef<'a, K: Kind, T = i64, C = i64>
where
    T: SolverVariable,
    C: SolverVariable,
{
    request: &'a Request<K, T, C>,
    start_position: SpacePosition,
    start_time: TimePoint<T>,
}

impl<'a, K: Kind, T: SolverVariable, C: SolverVariable> AssignmentRef<'a, K, T, C> {
    #[inline]
    pub fn new(
        request: &'a Request<K, T, C>,
        start_position: SpacePosition,
        start_time: TimePoint<T>,
    ) -> Self {
        Self {
            request,
            start_position,
            start_time,
        }
    }

    #[inline]
    pub fn request(&self) -> &'a Request<K, T, C> {
        self.request
    }

    #[inline]
    pub fn start_position(&self) -> SpacePosition {
        self.start_position
    }

    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.request.id()
    }

    #[inline]
    pub fn typed_id(&self) -> K::Id {
        self.request.typed_id()
    }

    #[inline]
    pub fn waiting_time(&self) -> TimeDelta<T> {
        (self.start_time() - self.request.arrival_time()).max(TimeDelta::zero())
    }

    #[inline]
    pub fn waiting_cost(&self) -> Cost<C>
    where
        C: TryFrom<T>,
    {
        let waiting_time = self.waiting_time();
        let scalar: C = C::try_from(waiting_time.value())
            .ok()
            .expect("waiting time does not fit in C");
        self.request().cost_per_delay() * scalar
    }

    #[inline]
    pub fn position_deviation(&self) -> SpaceLength {
        (self.start_position() - self.request.target_position()).abs()
    }

    #[inline]
    pub fn position_deviation_cost(&self) -> Cost<C>
    where
        C: TryFrom<usize>,
    {
        let deviation = self.position_deviation();
        let scalar: C = C::try_from(deviation.value())
            .ok()
            .expect("deviation does not fit in C");
        self.request().cost_per_position_deviation() * scalar
    }

    #[inline]
    pub fn cost(&self) -> Cost<C>
    where
        C: TryFrom<T> + TryFrom<usize>,
    {
        self.waiting_cost() + self.position_deviation_cost()
    }

    #[inline]
    pub fn to_owned(&self) -> Assignment<K, T, C> {
        Assignment::new(self.request.clone(), self.start_position, self.start_time)
    }

    #[inline]
    pub fn into_owned(self) -> Assignment<K, T, C> {
        Assignment::new(self.request.clone(), self.start_position, self.start_time)
    }
}

impl<'a, K: Kind, T: SolverVariable + Display, C: SolverVariable + Display> Display
    for AssignmentRef<'a, K, T, C>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} AssignmentRef(request_id: {}, start_position: {}, start_time: {})",
            K::NAME,
            self.request.id(),
            self.start_position,
            self.start_time
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AnyAssignment<T = i64, C = i64>
where
    T: SolverVariable,
    C: SolverVariable,
{
    request: AnyRequest<T, C>,
    start_position: SpacePosition,
    start_time: TimePoint<T>,
}

impl<T: SolverVariable, C: SolverVariable> Display for AnyAssignment<T, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "AnyAssignment(request_id: {}, start_position: {}, start_time: {})",
            self.request.id(),
            self.start_position,
            self.start_time
        )
    }
}

impl<T, C> AnyAssignment<T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    fn new(
        request: AnyRequest<T, C>,
        start_position: SpacePosition,
        start_time: TimePoint<T>,
    ) -> Self {
        Self {
            request,
            start_position,
            start_time,
        }
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.request.id()
    }

    #[inline]
    pub fn request(&self) -> &AnyRequest<T, C> {
        &self.request
    }

    #[inline]
    pub fn start_position(&self) -> SpacePosition {
        self.start_position
    }

    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }

    #[inline]
    pub fn into_ref<'a>(&'a self) -> AnyAssignmentRef<'a, T, C> {
        let request = match &self.request {
            AnyRequest::Movable(r) => AnyRequestRef::Movable(r),
            AnyRequest::Fixed(r) => AnyRequestRef::Fixed(r),
        };
        AnyAssignmentRef {
            request,
            start_position: self.start_position,
            start_time: self.start_time,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AnyAssignmentRef<'a, T = i64, C = i64>
where
    T: SolverVariable,
    C: SolverVariable,
{
    request: AnyRequestRef<'a, T, C>,
    start_position: SpacePosition,
    start_time: TimePoint<T>,
}

impl<'a, T: SolverVariable + Display, C: SolverVariable + Display> Display
    for AnyAssignmentRef<'a, T, C>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "AnyAssignmentRef(request_id: {}, start_position: {}, start_time: {})",
            self.request.id(),
            self.start_position,
            self.start_time
        )
    }
}

impl<'a, T, C> AnyAssignmentRef<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    #[inline]
    fn new(
        request: AnyRequestRef<'a, T, C>,
        start_position: SpacePosition,
        start_time: TimePoint<T>,
    ) -> Self {
        Self {
            request,
            start_position,
            start_time,
        }
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.request.id()
    }

    #[inline]
    pub fn request(&self) -> &AnyRequestRef<'a, T, C> {
        &self.request
    }

    #[inline]
    pub fn start_position(&self) -> SpacePosition {
        self.start_position
    }

    #[inline]
    pub fn start_time(&self) -> TimePoint<T> {
        self.start_time
    }

    #[inline]
    pub fn into_owned(self) -> AnyAssignment<T, C> {
        let request = match self.request {
            AnyRequestRef::Movable(r) => AnyRequest::Movable(r.clone()),
            AnyRequestRef::Fixed(r) => AnyRequest::Fixed(r.clone()),
        };
        AnyAssignment {
            request,
            start_position: self.start_position,
            start_time: self.start_time,
        }
    }

    pub fn waiting_time(&self) -> TimeDelta<T> {
        (self.start_time() - self.request.arrival_time()).max(TimeDelta::zero())
    }

    pub fn waiting_cost(&self) -> Cost<C>
    where
        C: TryFrom<T>,
    {
        let waiting_time = self.waiting_time();
        let scalar: C = C::try_from(waiting_time.value())
            .ok()
            .expect("waiting time does not fit in C");
        self.request().cost_per_delay() * scalar
    }

    pub fn position_deviation(&self) -> SpaceLength {
        (self.start_position() - self.request.target_position()).abs()
    }

    pub fn position_deviation_cost(&self) -> Cost<C>
    where
        C: TryFrom<usize>,
    {
        let deviation = self.position_deviation();
        let scalar: C = C::try_from(deviation.value())
            .ok()
            .expect("deviation does not fit in C");
        self.request().cost_per_position_deviation() * scalar
    }

    pub fn cost(&self) -> Cost<C>
    where
        C: TryFrom<T> + TryFrom<usize>,
    {
        self.waiting_cost() + self.position_deviation_cost()
    }

    #[inline]
    pub fn to_owned(&self) -> AnyAssignment<T, C> {
        let request = match self.request {
            AnyRequestRef::Movable(r) => AnyRequest::Movable(r.clone()),
            AnyRequestRef::Fixed(r) => AnyRequest::Fixed(r.clone()),
        };
        AnyAssignment::new(request, self.start_position, self.start_time)
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<&'a Assignment<Movable, T, C>>
    for AnyAssignmentRef<'a, T, C>
{
    #[inline]
    fn from(a: &'a Assignment<Movable, T, C>) -> Self {
        AnyAssignmentRef::new(
            AnyRequestRef::Movable(a.request()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<&'a Assignment<Fixed, T, C>>
    for AnyAssignmentRef<'a, T, C>
{
    #[inline]
    fn from(a: &'a Assignment<Fixed, T, C>) -> Self {
        AnyAssignmentRef::new(
            AnyRequestRef::Fixed(a.request()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<T: SolverVariable, C: SolverVariable> From<&Assignment<Movable, T, C>>
    for AnyAssignment<T, C>
{
    #[inline]
    fn from(a: &Assignment<Movable, T, C>) -> Self {
        AnyAssignment::new(
            AnyRequest::Movable(a.request().clone()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<T: SolverVariable, C: SolverVariable> From<&Assignment<Fixed, T, C>> for AnyAssignment<T, C> {
    #[inline]
    fn from(a: &Assignment<Fixed, T, C>) -> Self {
        AnyAssignment::new(
            AnyRequest::Fixed(a.request().clone()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<T: SolverVariable, C: SolverVariable> From<Assignment<Movable, T, C>> for AnyAssignment<T, C> {
    fn from(a: Assignment<Movable, T, C>) -> Self {
        AnyAssignment::new(
            AnyRequest::Movable(a.request().clone()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<T: SolverVariable, C: SolverVariable> From<Assignment<Fixed, T, C>> for AnyAssignment<T, C> {
    fn from(a: Assignment<Fixed, T, C>) -> Self {
        AnyAssignment::new(
            AnyRequest::Fixed(a.request().clone()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<&'a AssignmentRef<'a, Movable, T, C>>
    for AnyAssignmentRef<'a, T, C>
{
    #[inline]
    fn from(a: &'a AssignmentRef<'a, Movable, T, C>) -> Self {
        AnyAssignmentRef::new(
            AnyRequestRef::Movable(a.request()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<&'a AssignmentRef<'a, Fixed, T, C>>
    for AnyAssignmentRef<'a, T, C>
{
    #[inline]
    fn from(a: &'a AssignmentRef<'a, Fixed, T, C>) -> Self {
        AnyAssignmentRef::new(
            AnyRequestRef::Fixed(a.request()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<&AssignmentRef<'a, Movable, T, C>>
    for AnyAssignment<T, C>
{
    #[inline]
    fn from(a: &AssignmentRef<'a, Movable, T, C>) -> Self {
        AnyAssignment::new(
            AnyRequest::Movable(a.request().clone()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<&AssignmentRef<'a, Fixed, T, C>>
    for AnyAssignment<T, C>
{
    #[inline]
    fn from(a: &AssignmentRef<'a, Fixed, T, C>) -> Self {
        AnyAssignment::new(
            AnyRequest::Fixed(a.request().clone()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<AssignmentRef<'a, Movable, T, C>>
    for AnyAssignment<T, C>
{
    fn from(a: AssignmentRef<'a, Movable, T, C>) -> Self {
        AnyAssignment::new(
            AnyRequest::Movable(a.request().clone()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<AssignmentRef<'a, Fixed, T, C>>
    for AnyAssignment<T, C>
{
    fn from(a: AssignmentRef<'a, Fixed, T, C>) -> Self {
        AnyAssignment::new(
            AnyRequest::Fixed(a.request().clone()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<AssignmentRef<'a, Movable, T, C>>
    for AnyAssignmentRef<'a, T, C>
{
    fn from(a: AssignmentRef<'a, Movable, T, C>) -> Self {
        AnyAssignmentRef::new(
            AnyRequestRef::Movable(a.request()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<AssignmentRef<'a, Fixed, T, C>>
    for AnyAssignmentRef<'a, T, C>
{
    fn from(a: AssignmentRef<'a, Fixed, T, C>) -> Self {
        AnyAssignmentRef::new(
            AnyRequestRef::Fixed(a.request()),
            a.start_position(),
            a.start_time(),
        )
    }
}

#[cfg(test)]
mod tests {
    use dock_alloc_core::space::SpaceInterval;

    use super::*;

    type Tm = i64;
    type Cm = i64;

    fn req_movable_ok(
        id: u64,
        len: usize,
        t0: i64,
        proc_t: i64,
        s0: usize,
        s1: usize,
    ) -> Request<Movable, Tm, Cm> {
        Request::<Movable, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimePoint::new(t0),
            TimeDelta::new(proc_t),
            SpacePosition::new(s0),
            Cost::new(1),
            Cost::new(1),
            SpaceInterval::new(SpacePosition::new(s0), SpacePosition::new(s1)),
        )
        .expect("valid movable request")
    }

    fn asg<K: Kind>(r: Request<K, Tm, Cm>, pos: usize, time: i64) -> Assignment<K, Tm, Cm> {
        Assignment::new(r, SpacePosition::new(pos), TimePoint::new(time))
    }

    #[test]
    fn assignment_into_erased_roundtrip() {
        let r = req_movable_ok(5, 4, 2, 3, 0, 10);
        let a = asg(r, 7, 1);
        let ae: AnyAssignmentRef<'_, Tm, Cm> = AnyAssignmentRef::from(&a);
        assert_eq!(ae.id(), a.id());
        assert_eq!(ae.start_time(), a.start_time());
        assert_eq!(ae.start_position(), a.start_position());

        // owned conversion
        let a2: AnyAssignment<Tm, Cm> = AnyAssignment::from(a.clone());
        assert_eq!(a2.id(), a.id());
    }
}
