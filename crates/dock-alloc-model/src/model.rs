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

use dock_alloc_core::cost::Cost;
use dock_alloc_core::space::{SpaceInterval, SpaceLength, SpacePosition};
use dock_alloc_core::time::{TimeDelta, TimeInterval, TimePoint};
use num_traits::{PrimInt, Signed};
use std::fmt::{Debug, Display};
use std::marker::PhantomData;
use std::{collections::HashMap, hash::Hash};

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RequestId(u64);

impl RequestId {
    #[inline]
    pub const fn new(id: u64) -> Self {
        RequestId(id)
    }

    #[inline]
    pub const fn value(self) -> u64 {
        self.0
    }
}

impl Display for RequestId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RequestId({})", self.0)
    }
}

impl From<u64> for RequestId {
    fn from(value: u64) -> Self {
        RequestId(value)
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MovableRequestId(RequestId);

impl MovableRequestId {
    #[inline]
    pub fn new(id: RequestId) -> Self {
        Self(id)
    }

    #[inline]
    pub fn value(self) -> RequestId {
        self.0
    }
}
impl Display for MovableRequestId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Movable({})", self.0)
    }
}

impl From<RequestId> for MovableRequestId {
    fn from(value: RequestId) -> Self {
        MovableRequestId(value)
    }
}

impl From<MovableRequestId> for RequestId {
    fn from(value: MovableRequestId) -> Self {
        value.0
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FixedRequestId(RequestId);

impl FixedRequestId {
    #[inline]
    pub fn new(id: RequestId) -> Self {
        Self(id)
    }
    #[inline]
    pub fn value(self) -> RequestId {
        self.0
    }
}
impl Display for FixedRequestId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Fixed({})", self.0)
    }
}

impl From<RequestId> for FixedRequestId {
    fn from(value: RequestId) -> Self {
        FixedRequestId(value)
    }
}

impl From<FixedRequestId> for RequestId {
    fn from(value: FixedRequestId) -> Self {
        value.0
    }
}

pub trait Kind: Clone {
    type Id: Copy + Eq + Ord + Hash + Into<RequestId> + From<RequestId> + Display + Debug;
    const NAME: &'static str;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Movable;
impl Kind for Movable {
    type Id = MovableRequestId;
    const NAME: &'static str = "Movable";
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fixed;
impl Kind for Fixed {
    type Id = FixedRequestId;
    const NAME: &'static str = "Fixed";
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpaceWindowTooShortError {
    id: RequestId,
    length: SpaceLength,
    window: SpaceInterval,
}

impl SpaceWindowTooShortError {
    #[inline]
    pub fn new(id: RequestId, length: SpaceLength, window: SpaceInterval) -> Self {
        Self { id, length, window }
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.length
    }

    #[inline]
    pub fn space_window(&self) -> SpaceInterval {
        self.window
    }
}

impl Display for SpaceWindowTooShortError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Request {} has length {} not fitting space window {}",
            self.id, self.length, self.window
        )
    }
}

impl std::error::Error for SpaceWindowTooShortError {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Request<K: Kind, T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    id: RequestId,
    length: SpaceLength,
    arrival_time: TimePoint<T>,
    processing_duration: TimeDelta<T>,
    target_position: SpacePosition,
    cost_per_delay: Cost<C>,
    cost_per_position_deviation: Cost<C>,
    feasible_space_window: SpaceInterval,
    _k: PhantomData<K>,
}

impl<K: Kind, T: PrimInt + Signed, C: PrimInt + Signed> Request<K, T, C> {
    #[allow(clippy::too_many_arguments)]
    #[inline]
    pub fn new(
        id: RequestId,
        length: SpaceLength,
        arrival_time: TimePoint<T>,
        processing_duration: TimeDelta<T>,
        target_position: SpacePosition,
        cost_per_delay: Cost<C>,
        cost_per_position_deviation: Cost<C>,
        feasible_space_window: SpaceInterval,
    ) -> Result<Self, SpaceWindowTooShortError> {
        // Check if the space window is large enough to fit the request
        if feasible_space_window.measure() < length {
            return Err(SpaceWindowTooShortError::new(
                id,
                length,
                feasible_space_window,
            ));
        }

        Ok(Self {
            id,
            length,
            arrival_time,
            processing_duration,
            target_position,
            cost_per_delay,
            cost_per_position_deviation,
            feasible_space_window,
            _k: PhantomData,
        })
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn typed_id(&self) -> K::Id {
        self.id.into()
    }

    #[inline]
    pub fn length(&self) -> SpaceLength {
        self.length
    }

    #[inline]
    pub fn arrival_time(&self) -> TimePoint<T> {
        self.arrival_time
    }

    #[inline]
    pub fn processing_duration(&self) -> TimeDelta<T> {
        self.processing_duration
    }

    #[inline]
    pub fn target_position(&self) -> SpacePosition {
        self.target_position
    }

    #[inline]
    pub fn cost_per_delay(&self) -> Cost<C> {
        self.cost_per_delay
    }

    #[inline]
    pub fn cost_per_position_deviation(&self) -> Cost<C> {
        self.cost_per_position_deviation
    }

    #[inline]
    pub fn feasible_space_window(&self) -> SpaceInterval {
        self.feasible_space_window
    }
}

impl<K: Kind, T: PrimInt + Signed, C: PrimInt + Signed + TryFrom<T>> Request<K, T, C> {
    #[inline]
    pub fn waiting_cost(&self, waiting_time: TimeDelta<T>) -> Cost<C> {
        let scalar: C = C::try_from(waiting_time.value())
            .ok()
            .expect("waiting time does not fit in C");
        self.cost_per_delay * scalar
    }
}

impl<K: Kind, T: PrimInt + Signed, C: PrimInt + Signed + TryFrom<usize>> Request<K, T, C> {
    #[inline]
    pub fn target_position_deviation_cost(&self, deviation: SpaceLength) -> Cost<C> {
        let scalar: C = C::try_from(deviation.value())
            .ok()
            .expect("deviation does not fit in C");
        self.cost_per_position_deviation * scalar
    }
}

impl<K: Kind, T: PrimInt + Signed + Display, C: PrimInt + Signed + Display> Display
    for Request<K, T, C>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}Request(id: {}, length: {}, arrival_time: {}, processing_duration: {}, \
            target_position: {}, cost_per_delay: {}, cost_per_position_deviation: {}, \
             feasible_space_window: {})",
            K::NAME,
            self.id,
            self.length,
            self.arrival_time,
            self.processing_duration,
            self.target_position,
            self.cost_per_delay,
            self.cost_per_position_deviation,
            self.feasible_space_window
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assignment<K: Kind, T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    request: Request<K, T, C>,
    start_position: SpacePosition,
    start_time: TimePoint<T>,
}

impl<K: Kind, T: PrimInt + Signed, C: PrimInt + Signed> Assignment<K, T, C> {
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

impl<K: Kind, T: PrimInt + Signed + Display, C: PrimInt + Signed + Display> Display
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
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    request: &'a Request<K, T, C>,
    start_position: SpacePosition,
    start_time: TimePoint<T>,
}

impl<'a, K: Kind, T: PrimInt + Signed, C: PrimInt + Signed> AssignmentRef<'a, K, T, C> {
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

impl<'a, K: Kind, T: PrimInt + Signed + Display, C: PrimInt + Signed + Display> Display
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
pub enum AnyRequest<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    Movable(Request<Movable, T, C>),
    Fixed(Request<Fixed, T, C>),
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> AnyRequest<T, C> {
    pub fn id(&self) -> RequestId {
        match self {
            AnyRequest::Movable(r) => r.id(),
            AnyRequest::Fixed(r) => r.id(),
        }
    }

    #[inline]
    pub fn length(&self) -> SpaceLength {
        match self {
            AnyRequest::Movable(r) => r.length(),
            AnyRequest::Fixed(r) => r.length(),
        }
    }

    #[inline]
    pub fn arrival_time(&self) -> TimePoint<T> {
        match self {
            AnyRequest::Movable(r) => r.arrival_time(),
            AnyRequest::Fixed(r) => r.arrival_time(),
        }
    }

    #[inline]
    pub fn processing_duration(&self) -> TimeDelta<T> {
        match self {
            AnyRequest::Movable(r) => r.processing_duration(),
            AnyRequest::Fixed(r) => r.processing_duration(),
        }
    }

    #[inline]
    pub fn target_position(&self) -> SpacePosition {
        match self {
            AnyRequest::Movable(r) => r.target_position(),
            AnyRequest::Fixed(r) => r.target_position(),
        }
    }

    #[inline]
    pub fn cost_per_delay(&self) -> Cost<C> {
        match self {
            AnyRequest::Movable(r) => r.cost_per_delay(),
            AnyRequest::Fixed(r) => r.cost_per_delay(),
        }
    }

    #[inline]
    pub fn cost_per_position_deviation(&self) -> Cost<C> {
        match self {
            AnyRequest::Movable(r) => r.cost_per_position_deviation(),
            AnyRequest::Fixed(r) => r.cost_per_position_deviation(),
        }
    }

    #[inline]
    pub fn feasible_space_window(&self) -> SpaceInterval {
        match self {
            AnyRequest::Movable(r) => r.feasible_space_window(),
            AnyRequest::Fixed(r) => r.feasible_space_window(),
        }
    }

    pub fn is_movable(&self) -> bool {
        matches!(self, AnyRequest::Movable(_))
    }

    pub fn is_fixed(&self) -> bool {
        matches!(self, AnyRequest::Fixed(_))
    }
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> From<Request<Movable, T, C>> for AnyRequest<T, C> {
    fn from(r: Request<Movable, T, C>) -> Self {
        AnyRequest::Movable(r)
    }
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> From<Request<Fixed, T, C>> for AnyRequest<T, C> {
    fn from(r: Request<Fixed, T, C>) -> Self {
        AnyRequest::Fixed(r)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AnyRequestRef<'a, T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    Movable(&'a Request<Movable, T, C>),
    Fixed(&'a Request<Fixed, T, C>),
}

impl<'a, T, C> AnyRequestRef<'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    pub fn id(&self) -> RequestId {
        match self {
            AnyRequestRef::Movable(r) => r.id(),
            AnyRequestRef::Fixed(r) => r.id(),
        }
    }

    #[inline]
    pub fn length(&self) -> SpaceLength {
        match self {
            AnyRequestRef::Movable(r) => r.length(),
            AnyRequestRef::Fixed(r) => r.length(),
        }
    }

    #[inline]
    pub fn arrival_time(&self) -> TimePoint<T> {
        match self {
            AnyRequestRef::Movable(r) => r.arrival_time(),
            AnyRequestRef::Fixed(r) => r.arrival_time(),
        }
    }

    #[inline]
    pub fn processing_duration(&self) -> TimeDelta<T> {
        match self {
            AnyRequestRef::Movable(r) => r.processing_duration(),
            AnyRequestRef::Fixed(r) => r.processing_duration(),
        }
    }

    #[inline]
    pub fn target_position(&self) -> SpacePosition {
        match self {
            AnyRequestRef::Movable(r) => r.target_position(),
            AnyRequestRef::Fixed(r) => r.target_position(),
        }
    }

    #[inline]
    pub fn cost_per_delay(&self) -> Cost<C> {
        match self {
            AnyRequestRef::Movable(r) => r.cost_per_delay(),
            AnyRequestRef::Fixed(r) => r.cost_per_delay(),
        }
    }

    #[inline]
    pub fn cost_per_position_deviation(&self) -> Cost<C> {
        match self {
            AnyRequestRef::Movable(r) => r.cost_per_position_deviation(),
            AnyRequestRef::Fixed(r) => r.cost_per_position_deviation(),
        }
    }

    #[inline]
    pub fn feasible_space_window(&self) -> SpaceInterval {
        match self {
            AnyRequestRef::Movable(r) => r.feasible_space_window(),
            AnyRequestRef::Fixed(r) => r.feasible_space_window(),
        }
    }

    pub fn is_movable(&self) -> bool {
        matches!(self, AnyRequestRef::Movable(_))
    }

    pub fn is_fixed(&self) -> bool {
        matches!(self, AnyRequestRef::Fixed(_))
    }
}

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<&'a Request<Movable, T, C>>
    for AnyRequestRef<'a, T, C>
{
    fn from(r: &'a Request<Movable, T, C>) -> Self {
        AnyRequestRef::Movable(r)
    }
}

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<&'a Request<Fixed, T, C>>
    for AnyRequestRef<'a, T, C>
{
    fn from(r: &'a Request<Fixed, T, C>) -> Self {
        AnyRequestRef::Fixed(r)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AnyAssignment<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    request: AnyRequest<T, C>,
    start_position: SpacePosition,
    start_time: TimePoint<T>,
}

impl<T, C> AnyAssignment<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
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
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    request: AnyRequestRef<'a, T, C>,
    start_position: SpacePosition,
    start_time: TimePoint<T>,
}

impl<'a, T, C> AnyAssignmentRef<'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
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

    #[inline]
    pub fn to_owned(&self) -> AnyAssignment<T, C> {
        let request = match self.request {
            AnyRequestRef::Movable(r) => AnyRequest::Movable(r.clone()),
            AnyRequestRef::Fixed(r) => AnyRequest::Fixed(r.clone()),
        };
        AnyAssignment::new(request, self.start_position, self.start_time)
    }
}

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<&'a Assignment<Movable, T, C>>
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

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<&'a Assignment<Fixed, T, C>>
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

impl<T: PrimInt + Signed, C: PrimInt + Signed> From<&Assignment<Movable, T, C>>
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

impl<T: PrimInt + Signed, C: PrimInt + Signed> From<&Assignment<Fixed, T, C>>
    for AnyAssignment<T, C>
{
    #[inline]
    fn from(a: &Assignment<Fixed, T, C>) -> Self {
        AnyAssignment::new(
            AnyRequest::Fixed(a.request().clone()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> From<Assignment<Movable, T, C>>
    for AnyAssignment<T, C>
{
    fn from(a: Assignment<Movable, T, C>) -> Self {
        AnyAssignment::new(
            AnyRequest::Movable(a.request().clone()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> From<Assignment<Fixed, T, C>>
    for AnyAssignment<T, C>
{
    fn from(a: Assignment<Fixed, T, C>) -> Self {
        AnyAssignment::new(
            AnyRequest::Fixed(a.request().clone()),
            a.start_position(),
            a.start_time(),
        )
    }
}

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<&'a AssignmentRef<'a, Movable, T, C>>
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

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<&'a AssignmentRef<'a, Fixed, T, C>>
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

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<&AssignmentRef<'a, Movable, T, C>>
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

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<&AssignmentRef<'a, Fixed, T, C>>
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

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<AssignmentRef<'a, Movable, T, C>>
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

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<AssignmentRef<'a, Fixed, T, C>>
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

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<AssignmentRef<'a, Movable, T, C>>
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

impl<'a, T: PrimInt + Signed, C: PrimInt + Signed> From<AssignmentRef<'a, Fixed, T, C>>
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentBeforeArrivalTimeError<T: PrimInt + Signed> {
    id: RequestId,
    arrival_time: TimePoint<T>,
    assigned_start_time: TimePoint<T>,
}

impl<T: PrimInt + Signed> AssignmentBeforeArrivalTimeError<T> {
    #[inline]
    pub fn new(
        id: RequestId,
        arrival_time: TimePoint<T>,
        assigned_start_time: TimePoint<T>,
    ) -> Self {
        Self {
            id,
            arrival_time,
            assigned_start_time,
        }
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn arrival_time(&self) -> TimePoint<T> {
        self.arrival_time
    }

    #[inline]
    pub fn assigned_start_time(&self) -> TimePoint<T> {
        self.assigned_start_time
    }
}

impl<T: PrimInt + Signed + Display> std::fmt::Display for AssignmentBeforeArrivalTimeError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment for request {} starts before its arrival time: {} < {}",
            self.id, self.assigned_start_time, self.arrival_time
        )
    }
}

impl<T: PrimInt + Signed + Debug + Display> std::error::Error
    for AssignmentBeforeArrivalTimeError<T>
{
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentOutsideSpaceWindowError {
    id: RequestId,
    space_window: SpaceInterval,
    assigned_interval: SpaceInterval,
}

impl AssignmentOutsideSpaceWindowError {
    #[inline]
    pub fn new(
        id: RequestId,
        space_window: SpaceInterval,
        assigned_interval: SpaceInterval,
    ) -> Self {
        Self {
            id,
            space_window,
            assigned_interval,
        }
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn space_window(&self) -> SpaceInterval {
        self.space_window
    }

    #[inline]
    pub fn assigned_interval(&self) -> SpaceInterval {
        self.assigned_interval
    }
}
impl Display for AssignmentOutsideSpaceWindowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment for request {} is outside its space window: {} not in {}",
            self.id, self.assigned_interval, self.space_window
        )
    }
}

impl std::error::Error for AssignmentOutsideSpaceWindowError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentExceedsQuayError {
    id: RequestId,
    quay_length: SpaceLength,
    assigned_interval: SpaceInterval,
}

impl AssignmentExceedsQuayError {
    #[inline]
    pub fn new(id: RequestId, quay_length: SpaceLength, assigned_interval: SpaceInterval) -> Self {
        Self {
            id,
            quay_length,
            assigned_interval,
        }
    }

    #[inline]
    pub fn id(&self) -> RequestId {
        self.id
    }

    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    #[inline]
    pub fn assigned_interval(&self) -> SpaceInterval {
        self.assigned_interval
    }
}

impl Display for AssignmentExceedsQuayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Assignment for request {} exceeds quay length {}: {}",
            self.id, self.quay_length, self.assigned_interval
        )
    }
}

impl std::error::Error for AssignmentExceedsQuayError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PreassignedOverlapError {
    a: FixedRequestId,
    b: FixedRequestId,
}

impl PreassignedOverlapError {
    #[inline]
    pub fn new(a: FixedRequestId, b: FixedRequestId) -> Self {
        Self { a, b }
    }

    #[inline]
    pub fn request_a(&self) -> FixedRequestId {
        self.a
    }

    #[inline]
    pub fn request_b(&self) -> FixedRequestId {
        self.b
    }
}

impl Display for PreassignedOverlapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Preassigned assignments for requests {} and {} overlap",
            self.a, self.b
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProblemBuildError<T: PrimInt + Signed> {
    DuplicateRequestId(RequestId),
    AssignmentBeforeArrivalTime(AssignmentBeforeArrivalTimeError<T>),
    AssignmentOutsideSpaceWindow(AssignmentOutsideSpaceWindowError),
    AssignmentExceedsQuay(AssignmentExceedsQuayError),
    PreassignedOverlap(PreassignedOverlapError),
}

impl<T: PrimInt + Signed + Display> Display for ProblemBuildError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProblemBuildError::DuplicateRequestId(id) => write!(f, "Duplicate request ID: {}", id),
            ProblemBuildError::AssignmentBeforeArrivalTime(e) => write!(f, "{e}"),
            ProblemBuildError::AssignmentOutsideSpaceWindow(e) => write!(f, "{e}"),
            ProblemBuildError::AssignmentExceedsQuay(e) => write!(f, "{e}"),
            ProblemBuildError::PreassignedOverlap(e) => write!(f, "{e}"),
        }
    }
}

impl<T: PrimInt + Signed + Debug + Display> std::error::Error for ProblemBuildError<T> {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Problem<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    movables: Vec<Request<Movable, T, C>>,
    movable_index: HashMap<MovableRequestId, usize>,

    preassigned: Vec<Assignment<Fixed, T, C>>,
    preassigned_index: HashMap<FixedRequestId, usize>,

    quay_length: SpaceLength,
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> Problem<T, C> {
    #[inline]
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }

    #[inline]
    pub fn total_requests(&self) -> usize {
        self.movables.len() + self.preassigned.len()
    }

    #[inline]
    pub fn movables(&self) -> &[Request<Movable, T, C>] {
        &self.movables
    }

    #[inline]
    pub fn preassigned(&self) -> &[Assignment<Fixed, T, C>] {
        &self.preassigned
    }

    #[inline]
    pub fn get_movable(&self, id: MovableRequestId) -> Option<&Request<Movable, T, C>> {
        let idx = self.movable_index.get(&id)?;
        self.movables.get(*idx)
    }

    #[inline]
    pub fn get_preassigned(&self, id: FixedRequestId) -> Option<&Assignment<Fixed, T, C>> {
        let idx = self.preassigned_index.get(&id)?;
        self.preassigned.get(*idx)
    }

    #[inline]
    pub fn iter_movable_requests(&self) -> impl Iterator<Item = &Request<Movable, T, C>> {
        self.movables.iter()
    }

    #[inline]
    pub fn iter_fixed_requests(&self) -> impl Iterator<Item = &Request<Fixed, T, C>> {
        self.preassigned.iter().map(|a| a.request())
    }

    #[inline]
    pub fn iter_any_requests(&self) -> impl Iterator<Item = AnyRequestRef<'_, T, C>> + '_ {
        self.iter_movable_requests()
            .map(AnyRequestRef::from)
            .chain(self.iter_fixed_requests().map(AnyRequestRef::from))
    }

    #[inline]
    pub fn iter_fixed_assignments(&self) -> impl Iterator<Item = &Assignment<Fixed, T, C>> {
        self.preassigned.iter()
    }
}

pub struct ProblemBuilder<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    movables: HashMap<MovableRequestId, Request<Movable, T, C>>,
    preassigned: HashMap<FixedRequestId, Assignment<Fixed, T, C>>,
    quay_length: SpaceLength,
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> ProblemBuilder<T, C> {
    #[inline]
    pub fn new(quay_length: SpaceLength) -> Self {
        Self {
            movables: HashMap::new(),
            preassigned: HashMap::new(),
            quay_length,
        }
    }

    #[inline]
    pub fn quay_length(&mut self, length: SpaceLength) -> &mut Self {
        self.quay_length = length;
        self
    }

    #[inline]
    pub fn add_movable_request(
        &mut self,
        request: Request<Movable, T, C>,
    ) -> Result<&mut Self, ProblemBuildError<T>> {
        let id = request.id();
        if self.movables.contains_key(&id.into()) || self.preassigned.contains_key(&id.into()) {
            return Err(ProblemBuildError::DuplicateRequestId(id));
        }
        self.movables.insert(id.into(), request);
        Ok(self)
    }

    #[inline]
    fn assignment_spans<K: Kind>(a: &Assignment<K, T, C>) -> (TimeInterval<T>, SpaceInterval) {
        let t0 = a.start_time();
        let t1 = t0 + a.request().processing_duration();
        let s0 = a.start_position();
        let s1 = SpacePosition::new(s0.value() + a.request().length().value());
        (TimeInterval::new(t0, t1), SpaceInterval::new(s0, s1))
    }

    pub fn add_preassigned(
        &mut self,
        fixed: Assignment<Fixed, T, C>,
    ) -> Result<&mut Self, ProblemBuildError<T>> {
        let a = &fixed;
        let r = a.request();
        let id = r.id();

        if self.movables.contains_key(&id.into()) || self.preassigned.contains_key(&id.into()) {
            return Err(ProblemBuildError::DuplicateRequestId(id));
        }

        if a.start_time() < r.arrival_time() {
            return Err(ProblemBuildError::AssignmentBeforeArrivalTime(
                AssignmentBeforeArrivalTimeError::new(id, r.arrival_time(), a.start_time()),
            ));
        }

        let (tspan, sspan) = Self::assignment_spans(a);

        let sw = r.feasible_space_window();
        if !sw.contains_interval(&sspan) {
            return Err(ProblemBuildError::AssignmentOutsideSpaceWindow(
                AssignmentOutsideSpaceWindowError::new(id, sw, sspan),
            ));
        }

        if sspan.end().value() > self.quay_length.value() {
            return Err(ProblemBuildError::AssignmentExceedsQuay(
                AssignmentExceedsQuayError::new(id, self.quay_length, sspan),
            ));
        }

        // Non-overlap among fixed assignments (space & time)
        for (&other_id, other_fixed) in &self.preassigned {
            let (ot, os) = Self::assignment_spans(other_fixed);
            if tspan.intersects(&ot) && sspan.intersects(&os) {
                return Err(ProblemBuildError::PreassignedOverlap(
                    PreassignedOverlapError::new(id.into(), other_id),
                ));
            }
        }

        self.preassigned.insert(id.into(), fixed);
        Ok(self)
    }

    #[inline]
    pub fn build(&self) -> Problem<T, C> {
        let mut movable_pairs: Vec<(MovableRequestId, Request<Movable, T, C>)> =
            self.movables.iter().map(|(k, v)| (*k, v.clone())).collect();
        movable_pairs.sort_by_key(|(id, _)| id.value());

        let mut movables = Vec::with_capacity(movable_pairs.len());
        let mut movable_index = HashMap::with_capacity(movable_pairs.len());
        for (i, (mid, req)) in movable_pairs.into_iter().enumerate() {
            movable_index.insert(mid, i);
            movables.push(req);
        }

        let mut fixed_pairs: Vec<(FixedRequestId, Assignment<Fixed, T, C>)> = self
            .preassigned
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        fixed_pairs.sort_by_key(|(id, _)| id.value());

        let mut preassigned = Vec::with_capacity(fixed_pairs.len());
        let mut preassigned_index = HashMap::with_capacity(fixed_pairs.len());
        for (i, (fid, asg)) in fixed_pairs.into_iter().enumerate() {
            preassigned_index.insert(fid, i);
            preassigned.push(asg);
        }

        Problem {
            movables,
            movable_index,
            preassigned,
            preassigned_index,
            quay_length: self.quay_length,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SolutionStats<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    total_cost: Cost<C>,
    total_waiting_time: TimeDelta<T>,
    total_target_position_deviation: SpaceLength,
}

impl<T: PrimInt + Signed, C: PrimInt + Signed> SolutionStats<T, C> {
    #[inline]
    fn new(
        total_cost: Cost<C>,
        total_waiting_time: TimeDelta<T>,
        total_target_position_deviation: SpaceLength,
    ) -> Self {
        Self {
            total_cost,
            total_waiting_time,
            total_target_position_deviation,
        }
    }
    #[inline]
    pub fn total_cost(&self) -> Cost<C> {
        self.total_cost
    }

    #[inline]
    pub fn total_waiting_time(&self) -> TimeDelta<T> {
        self.total_waiting_time
    }

    #[inline]
    pub fn total_target_position_deviation(&self) -> SpaceLength {
        self.total_target_position_deviation
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedSolution<T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    decisions: HashMap<RequestId, AnyAssignment<T, C>>,
    stats: SolutionStats<T, C>,
}

impl<T, C> OwnedSolution<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn new(decisions: HashMap<RequestId, AnyAssignment<T, C>>, stats: SolutionStats<T, C>) -> Self {
        Self { decisions, stats }
    }

    #[inline]
    pub fn stats(&self) -> &SolutionStats<T, C> {
        &self.stats
    }

    #[inline]
    pub fn decisions(&self) -> &HashMap<RequestId, AnyAssignment<T, C>> {
        &self.decisions
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolutionRef<'a, T = i64, C = i64>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    decisions: HashMap<RequestId, AnyAssignmentRef<'a, T, C>>,
    stats: SolutionStats<T, C>,
}

impl<'a, T, C> SolutionRef<'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed + TryFrom<T> + TryFrom<usize>,
{
    #[inline]
    pub fn new(
        assignments: HashMap<RequestId, AnyAssignmentRef<'a, T, C>>,
        stats: SolutionStats<T, C>,
    ) -> Self {
        Self {
            decisions: assignments,
            stats,
        }
    }

    #[inline]
    pub fn from_assignments(assignments: HashMap<RequestId, AnyAssignmentRef<'a, T, C>>) -> Self {
        let mut total_wait = TimeDelta::<T>::new(T::zero());
        let mut total_dev = SpaceLength::new(0);
        let mut total_cost = Cost::<C>::new(C::zero());

        for a in assignments.values() {
            let r = a.request();

            let wait = (a.start_time() - r.arrival_time())
                .clamp(TimeDelta::zero(), TimeDelta::new(T::max_value()));
            total_wait += wait;

            let dev = a.start_position() - r.target_position();
            total_dev += dev;

            let wait_cost = {
                let scalar: C = C::try_from(wait.value())
                    .ok()
                    .expect("wait does not fit in C");
                r.cost_per_delay() * scalar
            };
            let dev_cost = {
                let scalar: C = C::try_from(dev.value())
                    .ok()
                    .expect("dev does not fit in C");
                r.cost_per_position_deviation() * scalar
            };

            total_cost = total_cost + wait_cost + dev_cost;
        }

        Self::new(
            assignments,
            SolutionStats::new(total_cost, total_wait, total_dev),
        )
    }

    #[inline]
    pub fn stats(&self) -> &SolutionStats<T, C> {
        &self.stats
    }

    #[inline]
    pub fn decisions(&self) -> &HashMap<RequestId, AnyAssignmentRef<'_, T, C>> {
        &self.decisions
    }
}

impl<'a, T, C> SolutionRef<'a, T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    pub fn to_owned(&self) -> OwnedSolution<T, C> {
        let owned_decisions = self
            .decisions
            .iter()
            .map(|(&id, a)| (id, a.to_owned()))
            .collect();

        OwnedSolution::new(owned_decisions, self.stats)
    }

    #[inline]
    pub fn into_owned(self) -> OwnedSolution<T, C> {
        let owned_decisions = self
            .decisions
            .into_iter()
            .map(|(id, a)| (id, a.into_owned()))
            .collect();

        OwnedSolution::new(owned_decisions, self.stats)
    }
}

impl<'a, T, C> From<&SolutionRef<'a, T, C>> for OwnedSolution<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    #[inline]
    fn from(s: &SolutionRef<'a, T, C>) -> Self {
        s.to_owned()
    }
}

#[cfg(test)]
mod tests {
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

    fn req_fixed_ok(
        id: u64,
        len: usize,
        t0: i64,
        proc_t: i64,
        s0: usize,
        s1: usize,
    ) -> Request<Fixed, Tm, Cm> {
        Request::<Fixed, _, _>::new(
            RequestId::new(id),
            SpaceLength::new(len),
            TimePoint::new(t0),
            TimeDelta::new(proc_t),
            SpacePosition::new(s0),
            Cost::new(1),
            Cost::new(1),
            SpaceInterval::new(SpacePosition::new(s0), SpacePosition::new(s1)),
        )
        .expect("valid fixed request")
    }

    fn asg<K: Kind>(r: Request<K, Tm, Cm>, pos: usize, time: i64) -> Assignment<K, Tm, Cm> {
        Assignment::new(r, SpacePosition::new(pos), TimePoint::new(time))
    }

    fn ids_sorted(mut v: Vec<RequestId>) -> Vec<RequestId> {
        v.sort_by_key(|id| id.value());
        v
    }

    #[test]
    fn request_new_rejects_bad_windows() {
        // too short space window
        let bad2 = Request::<Fixed, _, _>::new(
            RequestId::new(2),
            SpaceLength::new(10),
            TimePoint::new(0),
            TimeDelta::new(2),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(5)), // measure 5 < 10
        );
        assert!(bad2.is_err());
    }

    #[test]
    fn builder_duplicate_ids_rejected() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(20));
        let r1 = req_movable_ok(1, 4, 0, 3, 0, 10);
        let r2 = req_movable_ok(1, 5, 0, 3, 0, 10); // same id
        b.add_movable_request(r1).unwrap();
        assert!(matches!(
            b.add_movable_request(r2),
            Err(ProblemBuildError::DuplicateRequestId(_))
        ));
    }

    #[test]
    fn builder_preassigned_window_violations_rejected() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(20));
        let rf2 = req_fixed_ok(2, 6, 0, 2, 0, 10); // arrival = 0 (so time is fine)
        let a2 = Assignment::new(rf2, SpacePosition::new(7), TimePoint::new(1)); // [7,13) leaks past 10
        assert!(matches!(
            b.add_preassigned(a2),
            Err(ProblemBuildError::AssignmentOutsideSpaceWindow(_))
        ));
    }

    #[test]
    fn builder_preassigned_exceeds_quay_rejected() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(10));
        let rf = req_fixed_ok(1, 6, 0, 2, 0, 20); // window wide enough to include [6,12)
        let a = Assignment::new(rf, SpacePosition::new(6), TimePoint::new(1)); // [6,12) > quay 10
        assert!(matches!(
            b.add_preassigned(a),
            Err(ProblemBuildError::AssignmentExceedsQuay(_))
        ));
    }

    #[test]
    fn builder_preassigned_overlap_rejected() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(20));
        let r1 = req_fixed_ok(1, 4, 0, 5, 0, 20);
        let r2 = req_fixed_ok(2, 4, 0, 5, 0, 20);

        b.add_preassigned(Assignment::new(
            r1,
            SpacePosition::new(5),
            TimePoint::new(2),
        ))
        .unwrap(); // t[2,7), s[5,9)
        let a2 = Assignment::new(r2, SpacePosition::new(7), TimePoint::new(4)); // t[4,9), s[7,11) -> overlaps
        assert!(matches!(
            b.add_preassigned(a2),
            Err(ProblemBuildError::PreassignedOverlap(_))
        ));
    }

    #[test]
    fn builder_build_ok_when_valid() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(20));
        let r_m = req_movable_ok(1, 4, 0, 3, 0, 10);
        let r_f = req_fixed_ok(2, 4, 10, 3, 0, 10); // arrival = 10
        b.add_movable_request(r_m).unwrap();
        b.add_preassigned(Assignment::new(
            r_f,
            SpacePosition::new(6),
            TimePoint::new(10), // start at/after arrival
        ))
        .unwrap();
        let p = b.build();
        assert_eq!(p.total_requests(), 2);
        assert_eq!(p.movables().len(), 1);
        assert_eq!(p.preassigned().len(), 1);
    }

    #[test]
    fn problem_iters_and_solution_aggregation() {
        let mut b = ProblemBuilder::<Tm, Cm>::new(SpaceLength::new(100));
        let r1 = req_movable_ok(1, 10, 0, 5, 0, 100);
        let r2 = req_movable_ok(2, 10, 0, 5, 0, 100);
        let r_fixed = req_fixed_ok(10, 10, 60, 5, 60, 100);

        b.add_movable_request(r1.clone()).unwrap();
        b.add_movable_request(r2.clone()).unwrap();
        b.add_preassigned(Assignment::new(
            r_fixed,
            SpacePosition::new(60),
            TimePoint::new(60), // start at arrival
        ))
        .unwrap();

        let p = b.build();

        // movable typed ids -> RequestId
        let mids: Vec<_> = p.iter_movable_requests().map(|r| r.id()).collect();
        assert_eq!(ids_sorted(mids), vec![RequestId::new(1), RequestId::new(2)]);

        // fixed assignments exist
        assert_eq!(p.iter_fixed_assignments().count(), 1);

        // place r1 at (0,0)
        let a_r1 = Assignment::new(
            p.get_movable(MovableRequestId::from(RequestId::new(1)))
                .unwrap()
                .clone(),
            SpacePosition::new(0),
            TimePoint::new(0),
        );

        let a_fixed_ref: AnyAssignmentRef<'_, Tm, Cm> =
            AnyAssignmentRef::from(p.preassigned().iter().next().unwrap());
        let a_r1_ref: AnyAssignmentRef<'_, Tm, Cm> = AnyAssignmentRef::from(&a_r1);

        let mut map: HashMap<RequestId, AnyAssignmentRef<'_, Tm, Cm>> = HashMap::new();
        map.insert(a_fixed_ref.id(), a_fixed_ref);
        map.insert(a_r1_ref.id(), a_r1_ref);

        let sol = SolutionRef::from_assignments(map);
        assert_eq!(sol.stats().total_waiting_time(), TimeDelta::new(0));
        assert_eq!(
            sol.stats().total_target_position_deviation(),
            SpaceLength::new(0)
        );
        assert_eq!(sol.stats().total_cost(), Cost::new(0));
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

    #[test]
    fn cost_helpers_behave_like_solution_path() {
        // Set cost-per-delay=2, cost-per-dev=3 to see accumulation
        let r = Request::<Movable, Tm, Cm>::new(
            RequestId::new(7),
            SpaceLength::new(4),
            TimePoint::new(5),
            TimeDelta::new(3),
            SpacePosition::new(10),
            Cost::new(2), // per time unit
            Cost::new(3), // per space unit
            SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(100)),
        )
        .unwrap();

        // start at t=9 (wait=4), position=13 (dev=3)
        let a = Assignment::new(r, SpacePosition::new(13), TimePoint::new(9));
        let ae: AnyAssignmentRef<'_, Tm, Cm> = AnyAssignmentRef::from(&a);

        // replicate Solution math
        let wait = (ae.start_time() - ae.request().arrival_time())
            .clamp(TimeDelta::zero(), TimeDelta::new(Tm::max_value()));
        let dev = ae.start_position() - ae.request().target_position();

        assert_eq!(wait, TimeDelta::new(4));
        assert_eq!(dev, SpaceLength::new(3));

        let mut map = HashMap::new();
        map.insert(ae.id(), ae.clone());
        let sol = SolutionRef::from_assignments(map);

        // expected: cost = 2*4 + 3*3 = 8 + 9 = 17
        assert_eq!(sol.stats().total_cost(), Cost::new(17));
    }

    #[test]
    fn builder_preassigned_start_before_arrival_rejected() {
        let mut b = ProblemBuilder::<i64, i64>::new(SpaceLength::new(100));
        let r = req_fixed_ok(42, 10, 50, 5, 0, 100); // arrival_time = 50
        let a = Assignment::new(r, SpacePosition::new(0), TimePoint::new(49)); // starts before arrival
        assert!(matches!(
            b.add_preassigned(a),
            Err(ProblemBuildError::AssignmentBeforeArrivalTime(_))
        ));
    }
}
