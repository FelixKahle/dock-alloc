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

use crate::{
    err::SpaceWindowTooShortError,
    id::{FixedRequestId, MovableRequestId, RequestId},
};
use dock_alloc_core::{
    SolverVariable,
    cost::Cost,
    space::{SpaceInterval, SpaceLength, SpacePosition},
    time::{TimeDelta, TimePoint},
};
use std::{cmp::Ordering, fmt::Display, marker::PhantomData};

pub trait Kind: Clone {
    type Id: Copy
        + Eq
        + Ord
        + std::hash::Hash
        + Into<RequestId>
        + From<RequestId>
        + Display
        + std::fmt::Debug;
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Request<K: Kind, T = i64, C = i64>
where
    T: SolverVariable,
    C: SolverVariable,
{
    id: RequestId,
    length: SpaceLength,
    arrival_time: TimePoint<T>,
    processing_duration: TimeDelta<T>,
    target_position: SpacePosition,
    cost_per_delay: Cost<C>,
    cost_per_position_deviation: Cost<C>,
    feasible_space_windows: Vec<SpaceInterval>,
    _k: PhantomData<K>,
}

impl<K: Kind, T: SolverVariable, C: SolverVariable> Request<K, T, C> {
    fn merge_space_windows(mut windows: Vec<SpaceInterval>) -> Vec<SpaceInterval> {
        if windows.is_empty() {
            return windows;
        }
        windows.sort_by(|a, b| {
            let ord_start = a.start().cmp(&b.start());
            if ord_start == Ordering::Equal {
                a.end().cmp(&b.end())
            } else {
                ord_start
            }
        });

        let mut merged: Vec<SpaceInterval> = Vec::with_capacity(windows.len());

        for w in windows {
            if let Some(last) = merged.last_mut() {
                if let Some(u) = last.union(&w) {
                    *last = u;
                } else {
                    merged.push(w);
                }
            } else {
                merged.push(w);
            }
        }
        merged
    }

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
        feasible_space_windows: Vec<SpaceInterval>,
    ) -> Result<Self, SpaceWindowTooShortError> {
        let merged_windows = Self::merge_space_windows(feasible_space_windows);

        for space_window in merged_windows.iter().cloned() {
            if space_window.measure() < length {
                return Err(SpaceWindowTooShortError::new(id, length, space_window));
            }
        }

        Ok(Self {
            id,
            length,
            arrival_time,
            processing_duration,
            target_position,
            cost_per_delay,
            cost_per_position_deviation,
            feasible_space_windows: merged_windows,
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
    pub fn feasible_space_windows(&self) -> &[SpaceInterval] {
        &self.feasible_space_windows
    }
}

impl<K: Kind, T: SolverVariable, C: SolverVariable + TryFrom<T>> Request<K, T, C> {
    #[inline]
    pub fn waiting_cost(&self, waiting_time: TimeDelta<T>) -> Cost<C> {
        let scalar: C = C::try_from(waiting_time.value())
            .ok()
            .expect("waiting time does not fit in C");
        self.cost_per_delay * scalar
    }
}

impl<K: Kind, T: SolverVariable, C: SolverVariable + TryFrom<usize>> Request<K, T, C> {
    #[inline]
    pub fn target_position_deviation_cost(&self, deviation: SpaceLength) -> Cost<C> {
        let scalar: C = C::try_from(deviation.value())
            .ok()
            .expect("deviation does not fit in C");
        self.cost_per_position_deviation * scalar
    }
}

impl<K: Kind, T: SolverVariable + Display, C: SolverVariable + Display> Display
    for Request<K, T, C>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let windows = self
            .feasible_space_windows
            .iter()
            .map(|w| format!("{}", w))
            .collect::<Vec<_>>()
            .join(", ");

        write!(
            f,
            "{}Request(id: {}, length: {}, arrival_time: {}, processing_duration: {}, \
                target_position: {}, cost_per_delay: {}, cost_per_position_deviation: {}, \
                feasible_space_windows: [{}]",
            K::NAME,
            self.id,
            self.length,
            self.arrival_time,
            self.processing_duration,
            self.target_position,
            self.cost_per_delay,
            self.cost_per_position_deviation,
            windows
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AnyRequest<T = i64, C = i64>
where
    T: SolverVariable,
    C: SolverVariable,
{
    Movable(Request<Movable, T, C>),
    Fixed(Request<Fixed, T, C>),
}

impl<T: SolverVariable, C: SolverVariable> AnyRequest<T, C> {
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
    pub fn feasible_space_windows(&self) -> &[SpaceInterval] {
        match self {
            AnyRequest::Movable(r) => r.feasible_space_windows(),
            AnyRequest::Fixed(r) => r.feasible_space_windows(),
        }
    }

    #[inline]
    pub fn is_movable(&self) -> bool {
        matches!(self, AnyRequest::Movable(_))
    }

    #[inline]
    pub fn is_fixed(&self) -> bool {
        matches!(self, AnyRequest::Fixed(_))
    }
}

impl<T: SolverVariable, C: SolverVariable> From<Request<Movable, T, C>> for AnyRequest<T, C> {
    fn from(r: Request<Movable, T, C>) -> Self {
        AnyRequest::Movable(r)
    }
}

impl<T: SolverVariable, C: SolverVariable> From<Request<Fixed, T, C>> for AnyRequest<T, C> {
    fn from(r: Request<Fixed, T, C>) -> Self {
        AnyRequest::Fixed(r)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AnyRequestRef<'a, T = i64, C = i64>
where
    T: SolverVariable,
    C: SolverVariable,
{
    Movable(&'a Request<Movable, T, C>),
    Fixed(&'a Request<Fixed, T, C>),
}

impl<'a, T, C> AnyRequestRef<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
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
    pub fn feasible_space_windows(&self) -> &[SpaceInterval] {
        match self {
            AnyRequestRef::Movable(r) => r.feasible_space_windows(),
            AnyRequestRef::Fixed(r) => r.feasible_space_windows(),
        }
    }

    #[inline]
    pub fn is_movable(&self) -> bool {
        matches!(self, AnyRequestRef::Movable(_))
    }

    #[inline]
    pub fn is_fixed(&self) -> bool {
        matches!(self, AnyRequestRef::Fixed(_))
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<&'a Request<Movable, T, C>>
    for AnyRequestRef<'a, T, C>
{
    fn from(r: &'a Request<Movable, T, C>) -> Self {
        AnyRequestRef::Movable(r)
    }
}

impl<'a, T: SolverVariable, C: SolverVariable> From<&'a Request<Fixed, T, C>>
    for AnyRequestRef<'a, T, C>
{
    fn from(r: &'a Request<Fixed, T, C>) -> Self {
        AnyRequestRef::Fixed(r)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
            vec![SpaceInterval::new(
                SpacePosition::new(0),
                SpacePosition::new(5),
            )],
        );
        assert!(bad2.is_err());
    }

    #[test]
    fn request_new_accepts_multiple_windows_each_long_enough() {
        use dock_alloc_core::{
            cost::Cost,
            space::{SpaceInterval, SpaceLength, SpacePosition},
            time::{TimeDelta, TimePoint},
        };

        // len = 10; each window has measure >= 10
        let r = Request::<Movable, _, _>::new(
            RequestId::new(100),
            SpaceLength::new(10),
            TimePoint::new(0),
            TimeDelta::new(3),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            vec![
                SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10)), // measure 10
                SpaceInterval::new(SpacePosition::new(15), SpacePosition::new(30)), // measure 15
                SpaceInterval::new(SpacePosition::new(40), SpacePosition::new(50)), // measure 10
            ],
        );

        assert!(
            r.is_ok(),
            "constructor should accept multiple long-enough windows"
        );
    }

    #[test]
    fn request_new_rejects_when_any_window_is_too_short() {
        use dock_alloc_core::{
            cost::Cost,
            space::{SpaceInterval, SpaceLength, SpacePosition},
            time::{TimeDelta, TimePoint},
        };

        // len = 12; second window is only 8 long -> should error
        let r = Request::<Fixed, _, _>::new(
            RequestId::new(101),
            SpaceLength::new(12),
            TimePoint::new(0),
            TimeDelta::new(2),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            vec![
                SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(20)), // ok (20)
                SpaceInterval::new(SpacePosition::new(30), SpacePosition::new(38)), // too short (8)
                SpaceInterval::new(SpacePosition::new(50), SpacePosition::new(70)), // ok (20)
            ],
        );

        assert!(
            r.is_err(),
            "constructor must reject if any window is shorter than length"
        );
    }

    #[test]
    fn request_new_accepts_windows_equal_to_length() {
        use dock_alloc_core::{
            cost::Cost,
            space::{SpaceInterval, SpaceLength, SpacePosition},
            time::{TimeDelta, TimePoint},
        };

        // len = 15; windows equal to length are allowed
        let r = Request::<Movable, _, _>::new(
            RequestId::new(102),
            SpaceLength::new(15),
            TimePoint::new(0),
            TimeDelta::new(5),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            vec![
                SpaceInterval::new(SpacePosition::new(5), SpacePosition::new(20)), // measure 15
                SpaceInterval::new(SpacePosition::new(30), SpacePosition::new(45)), // measure 15
            ],
        );

        assert!(
            r.is_ok(),
            "windows with measure == length should be accepted"
        );
    }

    #[test]
    fn feasible_space_windows_returns_exact_input_order_and_bounds() {
        use dock_alloc_core::{
            cost::Cost,
            space::{SpaceInterval, SpaceLength, SpacePosition},
            time::{TimeDelta, TimePoint},
        };

        let windows = vec![
            SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(25)),
            SpaceInterval::new(SpacePosition::new(40), SpacePosition::new(60)),
            SpaceInterval::new(SpacePosition::new(70), SpacePosition::new(90)),
        ];

        let r = Request::<Fixed, _, _>::new(
            RequestId::new(103),
            SpaceLength::new(10),
            TimePoint::new(0),
            TimeDelta::new(1),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            windows.clone(),
        )
        .expect("should be valid");

        let got = r.feasible_space_windows();
        assert_eq!(got.len(), windows.len(), "windows length must match");
        for (i, (a, b)) in got.iter().zip(windows.iter()).enumerate() {
            assert_eq!(a.start(), b.start(), "window[{i}] start mismatch");
            assert_eq!(a.end(), b.end(), "window[{i}] end mismatch");
        }
    }

    #[test]
    fn request_new_merges_overlapping_and_adjacent_windows() {
        // Ship length 10
        // Windows:
        //   [0, 10)  and  [10, 20) -> adjacent -> should merge to [0, 20)
        //   [5, 15)        overlaps with [10, 30) -> should merge to [5, 30)
        // After a full pass, everything coalesces to [0, 30)
        let r = Request::<Movable, _, _>::new(
            RequestId::new(200),
            SpaceLength::new(10),
            TimePoint::new(0),
            TimeDelta::new(3),
            SpacePosition::new(0),
            Cost::new(1),
            Cost::new(1),
            vec![
                SpaceInterval::new(SpacePosition::new(0), SpacePosition::new(10)),
                SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(20)),
                SpaceInterval::new(SpacePosition::new(5), SpacePosition::new(15)),
                SpaceInterval::new(SpacePosition::new(10), SpacePosition::new(30)),
            ],
        )
        .expect("should be valid");

        let ws = r.feasible_space_windows();
        assert_eq!(
            ws.len(),
            1,
            "all overlapping/adjacent intervals should merge"
        );
        assert_eq!(ws[0].start().value(), 0);
        assert_eq!(ws[0].end().value(), 30);
        assert!(ws[0].measure() >= SpaceLength::new(10));
    }
}
