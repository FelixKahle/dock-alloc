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

use dock_alloc_core::domain::{SpaceInterval, TimeInterval};
use dock_alloc_model::RequestId;
use num_traits::{PrimInt, Signed};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OperationData<T: PrimInt + Signed> {
    time: TimeInterval<T>,
    space: SpaceInterval,
}

impl<T: PrimInt + Signed> OperationData<T> {
    pub fn new(time: TimeInterval<T>, space: SpaceInterval) -> Self {
        Self { time, space }
    }

    pub fn time(&self) -> TimeInterval<T> {
        self.time
    }

    pub fn space(&self) -> SpaceInterval {
        self.space
    }
}

impl<T: PrimInt + Signed + Display> Display for OperationData<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "OperationData(time: {}, space: {})",
            self.time, self.space
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Operation<T: PrimInt + Signed> {
    Free(OperationData<T>),
    Occupy(OperationData<T>),
}

impl<T: PrimInt + Signed> Operation<T> {
    pub fn data(&self) -> &OperationData<T> {
        match self {
            Operation::Free(d) => d,
            Operation::Occupy(d) => d,
        }
    }
}

impl<T: PrimInt + Signed + Display> Display for Operation<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operation::Free(d) => write!(f, "Free({})", d),
            Operation::Occupy(d) => write!(f, "Occupy({})", d),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RequestEdit<T: PrimInt + Signed> {
    id: RequestId,
    time: TimeInterval<T>,
    space: SpaceInterval,
}

impl<T: PrimInt + Signed> RequestEdit<T> {
    pub fn new(id: RequestId, time: TimeInterval<T>, space: SpaceInterval) -> Self {
        Self { id, time, space }
    }

    pub fn id(&self) -> RequestId {
        self.id
    }

    pub fn time(&self) -> TimeInterval<T> {
        self.time
    }

    pub fn space(&self) -> SpaceInterval {
        self.space
    }
}

impl<T: PrimInt + Signed + Display> Display for RequestEdit<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "RequestEdit(id: {}, time: {}, space: {})",
            self.id, self.time, self.space
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssignEdit<T: PrimInt + Signed> {
    Set(RequestEdit<T>),
    Clear(RequestId),
}

impl<T: PrimInt + Signed> AssignEdit<T> {
    pub fn request_id(&self) -> RequestId {
        match self {
            AssignEdit::Set(e) => e.id(),
            AssignEdit::Clear(id) => *id,
        }
    }
}

impl<T: PrimInt + Signed + Display> Display for AssignEdit<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AssignEdit::Set(e) => write!(f, "Set({})", e),
            AssignEdit::Clear(id) => write!(f, "Clear({})", id),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Footprint<T: PrimInt + Signed> {
    time: TimeInterval<T>,
    space: SpaceInterval,
}

impl<T: PrimInt + Signed> Footprint<T> {
    pub fn new(time: TimeInterval<T>, space: SpaceInterval) -> Self {
        Self { time, space }
    }

    pub fn time(&self) -> TimeInterval<T> {
        self.time
    }

    pub fn space(&self) -> SpaceInterval {
        self.space
    }
}
