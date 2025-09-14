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
