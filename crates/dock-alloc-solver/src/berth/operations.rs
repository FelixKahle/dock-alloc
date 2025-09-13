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

use crate::domain::SpaceTimeRectangle;
use dock_alloc_core::SolverVariable;
use std::fmt::Display;

#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FreeOperation<T>(SpaceTimeRectangle<T>)
where
    T: SolverVariable;

impl<T> FreeOperation<T>
where
    T: SolverVariable,
{
    pub fn new(rect: SpaceTimeRectangle<T>) -> Self {
        Self(rect)
    }

    pub fn rectangle(&self) -> &SpaceTimeRectangle<T> {
        &self.0
    }
}

impl<T> Display for FreeOperation<T>
where
    T: SolverVariable,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FreeOperation({})", self.0)
    }
}

impl<T> From<SpaceTimeRectangle<T>> for FreeOperation<T>
where
    T: SolverVariable,
{
    fn from(rect: SpaceTimeRectangle<T>) -> Self {
        Self::new(rect)
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OccupyOperation<T>(SpaceTimeRectangle<T>)
where
    T: SolverVariable;

impl<T> OccupyOperation<T>
where
    T: SolverVariable,
{
    pub fn new(rect: SpaceTimeRectangle<T>) -> Self {
        Self(rect)
    }

    pub fn rectangle(&self) -> &SpaceTimeRectangle<T> {
        &self.0
    }
}

impl<T> Display for OccupyOperation<T>
where
    T: SolverVariable,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "OccupyOperation({})", self.0)
    }
}

impl<T> From<SpaceTimeRectangle<T>> for OccupyOperation<T>
where
    T: SolverVariable,
{
    fn from(rect: SpaceTimeRectangle<T>) -> Self {
        Self::new(rect)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operation<T>
where
    T: SolverVariable,
{
    Occupy(OccupyOperation<T>),
    Free(FreeOperation<T>),
}

impl<T> Operation<T>
where
    T: SolverVariable,
{
    pub fn rectangle(&self) -> &SpaceTimeRectangle<T> {
        match self {
            Operation::Occupy(occ) => occ.rectangle(),
            Operation::Free(free) => free.rectangle(),
        }
    }
}

impl<T> Display for Operation<T>
where
    T: SolverVariable,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operation::Occupy(occ) => write!(f, "{}", occ),
            Operation::Free(free) => write!(f, "{}", free),
        }
    }
}

impl<T> From<OccupyOperation<T>> for Operation<T>
where
    T: SolverVariable,
{
    fn from(op: OccupyOperation<T>) -> Self {
        Self::Occupy(op)
    }
}

impl<T> From<FreeOperation<T>> for Operation<T>
where
    T: SolverVariable,
{
    fn from(op: FreeOperation<T>) -> Self {
        Self::Free(op)
    }
}
