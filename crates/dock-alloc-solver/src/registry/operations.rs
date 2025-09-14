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

use dock_alloc_core::SolverVariable;
use dock_alloc_model::prelude::*;
use std::fmt::Display;

#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignOperation<'a, T, C>(AssignmentRef<'a, Movable, T, C>)
where
    T: SolverVariable,
    C: SolverVariable;

impl<'a, T, C> AssignOperation<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    pub fn new(assignment: AssignmentRef<'a, Movable, T, C>) -> Self {
        Self(assignment)
    }

    pub fn assignment(&self) -> &AssignmentRef<'a, Movable, T, C> {
        &self.0
    }
}

impl<'a, T, C> From<AssignmentRef<'a, Movable, T, C>> for AssignOperation<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    fn from(assignment: AssignmentRef<'a, Movable, T, C>) -> Self {
        Self::new(assignment)
    }
}

impl<'a, T, C> Display for AssignOperation<'a, T, C>
where
    T: SolverVariable + Display,
    C: SolverVariable + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Assign({})", self.0)
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnassignOperation<'a, T, C>(AssignmentRef<'a, Movable, T, C>)
where
    T: SolverVariable,
    C: SolverVariable;

impl<'a, T, C> UnassignOperation<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    pub fn new(assignment: AssignmentRef<'a, Movable, T, C>) -> Self {
        Self(assignment)
    }

    pub fn assignment(&self) -> &AssignmentRef<'a, Movable, T, C> {
        &self.0
    }
}

impl<'a, T, C> From<AssignmentRef<'a, Movable, T, C>> for UnassignOperation<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    fn from(assignment: AssignmentRef<'a, Movable, T, C>) -> Self {
        Self::new(assignment)
    }
}

impl<'a, T, C> Display for UnassignOperation<'a, T, C>
where
    T: SolverVariable + Display,
    C: SolverVariable + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Unassign({})", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operation<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    Assign(AssignOperation<'a, T, C>),
    Unassign(UnassignOperation<'a, T, C>),
}

impl<'a, T, C> Operation<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    pub fn assignment(&self) -> &AssignmentRef<'a, Movable, T, C> {
        match self {
            Operation::Assign(op) => op.assignment(),
            Operation::Unassign(op) => op.assignment(),
        }
    }
}

impl<'a, T, C> From<AssignOperation<'a, T, C>> for Operation<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    fn from(op: AssignOperation<'a, T, C>) -> Self {
        Self::Assign(op)
    }
}

impl<'a, T, C> From<UnassignOperation<'a, T, C>> for Operation<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    fn from(op: UnassignOperation<'a, T, C>) -> Self {
        Self::Unassign(op)
    }
}

impl<'a, T, C> Display for Operation<'a, T, C>
where
    T: SolverVariable + Display,
    C: SolverVariable + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operation::Assign(op) => write!(f, "{}", op),
            Operation::Unassign(op) => write!(f, "{}", op),
        }
    }
}
