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

use crate::registry::operations::Operation;
use dock_alloc_core::SolverVariable;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LedgerOverlayCommit<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    amount_unassigned: usize,
    amount_assigned: usize,
    operations: Vec<Operation<'a, T, C>>,
}

impl<'a, T, C> LedgerOverlayCommit<'a, T, C>
where
    T: SolverVariable,
    C: SolverVariable,
{
    pub fn new(
        operations: Vec<Operation<'a, T, C>>,
        amount_unassigned: usize,
        amount_assigned: usize,
    ) -> Self {
        Self {
            operations,
            amount_unassigned,
            amount_assigned,
        }
    }

    pub fn operations(&self) -> &[Operation<'a, T, C>] {
        &self.operations
    }

    pub fn is_empty(&self) -> bool {
        self.operations.is_empty()
    }

    pub fn amount_unassigned(&self) -> usize {
        self.amount_unassigned
    }

    pub fn amount_assigned(&self) -> usize {
        self.amount_assigned
    }
}

#[cfg(test)]
mod tests {
    use static_assertions::assert_impl_all;

    assert_impl_all!(crate::registry::commit::LedgerOverlayCommit<'static, i64, i64>: Send, Sync);
}
