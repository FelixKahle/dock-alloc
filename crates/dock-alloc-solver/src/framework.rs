// Copyright (c) 2025 Felix Kahle.
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to do so, subject to the following conditions:
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
    quay::QuayRead,
    search::{Plan, ProposeCtx},
};
use dock_alloc_model::{Problem, Solution};
use num_traits::{PrimInt, Signed};

pub type ProposeResult<T, V> = Result<Option<Plan<T>>, V>;

pub trait Operator<T, C, Q, R>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
    Q: QuayRead,
    R: rand::Rng + ?Sized,
{
    type Error;

    fn propose<'brand>(
        &self,
        iter: usize,
        rng: &mut R,
        ctx: &'brand ProposeCtx<'brand, T, C, Q>,
    ) -> ProposeResult<T, Self::Error>;
}

pub trait Solver<T, C>
where
    T: PrimInt + Signed,
    C: PrimInt + Signed,
{
    type Error;

    fn solve(&self, problem: Problem<T, C>) -> Result<Solution<T, C>, Self::Error>;
}
