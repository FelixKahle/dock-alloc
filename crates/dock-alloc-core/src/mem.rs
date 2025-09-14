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

use std::{
    borrow::{Borrow, BorrowMut},
    ops::{Deref, DerefMut, Index, IndexMut},
    slice::SliceIndex,
};

/// A double-buffering utility built on two `Vec<T>`s.
///
/// This structure is designed to simplify iterative algorithms where the state of the
/// next step is computed based on the state of the current step. It manages two
/// internal buffers: a **current** buffer (for reading) and an **alternate** buffer
/// (for writing).
///
/// The core operation is [`step`], which takes a closure. This closure receives an
/// immutable slice of the `current` buffer and a mutable reference to the `alternate`
/// buffer. You compute the next state inside the closure and write it to the alternate
/// buffer. Once the closure returns, [`step`] automatically swaps the buffers, so the
/// newly computed state becomes the `current` one for the next iteration.
///
/// This approach avoids the need for expensive cloning or complex index management
/// when an algorithm cannot safely modify the data in-place.
///
/// ## Use Cases
///
/// `DoubleBuf` is particularly useful for:
/// - **Simulations**: Cellular automata like Conway's Game of Life, where the next
///   state of each cell depends on the current state of its neighbors.
/// - **Game Development**: Managing game states between frames, where the next frame's
///   state is calculated from the previous one.
/// - **Data Processing**: Iterative data transformations where the entire input is
///   needed to generate the output.
///
/// ## Ergonomics
///
/// To make it easy to use, `DoubleBuf` implements several traits (`Deref`, `AsRef`,
/// `Index`, `IntoIterator`, etc.) that delegate to the **current** buffer. This allows you
/// to treat a `DoubleBuf<T>` much like you would a `Vec<T>` or `&[T]` for most
/// reading and direct modification purposes.
#[derive(Debug, Default, Clone, Hash, PartialEq, Eq)]
pub struct DoubleBuf<T> {
    a: Vec<T>,
    b: Vec<T>,
}

impl<T> DoubleBuf<T> {
    #[inline]
    pub fn new() -> Self {
        Self {
            a: Vec::new(),
            b: Vec::new(),
        }
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            a: Vec::with_capacity(capacity),
            b: Vec::with_capacity(capacity),
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.a.clear();
        self.b.clear();
    }

    #[inline]
    pub fn current(&self) -> &[T] {
        &self.a
    }

    #[inline]
    pub fn current_mut(&mut self) -> &mut Vec<T> {
        &mut self.a
    }

    #[inline]
    pub fn alternate(&self) -> &[T] {
        &self.b
    }

    #[inline]
    pub fn alternate_mut(&mut self) -> &mut Vec<T> {
        &mut self.b
    }

    #[inline]
    pub fn seed_from_iter<I: IntoIterator<Item = T>>(&mut self, it: I) {
        self.a.clear();
        self.a.extend(it);
    }

    #[inline]
    pub fn seed_from_slice(&mut self, slice: &[T])
    where
        T: Clone,
    {
        self.a.clear();
        self.a.extend_from_slice(slice);
    }

    #[inline]
    pub fn step<F>(&mut self, func: F)
    where
        F: FnOnce(&[T], &mut Vec<T>),
    {
        self.b.clear();
        func(&self.a, &mut self.b);
        core::mem::swap(&mut self.a, &mut self.b);
    }

    #[inline]
    pub fn copy_current_into(&self, dst: &mut Vec<T>)
    where
        T: Clone,
    {
        dst.clear();
        dst.extend_from_slice(&self.a);
    }

    #[inline]
    pub fn move_current_into(&mut self, dst: &mut Vec<T>) {
        dst.clear();
        core::mem::swap(&mut self.a, dst);
        self.a.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::DoubleBuf;

    #[test]
    fn test_new_is_empty() {
        let db: DoubleBuf<i32> = DoubleBuf::new();
        assert!(db.current().is_empty());
        assert!(db.alternate().is_empty());
    }

    #[test]
    fn test_with_capacity_reserves() {
        let cap = 16;
        let mut db: DoubleBuf<i32> = DoubleBuf::with_capacity(cap);
        assert!(db.current().is_empty());
        assert!(db.alternate().is_empty());
        assert!(db.current_mut().capacity() >= cap);
        assert!(db.alternate_mut().capacity() >= cap);
    }

    #[test]
    fn test_clear_empties_both() {
        let mut db = DoubleBuf::new();
        db.current_mut().extend([1, 2, 3]);
        db.alternate_mut().extend([4, 5]);
        db.clear();
        assert!(db.current().is_empty());
        assert!(db.alternate().is_empty());
    }

    #[test]
    fn test_seed_from_iter_replaces() {
        let mut db = DoubleBuf::new();
        db.current_mut().extend([9, 9, 9]);
        db.seed_from_iter([1, 2, 3]);
        assert_eq!(db.current(), &[1, 2, 3]);
        assert_eq!(db.alternate(), &[]);
    }

    #[test]
    fn test_seed_from_slice_clones() {
        let mut db = DoubleBuf::new();
        let src = vec![String::from("a"), String::from("b")];
        db.seed_from_slice(&src);
        assert_eq!(db.current(), &["a".to_string(), "b".to_string()]);
        assert_eq!(src, vec!["a".to_string(), "b".to_string()]);
    }

    #[test]
    fn test_step_transforms_and_swaps() {
        let mut db = DoubleBuf::new();
        db.seed_from_iter([1, 2, 3]);
        db.step(|input, out| {
            out.extend(input.iter().map(|x| x * x).rev());
        });
        assert_eq!(db.current(), &[9, 4, 1]);
        assert_eq!(db.alternate(), &[1, 2, 3]);
    }

    #[test]
    fn test_step_empty_output() {
        let mut db = DoubleBuf::new();
        db.seed_from_iter([1, 2, 3]);
        db.alternate_mut().extend([7, 8, 9]);
        db.step(|_input, _out| {
            // no output
        });
        assert!(db.current().is_empty());
        assert_eq!(db.alternate(), &[1, 2, 3]);
    }

    #[test]
    fn test_copy_current_into_overwrites() {
        let mut db = DoubleBuf::new();
        db.seed_from_iter([1, 2, 3]);
        let mut dst = vec![10, 11];
        db.copy_current_into(&mut dst);
        assert_eq!(dst, vec![1, 2, 3]);
        assert_eq!(db.current(), &[1, 2, 3]);
    }

    #[test]
    fn test_move_current_into_moves() {
        let mut db = DoubleBuf::new();
        db.seed_from_iter(vec![String::from("x"), String::from("y")]);
        let mut dst = vec![String::from("old")];
        db.move_current_into(&mut dst);
        assert_eq!(dst, vec![String::from("x"), String::from("y")]);
        assert!(db.current().is_empty());
        assert!(db.alternate().is_empty());

        db.seed_from_iter(vec![String::from("z")]);
        db.move_current_into(&mut dst);
        assert_eq!(dst, vec![String::from("z")]);
        assert!(db.current().is_empty());
    }

    #[test]
    fn test_alternate_mut_isolated() {
        let mut db = DoubleBuf::new();
        db.seed_from_iter([1, 2]);
        db.alternate_mut().extend([42, 43, 44]);
        assert_eq!(db.current(), &[1, 2]);
        db.step(|input, out| {
            out.extend_from_slice(input);
        });
        assert_eq!(db.current(), &[1, 2]);
        assert_eq!(db.alternate(), &[1, 2]);
    }

    #[test]
    fn test_multiple_steps_prev_in_alternate() {
        let mut db = DoubleBuf::new();
        db.seed_from_iter([1, 2, 3, 4]);

        db.step(|input, out| {
            out.extend(input.iter().copied().filter(|x| x % 2 == 0));
        });
        assert_eq!(db.current(), &[2, 4]);
        assert_eq!(db.alternate(), &[1, 2, 3, 4]);

        db.step(|input, out| {
            out.extend(input.iter().map(|x| x * 2));
        });
        assert_eq!(db.current(), &[4, 8]);
        assert_eq!(db.alternate(), &[2, 4]);

        db.step(|_input, _out| {});
        assert_eq!(db.current(), &[]);
        assert_eq!(db.alternate(), &[4, 8]);
    }

    #[test]
    fn test_current_mut_vec_ops() {
        let mut db = DoubleBuf::new();
        {
            let v = db.current_mut();
            v.push(1);
            v.push(2);
            v.push(3);
        }
        assert_eq!(db.current(), &[1, 2, 3]);
        assert_eq!(db.current_mut().pop(), Some(3));
        assert_eq!(db.current(), &[1, 2]);
    }

    #[test]
    fn test_seed_empty_and_step() {
        let mut db: DoubleBuf<i32> = DoubleBuf::new();
        db.seed_from_iter(std::iter::empty());
        assert!(db.current().is_empty());
        db.step(|input, out| {
            assert!(input.is_empty());
            out.extend([7, 8]);
        });
        assert_eq!(db.current(), &[7, 8]);
        assert!(db.alternate().is_empty());
    }
}

impl<T> AsRef<[T]> for DoubleBuf<T> {
    fn as_ref(&self) -> &[T] {
        &self.a
    }
}

impl<T> AsMut<[T]> for DoubleBuf<T> {
    fn as_mut(&mut self) -> &mut [T] {
        &mut self.a
    }
}

impl<T> Borrow<[T]> for DoubleBuf<T> {
    fn borrow(&self) -> &[T] {
        &self.a
    }
}

impl<T> BorrowMut<[T]> for DoubleBuf<T> {
    fn borrow_mut(&mut self) -> &mut [T] {
        &mut self.a
    }
}

impl<T> Deref for DoubleBuf<T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        &self.a
    }
}

impl<T> DerefMut for DoubleBuf<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.a
    }
}

impl<T, I> Index<I> for DoubleBuf<T>
where
    I: SliceIndex<[T]>,
{
    type Output = I::Output;
    fn index(&self, index: I) -> &Self::Output {
        &self.a[index]
    }
}

impl<T, I> IndexMut<I> for DoubleBuf<T>
where
    I: SliceIndex<[T]>,
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.a[index]
    }
}

impl<'a, T> IntoIterator for &'a DoubleBuf<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.a.iter()
    }
}
impl<'a, T> IntoIterator for &'a mut DoubleBuf<T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.a.iter_mut()
    }
}

impl<T> Extend<T> for DoubleBuf<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.a.extend(iter)
    }
}

impl<T> FromIterator<T> for DoubleBuf<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut db = DoubleBuf::new();
        db.a.extend(iter);
        db
    }
}

impl<T> From<Vec<T>> for DoubleBuf<T> {
    fn from(v: Vec<T>) -> Self {
        Self {
            a: v,
            b: Vec::new(),
        }
    }
}

impl<T> From<DoubleBuf<T>> for Vec<T> {
    fn from(mut db: DoubleBuf<T>) -> Self {
        let mut v = Vec::new();
        db.move_current_into(&mut v);
        v
    }
}
