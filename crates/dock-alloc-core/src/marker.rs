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

/// A marker type to create a lifetime dependency without actually storing a reference.
///
/// This is useful to create types that are generic over a lifetime without actually
/// storing a reference with that lifetime.
/// This is a zero-cost abstraction, as the compiler optimizes away the
/// `PhantomData` field.
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Brand<'x>(std::marker::PhantomData<fn(&'x ()) -> &'x ()>);

impl<'x> Brand<'x> {
    /// Create a new `Brand` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use dock_alloc_core::marker::Brand;
    ///
    /// let brand: Brand<'static> = Brand::new();
    /// ```
    #[inline(always)]
    pub const fn new() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl<'x> From<()> for Brand<'x> {
    #[inline(always)]
    fn from(_: ()) -> Self {
        Self::new()
    }
}

impl<'x> std::fmt::Display for Brand<'x> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Brand")
    }
}
