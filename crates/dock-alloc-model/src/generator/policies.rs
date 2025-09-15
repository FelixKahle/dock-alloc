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
// THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

use std::fmt::Display;

use dock_alloc_core::space::SpaceLength;

#[derive(Debug, Clone, PartialEq)]
pub struct RelativeSpaceWindowPolicy {
    pub frac_of_length: f64,
    pub min: SpaceLength,
    pub max: SpaceLength,
}

impl RelativeSpaceWindowPolicy {
    pub fn new(frac_of_length: f64, min: SpaceLength, max: SpaceLength) -> Self {
        Self {
            frac_of_length,
            min,
            max,
        }
    }
}

impl Display for RelativeSpaceWindowPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "RelativeSpaceWindowPolicy {{ frac_of_length: {:.4}, min: {}, max: {} }}",
            self.frac_of_length, self.min, self.max
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum HalfwidthPolicy {
    Fixed(SpaceLength),
    Relative(RelativeSpaceWindowPolicy),
}

impl Display for HalfwidthPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HalfwidthPolicy::Fixed(hw) => write!(f, "HalfwidthPolicy::Fixed({})", hw),
            HalfwidthPolicy::Relative(r) => write!(f, "HalfwidthPolicy::Relative({})", r),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum SpaceWindowPolicy {
    Halfwidth(HalfwidthPolicy),
    FullQuay,
}

impl SpaceWindowPolicy {
    #[inline]
    pub fn full_quay() -> Self {
        Self::FullQuay
    }

    #[inline]
    pub fn fixed(halfwidth: SpaceLength) -> Self {
        Self::Halfwidth(HalfwidthPolicy::Fixed(halfwidth))
    }

    #[inline]
    pub fn relative(frac: f64, min: SpaceLength, max: SpaceLength) -> Self {
        Self::Halfwidth(HalfwidthPolicy::Relative(RelativeSpaceWindowPolicy::new(
            frac, min, max,
        )))
    }
}

impl Display for SpaceWindowPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpaceWindowPolicy::Halfwidth(hp) => write!(f, "Halfwidth({})", hp),
            SpaceWindowPolicy::FullQuay => write!(f, "FullQuay"),
        }
    }
}
