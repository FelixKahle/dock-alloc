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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuayTooShortError {
    quay_length: SpaceLength,
    max_ship_length: SpaceLength,
}

impl QuayTooShortError {
    pub fn new(quay_length: SpaceLength, max_ship_length: SpaceLength) -> Self {
        Self {
            quay_length,
            max_ship_length,
        }
    }
    pub fn quay_length(&self) -> SpaceLength {
        self.quay_length
    }
    pub fn max_ship_length(&self) -> SpaceLength {
        self.max_ship_length
    }
}

impl Display for QuayTooShortError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "QuayTooShortError: quay_length {} is shorter than max ship length {}",
            self.quay_length, self.max_ship_length
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstanceGenConfigBuildError {
    QuayTooShort(QuayTooShortError),
    MissingQuayLength,
    MissingMinLength,
    MissingMaxLength,
    MissingHorizon,
    MissingSpaceWindowPolicy,
    MissingAmountMovables,
    MissingAmountFixed,
}

impl Display for InstanceGenConfigBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use InstanceGenConfigBuildError::*;
        match self {
            QuayTooShort(e) => write!(f, "{}", e),
            MissingQuayLength => write!(f, "Missing quay_length"),
            MissingMinLength => write!(f, "Missing min_length"),
            MissingMaxLength => write!(f, "Missing max_length"),
            MissingHorizon => write!(f, "Missing horizon"),
            MissingSpaceWindowPolicy => write!(f, "Missing space_window_policy"),
            MissingAmountMovables => write!(f, "Missing amount_movables"),
            MissingAmountFixed => write!(f, "Missing amount_fixed"),
        }
    }
}

impl From<QuayTooShortError> for InstanceGenConfigBuildError {
    fn from(err: QuayTooShortError) -> Self {
        Self::QuayTooShort(err)
    }
}

impl std::error::Error for InstanceGenConfigBuildError {}
