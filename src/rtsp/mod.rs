// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTSP/1.0 message types and parser.
//!
//! This is a hand-rolled streaming parser designed for use with both
//! contiguous and ring-buffer inputs via the [`crate::inputs::Input`] trait.

pub mod msg;
pub mod parse;
pub(crate) mod table;
