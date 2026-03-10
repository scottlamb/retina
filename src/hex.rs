// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Quick wrapper around `pretty-hex` to limit output.

use std::borrow::Cow;

use pretty_hex::PrettyHex;

pub struct LimitedHex<'a> {
    first: &'a [u8],
    second: &'a [u8],
    full_len: usize,
}

impl<'a> LimitedHex<'a> {
    pub fn new(inner: &'a [u8], max_bytes: usize) -> Self {
        let truncated_len = inner.len().min(max_bytes);
        Self {
            first: &inner[..truncated_len],
            second: &[],
            full_len: inner.len(),
        }
    }

    /// Creates a `LimitedHex` from a [`Split`](crate::inputs::Split).
    ///
    /// Truncates to `max_bytes` before storing, so the allocation
    /// (if the split wraps) is bounded. The allocation itself is deferred
    /// to `Display`/`Debug` time, so it is avoided entirely when the
    /// output is not actually rendered (e.g. disabled `trace!` calls).
    pub fn from_split(split: crate::inputs::Split<'a>, max_bytes: usize) -> Self {
        use crate::inputs::Input as _;
        let full_len = split.len();
        let len = full_len.min(max_bytes);
        let mut truncated = split;
        let truncated = truncated.next_slice(len);
        let (first, second) = truncated.slices();
        Self {
            first,
            second,
            full_len,
        }
    }

    /// Returns the (pre-truncated) data as a contiguous `Cow`, allocating
    /// only if the data spans both halves of a ring buffer.
    fn to_cow(&self) -> Cow<'a, [u8]> {
        if self.second.is_empty() {
            Cow::Borrowed(self.first)
        } else {
            let mut v = Vec::with_capacity(self.first.len() + self.second.len());
            v.extend_from_slice(self.first);
            v.extend_from_slice(self.second);
            Cow::Owned(v)
        }
    }

    fn omitted(&self) -> usize {
        self.full_len - self.first.len() - self.second.len()
    }
}

impl std::fmt::Display for LimitedHex<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data = self.to_cow();
        let hex = data.hex_conf(pretty_hex::HexConfig {
            title: false,
            width: 0,
            group: 0,
            chunk: 0,
            ..Default::default()
        });
        write!(f, "Length: {0} (0x{0:x}) bytes\n{hex:#}", self.full_len)?;
        let omitted = self.omitted();
        if omitted > 0 {
            write!(f, "\n...{0} (0x{0:x}) bytes not shown...", omitted)?;
        }
        Ok(())
    }
}

impl std::fmt::Debug for LimitedHex<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data = self.to_cow();
        let hex = data.hex_conf(pretty_hex::HexConfig {
            title: false,
            ..Default::default()
        });
        write!(f, "Length: {0} (0x{0:x}) bytes\n{hex:#?}", self.full_len)?;
        let omitted = self.omitted();
        if omitted > 0 {
            write!(f, "\n...{0} (0x{0:x}) bytes not shown...", omitted)?;
        }
        Ok(())
    }
}
