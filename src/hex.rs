// Copyright (C) 2022 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Quick wrapper around `pretty-hex` to limit output.
//!
//! TODO: remove this if [wolandr/pretty-hex#9](https://github.com/wolandr/pretty-hex/pull/9)
//! is merged.

use pretty_hex::PrettyHex;

pub struct LimitedHex<'a> {
    inner: &'a [u8],
    max_bytes: usize,
}

impl<'a> LimitedHex<'a> {
    pub fn new(inner: &'a [u8], max_bytes: usize) -> Self {
        Self { inner, max_bytes }
    }
}

impl<'a> std::fmt::Debug for LimitedHex<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let omitted = self.inner.len().checked_sub(self.max_bytes);
        let print = if omitted.is_some() {
            &self.inner[..self.max_bytes]
        } else {
            self.inner
        };
        writeln!(f, "Length: {0} (0x{0:x}) bytes", self.inner.len())?;
        writeln!(
            f,
            "{:#?}",
            print.hex_conf(pretty_hex::HexConfig {
                title: false,
                ..Default::default()
            })
        )?;
        if let Some(o) = omitted {
            write!(f, "\n...{0} (0x{0:x}) bytes not shown...", o)?;
        }
        Ok(())
    }
}
