// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

mod h264;

pub use h264::{H264DtsExtractor, H264DtsExtractorError};

pub(crate) struct NalUnitIter<'a> {
    remaining: &'a [u8],
}

impl<'a> NalUnitIter<'a> {
    pub(crate) fn new(data: &'a [u8]) -> Self {
        Self { remaining: data }
    }
}

impl<'a> Iterator for NalUnitIter<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining.is_empty() {
            return None;
        }

        let (nal_len, remaining) = self.remaining.split_at(4);
        let nal_len = u32::from_be_bytes(nal_len.try_into().expect("u32 should be 4 bytes"));
        let (nalu, remaining) = remaining.split_at(
            nal_len
                .try_into()
                .expect("usize should be convertible from u32"),
        );
        self.remaining = remaining;

        Some(nalu)
    }
}
