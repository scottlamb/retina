// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

#![no_main]

use libfuzzer_sys::fuzz_target;
use retina::rtsp::{
    inputs::{Contiguous, Slice as _, Split},
    msg::Message,
    parse::Parser,
};

/// Parse with the given input, round-trip, and compare.
fn check<'i, I: retina::rtsp::inputs::Input<'i>>(data: &[u8], mut input: I, initial_len: usize)
where
    I::Slice: std::fmt::Debug,
{
    let Ok(Some((head, body_slice))) = Parser::default().feed(&mut input) else {
        return;
    };
    let consumed = initial_len - input.len();
    let body_cow = body_slice.to_cow();

    // Strip leading CRLFs from the original (the parser skips them).
    let mut expected = &data[..consumed];
    while let [b'\r', b'\n', rest @ ..] = expected {
        expected = rest;
    }

    let mut out = Vec::with_capacity(consumed);
    match &head {
        Message::Request(req) => {
            req.write_head(&mut out).unwrap();
            out.extend_from_slice(&body_cow);
        }
        Message::Response(resp) => {
            resp.write_head(&mut out).unwrap();
            out.extend_from_slice(&body_cow);
        }
        Message::Data(d) => {
            d.write(&mut out).unwrap();
            out.extend_from_slice(&body_cow);
        }
    }
    assert_eq!(
        out,
        expected,
        "round-trip mismatch on {head:#?}\n\
         expected ({} bytes): {expected:02x?}\n\
         got ({} bytes): {out:02x?}",
        expected.len(),
        out.len(),
    );
}

fuzz_target!(|data: &[u8]| {
    retina_fuzz::init_logging();

    let initial_len = data.len();

    // Test with Contiguous input.
    check(data, Contiguous::new(data, false), initial_len);

    // Test with Split input at every possible split point.
    for split in 0..=data.len() {
        let (first, second) = data.split_at(split);
        check(data, Split::new(first, second, false), initial_len);
    }
});
