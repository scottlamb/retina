// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

#![no_main]

use libfuzzer_sys::fuzz_target;
use retina::inputs::{Input, Split};
use retina::rtsp::{msg::Message, parse::Parser};

/// Serializes a parsed message and its body.
fn serialize(head: &Message, body: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    match head {
        Message::Request(req) => req.write_head(&mut out).unwrap(),
        Message::Response(resp) => resp.write_head(&mut out).unwrap(),
        Message::Data(d) => d.write(&mut out).unwrap(),
    }
    out.extend_from_slice(body);
    out
}

/// Parses with the given input, serializes, reparses, and compares.
///
/// This compares parsed messages rather than bytes because parsing doesn't
/// preserve header order or name case, so real-world messages generally
/// don't serialize back to the original bytes.
fn check<'i, I: Input<'i> + std::fmt::Debug>(mut input: I) {
    let Ok(Some((head, body_slice))) = Parser::default().feed(&mut input) else {
        return;
    };
    let body = body_slice.to_cow();
    let out = serialize(&head, &body);

    let mut reparse_input = &out[..];
    let (reparsed_head, reparsed_body) = match Parser::default().feed(&mut reparse_input) {
        Ok(Some(m)) => m,
        o => panic!(
            "failed to reparse {head:#?}: {o:?}\n\
             serialized ({} bytes): {out:02x?}",
            out.len(),
        ),
    };
    assert!(
        reparse_input.is_empty(),
        "reparse of {head:#?} left {} trailing bytes\n\
         serialized ({} bytes): {out:02x?}",
        reparse_input.len(),
        out.len(),
    );
    assert_eq!(
        (&reparsed_head, reparsed_body),
        (&head, &body[..]),
        "round-trip mismatch\n\
         serialized ({} bytes): {out:02x?}",
        out.len(),
    );
}

/// Inputs up to this length are tested at every split point.
const MAX_EXHAUSTIVE_LEN: usize = 256;

/// For longer inputs, the number of split points tested at each edge and in
/// the evenly-spaced middle.
const EDGE_SPLITS: usize = 16;
const MIDDLE_SPLITS: usize = 64;

/// Returns the split points to test, in increasing order without duplicates.
fn split_points(len: usize) -> impl Iterator<Item = usize> {
    let stride = if len <= MAX_EXHAUSTIVE_LEN {
        1
    } else {
        len.div_ceil(MIDDLE_SPLITS)
    };
    (0..=len).filter(move |&s| {
        stride == 1 || s <= EDGE_SPLITS || s >= len - EDGE_SPLITS || s % stride == 0
    })
}

fuzz_target!(|data: &[u8]| {
    retina_fuzz::init_logging();

    // Test with contiguous &[u8] input.
    check(data);

    // Test with Split input at a bounded number of split points: all of them
    // for short inputs, or the edges plus evenly-spaced points for long ones.
    // Checking every split point makes each run cost O(len * parse cost),
    // which can exceed libFuzzer's timeout for long inputs that are
    // individually slow to parse (e.g. 1 KiB+ Punycode hostnames, which
    // `idna` decodes in quadratic time).
    for split in split_points(data.len()) {
        let (first, second) = data.split_at(split);
        check(Split::new(first, second));
    }
});
