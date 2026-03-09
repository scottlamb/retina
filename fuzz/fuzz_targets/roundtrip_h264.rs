// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Tests that decode(encode(max_payload_size, frame)) == frame with
//! an arbitrary max_payload_size. Ensures the following:
//!
//! *   there are no crashes.
//! *   the round trip produces an error, nothing (see note about `can_end_au`), or identical data.
//!
//! This is not expected to exercise all the depacketizer paths because the packetizer will only emit
//! a strict, normalized form, where the depacketizer is expected to accept garbage.

#![no_main]
use bytes::Bytes;
use derive_more::Debug;
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use libfuzzer_sys::{Corpus, fuzz_target};
use pretty_hex::PrettyHex as _;
use std::num::NonZeroU32;

#[derive(Arbitrary, Debug)]
struct Input<'i> {
    max_payload_size: u16,
    #[debug("{:?}", data.hex_conf(retina::testutil::NONASCII_HEX_CONFIG))]
    data: &'i [u8],
}

fuzz_target!(|input: Input<'_>| -> Corpus {
    // The packetizer is not written to strip Annex B sequences, for example.
    if retina::testutil::validate_avcc_frame(input.data).is_err() {
        return Corpus::Reject;
    }

    let mut p = match retina::codec::h264::Packetizer::new(input.max_payload_size, 0, 0, 0, 0) {
        Ok(p) => p,
        Err(_) => return Corpus::Reject,
    };
    let mut d = retina::codec::Depacketizer::new(
        "video",
        "h264",
        90_000,
        None,
        Some("packetization-mode=1;sprop-parameter-sets=J01AHqkYGwe83gDUBAQG2wrXvfAQ,KN4JXGM4"),
    )
    .unwrap();
    let timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();

    if p.push(timestamp, Bytes::copy_from_slice(input.data))
        .is_err()
    {
        return Corpus::Keep;
    }
    let frame = loop {
        match p.pull() {
            Ok(Some(pkt)) => {
                let mark = pkt.mark();
                if d.push(pkt).is_err() {
                    return Corpus::Keep;
                }
                match d.pull() {
                    Some(Err(_)) => return Corpus::Keep,
                    Some(Ok(retina::codec::CodecItem::VideoFrame(f))) => {
                        assert!(mark);
                        break f;
                    }
                    Some(Ok(_)) => panic!(),
                    None => {
                        // XXX: assert!(!mark)
                        //
                        // One would expect that a frame would be produced if the packet has mark
                        // set. This used to be true, but Retina now has a workaround for some
                        // RTSP servers that spuriously set the mark bit. See
                        // `retina::codec::h264::can_end_au`. In this case, just exit.
                        if mark {
                            assert!(matches!(p.pull(), Ok(None)));
                            return Corpus::Keep;
                        }
                    }
                }
            }
            Ok(None) => panic!("packetizer ran out of packets before depacketizer produced frame"),
            Err(_) => return Corpus::Keep,
        }
    };
    assert_eq!(input.data, frame.data());
    assert_eq!(d.pull(), None);
    assert_eq!(p.pull(), Ok(None));
    Corpus::Keep
});
