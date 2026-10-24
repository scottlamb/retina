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

    // The depacketizer always strips inline SPS/PPS NALs (they're managed
    // via ParameterSetInsertion). Reject inputs containing them since they
    // can't round-trip exactly.
    {
        let mut remaining = input.data;
        while let Some((len_bytes, rest)) = remaining.split_first_chunk::<4>() {
            let len = u32::from_be_bytes(*len_bytes) as usize;
            let nal_type = rest[0] & 0x1f;
            if nal_type == 7 || nal_type == 8 {
                return Corpus::Reject;
            }
            remaining = &rest[len..];
        }
    }

    let mut p = match retina::codec::h264::Packetizer::new(input.max_payload_size, 0, 0, 0) {
        Ok(p) => p,
        Err(_) => return Corpus::Reject,
    };
    let mut d = retina::codec::VideoDepacketizer::<u64>::new(
        "h264",
        90_000,
        Some("packetization-mode=1;sprop-parameter-sets=J01AHqkYGwe83gDUBAQG2wrXvfAQ,KN4JXGM4"),
    )
    .unwrap();
    // The packetizer doesn't insert parameter sets; `CheckingHandler` uses
    // `FrameFormat::MP4`, which doesn't either.
    let mut h = retina_fuzz::CheckingHandler::new(retina::codec::Accumulate::Yes, true);
    let timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();
    let mut buf = retina::buf::MarkBuf::new(65536);

    if p.push(timestamp, Bytes::copy_from_slice(input.data))
        .is_err()
    {
        return Corpus::Keep;
    }
    let frame = loop {
        match p.pull() {
            Ok(Some(pkt)) => {
                // Recover the metadata from the header, which also checks
                // header parsing in the round trip.
                let (header, payload) = retina::rtp::PacketHeader::validate(&pkt[..])
                    .expect("packetizer should produce valid RTP packets");
                let mark = header.mark();
                let meta = retina::rtp::ReceivedPacketMeta::new(
                    0,
                    retina::Timestamp::new(
                        i64::from(header.timestamp()),
                        timestamp.clock_rate(),
                        0,
                    )
                    .unwrap(),
                    header.sequence_number(),
                    header.ssrc(),
                    mark,
                    0,
                );
                let payload = &pkt[usize::from(payload.start)..usize::from(payload.end)];
                retina_fuzz::push(&mut buf, meta, payload, &mut [(&mut d, &mut h)]);
                if h.events
                    .iter()
                    .any(|e| matches!(e, retina_fuzz::Event::Loss(_)))
                {
                    return Corpus::Keep;
                }
                if let Some(f) = h.frames.pop() {
                    assert!(mark);
                    break f;
                }
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
            Ok(None) => panic!("packetizer ran out of packets before depacketizer produced frame"),
            Err(_) => return Corpus::Keep,
        }
    };
    assert_eq!(input.data, &frame[..]);
    assert_eq!(p.pull(), Ok(None));
    Corpus::Keep
});
