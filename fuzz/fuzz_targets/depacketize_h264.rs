// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Fuzzes depacketization, checking that streaming and accumulating
//! depacketizers agree.

#![no_main]
use derive_more::Debug;
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use libfuzzer_sys::fuzz_target;
use pretty_hex::PrettyHex as _;
use retina::codec::Accumulate;
use retina_fuzz::CheckingHandler;
use std::num::NonZeroU32;

#[derive(Arbitrary, Debug)]
struct Pkt<'i> {
    ts_change: bool,
    mark: bool,
    loss: bool,

    #[debug("{:?}", payload.hex_conf(retina::testutil::NONASCII_HEX_CONFIG))]
    payload: &'i [u8],
}

fuzz_target!(|pkts: Vec<Pkt<'_>>| {
    retina_fuzz::init_logging();
    let new = || {
        retina::codec::VideoDepacketizer::<u64>::new("h264", 90_000, Some("packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA")).unwrap()
    };
    let mut accumulating = new();
    let mut streaming = new();
    let mut accumulating_h = CheckingHandler::new(Accumulate::Yes, true);
    let mut streaming_h = CheckingHandler::new(Accumulate::No, true);
    let mut timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();
    let mut sequence_number: u16 = 0;
    let mut buf = retina::buf::MarkBuf::new(65536);
    for (i, pkt) in pkts.iter().enumerate() {
        log::trace!("pkt: {pkt:?}");
        if pkt.loss {
            sequence_number = sequence_number.wrapping_add(1);
        }
        if pkt.ts_change {
            timestamp = timestamp.try_add(1).unwrap();
        }
        let meta = retina::rtp::ReceivedPacketMeta::new(
            i as u64,
            timestamp,
            sequence_number,
            0,
            pkt.mark,
            retina::rtp::Continuity::from_loss(u16::from(pkt.loss)),
        );
        let Ok(_) = u16::try_from(pkt.payload.len()) else {
            return;
        };
        retina_fuzz::push(
            &mut buf,
            meta,
            pkt.payload,
            &mut [
                (&mut accumulating, &mut accumulating_h),
                (&mut streaming, &mut streaming_h),
            ],
        );
        sequence_number = sequence_number.wrapping_add(1);
    }
    assert_eq!(accumulating_h.events, streaming_h.events);
    for f in &accumulating_h.frames {
        retina::testutil::validate_avcc_frame(f).unwrap();
    }
});
