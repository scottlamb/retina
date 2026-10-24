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
        retina::codec::VideoDepacketizer::<u64>::new("h265", 90_000, Some("profile-id=1;sprop-sps=QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=;sprop-pps=RAHA8saNA7NA;sprop-vps=QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==")).unwrap()
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
            u16::from(pkt.loss),
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
});
