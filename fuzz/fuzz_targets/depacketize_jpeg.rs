// Copyright (C) 2023 Niclas Olmenius <niclas@voysys.se>
// SPDX-License-Identifier: MIT OR Apache-2.0

#![no_main]
use derive_more::Debug;
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use libfuzzer_sys::fuzz_target;
use pretty_hex::PrettyHex as _;
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
    let mut depacketizer =
        retina::codec::Depacketizer::new("video", "jpeg", 90_000, None, None).unwrap();
    let mut timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();
    let mut sequence_number: u16 = 0;
    let pkt_ctx = retina::PacketContext::dummy();
    for pkt in pkts {
        if pkt.loss {
            sequence_number = sequence_number.wrapping_add(1);
        }
        if pkt.ts_change {
            timestamp = timestamp.try_add(1).unwrap();
        }
        let pkt = retina::rtp::ReceivedPacketBuilder {
            ctx: pkt_ctx,
            stream_id: 0,
            timestamp,
            ssrc: 0,
            sequence_number,
            loss: u16::from(pkt.loss),
            payload_type: 96,
            mark: pkt.mark,
        }
        .build(pkt.payload.iter().copied())
        .unwrap();
        log::trace!("pkt: {pkt:#?}");
        if depacketizer.push(pkt).is_err() {
            return;
        }
        while let Some(item) = depacketizer.pull() {
            if item.is_err() {
                return;
            }
        }
        sequence_number = sequence_number.wrapping_add(1);
    }
});
