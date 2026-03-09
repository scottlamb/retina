// Copyright (C) The Retina Authors
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
    let mut depacketizer = retina::codec::Depacketizer::new(
        "video", "h265", 90_000, None, Some("profile-id=1;sprop-sps=QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=;sprop-pps=RAHA8saNA7NA;sprop-vps=QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==")).unwrap();
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
        log::trace!("pkt: {:#?}", pkt);
        if let Err(e) = depacketizer.push(pkt) {
            log::info!("depacketizer push error: {e}");
            depacketizer.check_invariants();
            return;
        }
        depacketizer.check_invariants();
        while let Some(item) = depacketizer.pull() {
            depacketizer.check_invariants();
            if let Err(e) = item {
                log::info!("depacketizer pull error: {e:?}");
                return;
            }
        }
        depacketizer.check_invariants();
        sequence_number = sequence_number.wrapping_add(1);
    }
});
