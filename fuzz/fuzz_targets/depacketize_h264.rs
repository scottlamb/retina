// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

#![no_main]
use derive_more::Debug;
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use libfuzzer_sys::{Corpus, fuzz_target};
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

fuzz_target!(|pkts: Vec<Pkt<'_>>| -> Corpus {
    retina_fuzz::init_logging();
    if pkts.first().is_none_or(|p| p.ts_change) {
        return Corpus::Reject;
    }
    let mut depacketizer = retina::codec::Depacketizer::new(
        "video", "h264", 90_000, None, Some("packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA")).unwrap();
    let mut timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();
    let mut sequence_number: u16 = 0;
    let pkt_ctx = retina::PacketContext::dummy();
    for pkt in pkts {
        log::trace!("pkt: {pkt:?}");
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
        if let Err(e) = depacketizer.push(pkt) {
            log::info!("depacketizer push error: {e:?}");
            depacketizer.check_invariants();
            return Corpus::Keep;
        }
        depacketizer.check_invariants();
        while let Some(item) = depacketizer.pull() {
            depacketizer.check_invariants();
            match item {
                Ok(retina::codec::CodecItem::VideoFrame(f)) => {
                    retina::testutil::validate_avcc_frame(f.data()).unwrap();
                }
                Ok(_) => unreachable!(),
                Err(e) => {
                    log::info!("depacketizer pull error: {e:?}");
                    return Corpus::Keep;
                }
            }
        }
        depacketizer.check_invariants();
        sequence_number = sequence_number.wrapping_add(1);
    }
    Corpus::Keep
});
