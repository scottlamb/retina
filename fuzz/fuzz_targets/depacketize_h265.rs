// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

#![no_main]
use libfuzzer_sys::fuzz_target;
use std::num::NonZeroU32;

fuzz_target!(|data: &[u8]| {
    let mut data = data;
    let mut depacketizer = retina::codec::Depacketizer::new(
        "video", "h265", 90_000, None, Some("profile-id=1;sprop-sps=QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=;sprop-pps=RAHA8saNA7NA;sprop-vps=QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==")).unwrap();
    let mut timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();
    let mut sequence_number: u16 = 0;
    let pkt_ctx = retina::PacketContext::dummy();
    loop {
        let (hdr, rest) = match data.split_first() {
            Some(r) => r,
            None => return,
        };
        let ts_change = (hdr & 0b001) != 0;
        let mark = (hdr & 0b010) != 0;
        let loss = (hdr & 0b100) != 0;
        let len = usize::from(hdr >> 3);
        if rest.len() < len {
            return;
        }
        let (payload, rest) = rest.split_at(len);
        data = rest;
        if loss {
            sequence_number = sequence_number.wrapping_add(1);
        }
        if ts_change {
            timestamp = timestamp.try_add(1).unwrap();
        }
        let pkt = retina::rtp::ReceivedPacketBuilder {
            ctx: pkt_ctx,
            stream_id: 0,
            timestamp,
            ssrc: 0,
            sequence_number,
            loss: u16::from(loss),
            payload_type: 96,
            mark,
        }
        .build(payload.iter().copied())
        .unwrap();
        // println!("pkt: {:#?}", pkt);
        if let Err(_e) = depacketizer.push(pkt) {
            // println!("error: {_e}");
            depacketizer.check_invariants();
            return;
        }
        depacketizer.check_invariants();
        while let Some(item) = depacketizer.pull() {
            depacketizer.check_invariants();
            if item.is_err() {
                return;
            }
        }
        depacketizer.check_invariants();
        sequence_number = sequence_number.wrapping_add(1);
    }
});
