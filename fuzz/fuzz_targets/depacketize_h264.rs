// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

#![no_main]
use bytes::{Buf, Bytes};
use libfuzzer_sys::fuzz_target;
use std::num::NonZeroU32;

fuzz_target!(|data: &[u8]| {
    let mut data = Bytes::copy_from_slice(data);
    let mut depacketizer = retina::codec::Depacketizer::new(
        "video", "h264", 90_000, None, Some("packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA")).unwrap();
    let mut timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();
    let mut sequence_number: u16 = 0;
    let conn_ctx = retina::ConnectionContext::dummy();
    let pkt_ctx = retina::PacketContext::dummy();
    while data.has_remaining() {
        let hdr = data.get_u8();
        let ts_change = (hdr & 0b001) != 0;
        let mark = (hdr & 0b010) != 0;
        let loss = (hdr & 0b100) != 0;
        let len = usize::from(hdr >> 3);
        if len > data.remaining() {
            return;
        }
        if loss {
            sequence_number = sequence_number.wrapping_add(1);
        }
        if ts_change {
            timestamp = timestamp.try_add(1).unwrap();
        }
        let pkt = retina::client::rtp::Packet {
            ctx: pkt_ctx,
            stream_id: 0,
            timestamp,
            ssrc: 0,
            sequence_number,
            loss: u16::from(loss),
            mark,
            payload: data.split_off(usize::from(len)),
        };
        //println!("pkt: {:#?}", pkt);
        if depacketizer.push(pkt).is_err() {
            return;
        }
        while let Some(item) = depacketizer.pull(&conn_ctx).transpose() {
            if item.is_err() {
                return;
            }
        }
        sequence_number = sequence_number.wrapping_add(1);
    }
});
