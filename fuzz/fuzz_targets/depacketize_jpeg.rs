#![no_main]
use libfuzzer_sys::fuzz_target;
use std::num::NonZeroU32;

fuzz_target!(|data: &[u8]| {
    let mut data = data;
    let mut depacketizer =
        retina::codec::Depacketizer::new("video", "jpeg", 90_000, None, None).unwrap();
    let mut timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();
    let mut sequence_number: u16 = 0;
    let conn_ctx = retina::ConnectionContext::dummy();
    let stream_ctx = retina::StreamContext::dummy();
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
        //println!("pkt: {:#?}", pkt);
        if depacketizer.push(pkt).is_err() {
            return;
        }
        while let Some(item) = depacketizer.pull(&conn_ctx, &stream_ctx).transpose() {
            if item.is_err() {
                return;
            }
        }
        sequence_number = sequence_number.wrapping_add(1);
    }
});
