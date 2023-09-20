#![no_main]
use lazy_static::lazy_static;
use libfuzzer_sys::fuzz_target;
use retina::Timestamp;
use std::{num::NonZeroU32, sync::Mutex};

lazy_static! {
    static ref DEPACKETIZER: Mutex<retina::codec::Depacketizer> =
        Mutex::new(retina::codec::Depacketizer::new("video", "jpeg", 90_000, None, None).unwrap());
}

fuzz_target!(|data: &[u8]| {
    let mut data = data;

    let conn_ctx = retina::ConnectionContext::dummy();
    let stream_ctx = retina::StreamContext::dummy();
    let pkt_ctx = retina::PacketContext::dummy();
    loop {
        let (hdr, rest) = match data.split_first() {
            Some(r) => r,
            None => return,
        };
        let mark = (hdr & 0b010) != 0;
        let loss = (hdr & 0b100) != 0;
        let len = usize::from(hdr >> 3);
        if rest.len() < len {
            return;
        }
        let (payload, rest) = rest.split_at(len);
        data = rest;

        let pkt = retina::rtp::ReceivedPacketBuilder {
            ctx: pkt_ctx,
            stream_id: 0,
            timestamp: Timestamp::new(0, NonZeroU32::new(96000).unwrap(), 0).unwrap(),
            ssrc: 0,
            sequence_number: 1,
            loss: u16::from(loss),
            payload_type: 96,
            mark,
        }
        .build(payload.iter().copied())
        .unwrap();
        //println!("pkt: {:#?}", pkt);
        if DEPACKETIZER.lock().unwrap().push(pkt).is_err() {
            return;
        }
        while let Some(item) = DEPACKETIZER
            .lock()
            .unwrap()
            .pull(&conn_ctx, &stream_ctx)
            .transpose()
        {
            if item.is_err() {
                return;
            }
        }
    }
});
