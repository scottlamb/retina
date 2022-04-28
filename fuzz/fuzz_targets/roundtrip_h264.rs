// Copyright (C) 2022 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Tests a roundtrip through the H.264 packetizer and depacketizer with an arbitrary
//! input packet size and frame. Ensures the following:
//! *   there are no crashes.
//! *   the round trip produces an error, nothing (see note about `can_end_au`), or identical data.

#![no_main]
use bytes::Bytes;
use libfuzzer_sys::fuzz_target;
use std::num::NonZeroU32;

fuzz_target!(|data: &[u8]| {
    if data.len() < 2 {
        return;
    }
    let conn_ctx = retina::ConnectionContext::dummy();
    let max_payload_size = u16::from_be_bytes([data[0], data[1]]);
    let mut p = match retina::codec::h264::Packetizer::new(max_payload_size, 0, 0) {
        Ok(p) => p,
        Err(_) => return,
    };
    let mut d = retina::codec::Depacketizer::new(
        "video",
        "h264",
        90_000,
        None,
        Some("packetization-mode=1;sprop-parameter-sets=J01AHqkYGwe83gDUBAQG2wrXvfAQ,KN4JXGM4"),
    )
    .unwrap();
    let timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();
    if p.push(timestamp, Bytes::copy_from_slice(&data[2..]))
        .is_err()
    {
        return;
    }
    let frame = loop {
        match p.pull() {
            Ok(Some(pkt)) => {
                let mark = pkt.mark;
                if d.push(pkt).is_err() {
                    return;
                }
                match d.pull(&conn_ctx) {
                    Err(_) => return,
                    Ok(Some(retina::codec::CodecItem::VideoFrame(f))) => {
                        assert!(mark);
                        break f;
                    }
                    Ok(Some(_)) => panic!(),
                    Ok(None) => {
                        // XXX: assert!(!mark)
                        //
                        // One would expect that a frame would be produced if the packet has mark
                        // set. This used to be true, but Retina now has a workaround for some
                        // RTSP servers that spuriously set the mark bit. See
                        // `retina::codec::h264::can_end_au`. In this case, just exit.
                        if mark {
                            assert!(matches!(p.pull(), Ok(None)));
                            return;
                        }
                    }
                }
            }
            Ok(None) => panic!("packetizer ran out of packets before depacketizer produced frame"),
            Err(_) => return,
        }
    };
    assert_eq!(&data[2..], &frame.data()[..]);
    assert!(matches!(d.pull(&conn_ctx), Ok(None)));
    assert!(matches!(p.pull(), Ok(None)));
});
