// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! As in `roundtrip_h264`, tests that decode(encode(max_payload_size, frame))
//! == frame with an arbitrary max_payload_size, for H.265.

#![no_main]
use derive_more::Debug;
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use libfuzzer_sys::{Corpus, fuzz_target};
use pretty_hex::PrettyHex as _;
use std::num::NonZeroU32;

#[derive(Arbitrary, Debug)]
struct Input<'i> {
    max_payload_size: u16,
    aggregate: bool,
    #[debug("{:?}", data.hex_conf(retina::testutil::NONASCII_HEX_CONFIG))]
    data: &'i [u8],
}

fuzz_target!(|input: Input<'_>| -> Corpus {
    // An empty frame produces no packets. Require validly length-prefixed NALs.
    if input.data.is_empty() {
        return Corpus::Reject;
    }
    let mut nals = Vec::new();
    {
        let mut remaining = input.data;
        while !remaining.is_empty() {
            let Some((len_bytes, rest)) = remaining.split_first_chunk::<4>() else {
                return Corpus::Reject;
            };
            let len = u32::from_be_bytes(*len_bytes) as usize;
            let Some((nal, rest)) = rest.split_at_checked(len) else {
                return Corpus::Reject;
            };
            if nal.is_empty() {
                return Corpus::Reject;
            }
            nals.push(nal);
            remaining = rest;
        }
    }

    // The depacketizer always strips inline VPS/SPS/PPS NALs (they're managed
    // via ParameterSetInsertion). Reject inputs containing them since they
    // can't round-trip exactly.
    if nals
        .iter()
        .any(|n| matches!(n[0] >> 1 & 0b11_1111, 32..=34))
    {
        return Corpus::Reject;
    }

    // Truncated headers, the F bit, types 48–63, and a zero TID are invalid;
    // the packetizer must reject frames containing them.
    let expect_err = nals.iter().any(|n| {
        n.len() < 2 || n[0] & 0x80 != 0 || n[0] >> 1 & 0b11_1111 >= 48 || n[1] & 0b111 == 0
    });

    let mut d = retina::codec::VideoDepacketizer::<u64>::new(
        "h265",
        90_000,
        Some("sprop-vps=QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==;sprop-sps=QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=;sprop-pps=RAHA8saNA7NA"),
    )
    .unwrap();
    // Smaller limits can't make progress with fragments; the packetizer
    // exceeds them.
    if input.max_payload_size < 4 {
        return Corpus::Reject;
    }
    let mut p = match retina::codec::VideoPacketizer::new(
        d.parameters().unwrap(),
        retina::codec::VideoPacketizerOptions::default()
            .parameter_set_insertion(retina::codec::ParameterSetInsertion::Never)
            .aggregate(input.aggregate),
    ) {
        Ok(p) => p,
        Err(_) => return Corpus::Reject,
    };
    // The packetizer doesn't insert parameter sets; `CheckingHandler` uses
    // `FrameFormat::MP4`, which doesn't either.
    let mut h = retina_fuzz::CheckingHandler::new(retina::codec::Accumulate::Yes, true);
    let timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();
    let mut buf = retina::buf::MarkBuf::new(65536);

    let mut sender = retina::rtp::Sender::new(
        96,
        retina::rtp::SenderOptions::default()
            .ssrc(0)
            .initial_sequence_number(0)
            .timestamp_offset(0)
            .max_payload_size(input.max_payload_size),
    );
    let mut pkts = Vec::new();
    let r = p.push_frame(
        retina::codec::VideoFrameInfo::new(timestamp),
        retina::codec::FrameFormat::MP4,
        input.data,
        &mut sender.sink(|pkt| pkts.push(pkt.to_vec())),
    );
    if expect_err {
        assert!(r.is_err(), "packetizer should reject invalid NALs");
        assert!(pkts.is_empty(), "rejected frame should produce no packets");
        return Corpus::Keep;
    }
    r.expect("packetizer should accept valid frame");
    let mut pkts = pkts.into_iter();
    let frame = loop {
        let Some(pkt) = pkts.next() else {
            panic!("packetizer ran out of packets before depacketizer produced frame");
        };
        assert!(pkt.len() <= 12 + usize::from(input.max_payload_size));

        // Recover the metadata from the header, which also checks header
        // parsing in the round trip.
        let retina::rtp::ValidatedPacket {
            header, payload, ..
        } = retina::rtp::PacketHeader::validate(&pkt[..])
            .expect("packetizer should produce valid RTP packets");
        let mark = header.mark();
        let meta = retina::rtp::ReceivedPacketMeta::new(
            0,
            retina::Timestamp::new(i64::from(header.timestamp()), timestamp.clock_rate(), 0)
                .unwrap(),
            header.sequence_number(),
            header.ssrc(),
            mark,
            retina::rtp::Continuity::Contiguous,
        );
        let payload = &pkt[usize::from(payload.start)..usize::from(payload.end)];
        retina_fuzz::push(&mut buf, meta, payload, &mut [(&mut d, &mut h)]);
        if h.events
            .iter()
            .any(|e| matches!(e, retina_fuzz::Event::Loss(_)))
        {
            return Corpus::Keep;
        }
        if let Some(f) = h.frames.pop() {
            assert!(mark);
            break f;
        }
        // As in `roundtrip_h264`, the depacketizer may not end an access unit
        // at a marked packet; see `retina::codec::h265::can_end_au`. In this
        // case, just exit.
        if mark {
            assert!(pkts.next().is_none());
            return Corpus::Keep;
        }
    };
    assert_eq!(input.data, &frame[..]);
    assert!(pkts.next().is_none());
    Corpus::Keep
});
