// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::num::NonZeroU16;

use criterion::{criterion_group, criterion_main, Criterion};
use retina::{
    client::{rtp::StrictSequenceChecker, Timeline},
    codec::Depacketizer,
};
use rtsp_types::Message;
use std::convert::TryFrom;

// This holds just the RTSP data portions of a session from this public endpoint.
// https://www.wowza.com/html/mobile.html
// Big Buck Bunny is (c) copyright 2008, Blender Foundation, licensed via
// Creative Commons Attribution 3.0. See https://peach.blender.org/about/
const BUNNY: &[u8] = include_bytes!("bunny.rtsp");

// TODO: it'd be nice to have a slick way of loading saved RTSP flows for testing.
// For now, this builds state via several internal interfaces.
fn h264_aac() {
    let mut remaining = BUNNY;
    let mut timelines = [
        Timeline::new(Some(0), 12_000, None).unwrap(),
        Timeline::new(Some(0), 90_000, None).unwrap(),
    ];
    let mut rtps = [
        StrictSequenceChecker::new(None, Some(1)),
        StrictSequenceChecker::new(None, Some(1)),
    ];
    let mut depacketizers = [
        Depacketizer::new("audio", "mpeg4-generic", 12_000, NonZeroU16::new(2), Some("profile-level-id=1;mode=AAC-hbr;sizelength=13;indexlength=3;indexdeltalength=3;config=1490")).unwrap(),
        Depacketizer::new("video", "h264", 90_000, None, Some("packetization-mode=1;profile-level-id=42C01E;sprop-parameter-sets=Z0LAHtkDxWhAAAADAEAAAAwDxYuS,aMuMsg==")).unwrap(),
    ];
    let ctx = retina::Context::dummy();
    while !remaining.is_empty() {
        let (msg, len): (Message<&[u8]>, _) = Message::parse(remaining).unwrap();
        let data = match msg {
            Message::Data(d) => d,
            _ => panic!("{:#?}", msg),
        };
        let stream_id = match data.channel_id() {
            0 => 0,
            2 => 1,
            1 | 3 => continue, // RTCP
            _ => unreachable!(),
        };
        let raw_pkt = bytes::Bytes::from_static(data.into_body());
        remaining = &remaining[len..];
        let pkt = match rtps[stream_id].rtp(ctx, &mut timelines[stream_id], stream_id, raw_pkt) {
            Ok(retina::client::PacketItem::RtpPacket(rtp)) => rtp,
            _ => unreachable!(),
        };
        depacketizers[stream_id].push(pkt).unwrap();
        while depacketizers[stream_id].pull().unwrap().is_some() {}
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut g = c.benchmark_group("depacketize");
    g.throughput(criterion::Throughput::Bytes(
        u64::try_from(BUNNY.len()).unwrap(),
    ))
    .bench_function("h264_aac", |b| b.iter(h264_aac));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
