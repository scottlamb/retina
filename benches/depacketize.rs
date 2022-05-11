// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::num::NonZeroU16;

use criterion::{criterion_group, criterion_main, Criterion};
use retina::client::{rtp::InorderParser, Timeline};
use retina::codec::{CodecItem, Depacketizer};
use std::convert::TryFrom;
use std::io::Write;

// This holds just the RTSP data portions of a session from this public endpoint.
// https://www.wowza.com/html/mobile.html
// Big Buck Bunny is (c) copyright 2008, Blender Foundation, licensed via
// Creative Commons Attribution 3.0. See https://peach.blender.org/about/
const BUNNY: &[u8] = include_bytes!("bunny.rtsp");

// TODO: it'd be nice to have a slick way of loading saved RTSP flows for testing.
// For now, this builds state via several internal interfaces.
fn h264_aac<F: FnMut(CodecItem) -> ()>(mut f: F) {
    let mut remaining = BUNNY;
    let mut timelines = [
        Timeline::new(Some(0), 12_000, None).unwrap(),
        Timeline::new(Some(0), 90_000, None).unwrap(),
    ];
    let mut rtps = [
        InorderParser::new(None, Some(1)),
        InorderParser::new(None, Some(1)),
    ];
    let mut depacketizers = [
        Depacketizer::new("audio", "mpeg4-generic", 12_000, NonZeroU16::new(2), Some("profile-level-id=1;mode=AAC-hbr;sizelength=13;indexlength=3;indexdeltalength=3;config=1490")).unwrap(),
        Depacketizer::new("video", "h264", 90_000, None, Some("packetization-mode=1;profile-level-id=42C01E;sprop-parameter-sets=Z0LAHtkDxWhAAAADAEAAAAwDxYuS,aMuMsg==")).unwrap(),
    ];
    let conn_ctx = retina::ConnectionContext::dummy();
    let stream_ctx = retina::StreamContext::dummy();
    let pkt_ctx = retina::PacketContext::dummy();
    while !remaining.is_empty() {
        assert!(remaining.len() > 4);
        assert_eq!(remaining[0], b'$');
        let channel_id = remaining[1];
        let len = u16::from_be_bytes([remaining[2], remaining[3]]);
        let (data, after) = remaining.split_at(4 + usize::from(len));
        let data = bytes::Bytes::from_static(&data[4..]);
        remaining = after;
        let stream_id = match channel_id {
            0 => 0,
            2 => 1,
            1 | 3 => continue, // RTCP
            _ => unreachable!(),
        };
        let pkt = match rtps[stream_id].rtp(
            &retina::client::SessionOptions::default(),
            &stream_ctx,
            None,
            &conn_ctx,
            &pkt_ctx,
            &mut timelines[stream_id],
            stream_id,
            data,
        ) {
            Ok(Some(retina::client::PacketItem::Rtp(rtp))) => rtp,
            _ => unreachable!(),
        };
        depacketizers[stream_id].push(pkt).unwrap();
        while let Some(pkt) = depacketizers[stream_id]
            .pull(&conn_ctx, &stream_ctx)
            .unwrap()
        {
            f(pkt);
        }
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut g = c.benchmark_group("depacketize");
    let mut w = std::fs::OpenOptions::new()
        .write(true)
        .open("/dev/null")
        .unwrap();
    let w = &mut w;
    g.throughput(criterion::Throughput::Bytes(
        u64::try_from(BUNNY.len()).unwrap(),
    ));
    g.bench_function("h264_aac_discard", |b| {
        b.iter(|| h264_aac(|_pkt: CodecItem| ()))
    });
    g.bench_function("h264_aac_writevideo", move |b| {
        b.iter(|| {
            h264_aac(|pkt: CodecItem| {
                let v = match pkt {
                    CodecItem::VideoFrame(v) => v,
                    _ => return,
                };
                w.write_all(&v.data()[..]).unwrap();
            })
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
