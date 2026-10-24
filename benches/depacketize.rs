// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::num::NonZeroU16;

use criterion::{Criterion, criterion_group, criterion_main};
use retina::PacketContext;
use retina::buf::MarkBuf;
use retina::codec::{
    Accumulate, AudioDepacketizer, AudioFrameRef, AudioHandler, FrameFormat, VideoData,
    VideoDepacketizer, VideoFrameEnd, VideoFrameStart, VideoHandler,
};
use retina::rtp::ReceivedPacketRef;
use retina::rtp::{Receiver, ReceiverOptions};
use std::convert::TryFrom;
use std::io::Write;

/// Handles frames by calling `f` with each whole frame, either as accumulated by the
/// depacketizer or as assembled by the handler from streamed data.
struct BenchHandler<F> {
    accumulate: Accumulate,
    f: F,

    /// The frame so far, when streaming. Kept around to reuse the allocation.
    frame: Vec<u8>,
}

impl<F: FnMut(&[u8])> VideoHandler<PacketContext> for BenchHandler<F> {
    fn frame_start(&mut self, _: &mut VideoFrameStart<'_, PacketContext>) -> Accumulate {
        self.frame.clear();
        self.accumulate
    }

    fn data(&mut self, data: &VideoData<'_>) {
        if self.accumulate == Accumulate::No {
            if data.position.is_first() {
                self.frame.extend_from_slice(&[0, 0, 0, 1]); // Annex B start code.
            }
            for d in data.data {
                self.frame.extend_from_slice(d);
            }
        }
    }

    fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, PacketContext>) {
        if let Some(frame) = frame_end.complete_frame(FrameFormat::default()) {
            (self.f)(&frame);
        } else {
            (self.f)(&self.frame);
        }
    }
}

impl<F> AudioHandler<PacketContext> for BenchHandler<F> {
    fn audio_frame(&mut self, frame: &AudioFrameRef<'_, PacketContext>) {
        std::hint::black_box(frame.data(FrameFormat::default()));
    }
}

// This holds just the RTSP data portions of a session from this public endpoint.
// https://www.wowza.com/html/mobile.html
// Big Buck Bunny is (c) copyright 2008, Blender Foundation, licensed via
// Creative Commons Attribution 3.0. See https://peach.blender.org/about/
const BUNNY: &[u8] = include_bytes!("bunny.rtsp");

// TODO: it'd be nice to have a slick way of loading saved RTSP flows for testing.
// For now, this builds state via several internal interfaces.
fn h264_aac<F: FnMut(&[u8])>(accumulate: Accumulate, f: F) {
    let mut remaining = BUNNY;
    let opts = ReceiverOptions::default()
        .initial_rtptime(0)
        .initial_sequence_number(1);
    let mut rtps = [
        Receiver::new(12_000, opts.clone()).unwrap(),
        Receiver::new(90_000, opts).unwrap(),
    ];
    let mut audio = AudioDepacketizer::new("mpeg4-generic", 12_000, NonZeroU16::new(2), Some("profile-level-id=1;mode=AAC-hbr;sizelength=13;indexlength=3;indexdeltalength=3;config=1490")).unwrap();
    let mut video = VideoDepacketizer::new("h264", 90_000, Some("packetization-mode=1;profile-level-id=42C01E;sprop-parameter-sets=Z0LAHtkDxWhAAAADAEAAAAwDxYuS,aMuMsg==")).unwrap();
    let mut bufs = [MarkBuf::new(65536), MarkBuf::new(65536)];
    let mut handler = BenchHandler {
        accumulate,
        f,
        frame: Vec::new(),
    };
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
        let (header, payload_range) = retina::rtp::PacketHeader::validate(&data[..]).unwrap();
        let meta = rtps[stream_id].rtp(pkt_ctx, &header).unwrap().unwrap();
        let buf = &mut bufs[stream_id];
        let pos = buf.end();
        buf.extend(&data);
        buf.advance_unparsed(buf.end());
        let pkt = ReceivedPacketRef::new(
            meta,
            buf,
            pos + u64::from(payload_range.start),
            payload_range.end - payload_range.start,
        );
        match stream_id {
            0 => audio.push(&pkt, &mut handler),
            _ => video.push(&pkt, &mut handler),
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
        b.iter(|| h264_aac(Accumulate::Yes, |_| ()))
    });
    let mut w2 = w.try_clone().unwrap();
    g.bench_function("h264_aac_writevideo", move |b| {
        b.iter(|| h264_aac(Accumulate::Yes, |d| w.write_all(d).unwrap()))
    });
    g.bench_function("h264_aac_streamvideo", move |b| {
        b.iter(|| h264_aac(Accumulate::No, |d| w2.write_all(d).unwrap()))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
