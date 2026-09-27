// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Tests client performance against a mock server.

use std::{io::ErrorKind, net::SocketAddr, num::NonZeroU32};

use bytes::Bytes;
use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use retina::PacketContext;
use retina::client::{PlayOptions, PlayingItem, SetupOptions};
use retina::codec::{
    Accumulate, Depacketizer, FrameFormat, VideoFrameEnd, VideoFrameStart, VideoHandler,
};
use std::convert::TryFrom;
use tokio::io::AsyncWriteExt;
use url::Url;

/// Mock server. Serves `data` on every connection.
async fn serve(data: Bytes) -> SocketAddr {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    tokio::task::spawn(async move {
        loop {
            let conn = match listener.accept().await {
                Err(_) => return,
                Ok((conn, _addr)) => conn,
            };
            tokio::task::spawn(serve_connection(conn, data.clone()));
        }
    });
    addr
}

/// Mock server connection handler.
///
/// Tries to send the canned data. Doesn't even try to read any data from the
/// client until the end. This assumes the total data written from client fits
/// within the socket buffer; it might cause deadlock otherwise.
async fn serve_connection(mut stream: tokio::net::TcpStream, data: Bytes) {
    // Send.
    if stream.write_all(&data[..]).await.is_err() {
        return;
    }

    // Wait until the client has read it all and closes the connection.
    // This reads and discards whatever the client sent earlier.
    if stream.shutdown().await.is_err() {
        return;
    }
    loop {
        if stream.readable().await.is_err() {
            return;
        }
        let mut buf = [0u8; 1024];
        match stream.try_read(&mut buf) {
            Err(e) if e.kind() == ErrorKind::WouldBlock => {}
            Err(_) | Ok(0) => return,
            Ok(_) => {}
        }
    }
}

fn make_test_data(max_payload_size: u16) -> Bytes {
    let mut data = Vec::new();
    data.extend_from_slice(include_bytes!(
        "../src/client/testdata/hikvision_describe.txt"
    ));
    data.extend_from_slice(include_bytes!("../src/client/testdata/hikvision_setup.txt"));
    data.extend_from_slice(include_bytes!("../src/client/testdata/hikvision_play.txt"));

    // These are the actual sizes of the slice NALs in one (two-second, 60-frame) Group of Pictures
    // from a Dahua IP camera. This is about 3.5 Mbps.
    let frame_sizes: [u32; 60] = [
        667339, 7960, 2296, 3153, 3687, 3246, 3621, 2300, 2603, 2956, 2888, 3187, 3439, 3299, 3252,
        3372, 3052, 2988, 2921, 2859, 2806, 3400, 2811, 3143, 2972, 4097, 2906, 3307, 3628, 3750,
        3575, 3144, 3431, 3317, 3154, 3387, 3630, 3232, 3574, 3254, 4198, 4235, 4898, 4890, 4854,
        4854, 4863, 4652, 4227, 4101, 3867, 3870, 3716, 3074, 3253, 3267, 3192, 3995, 3904, 3781,
    ];
    let mut dummy_frame = vec![1; 1048576];
    dummy_frame[4] = h264_reader::nal::UnitType::SliceLayerWithoutPartitioningIdr.id();
    let parameters = retina::codec::VideoDepacketizer::<()>::new(
        "h264",
        90_000,
        Some("sprop-parameter-sets=Z00AKZpkA8ARPyzUBAQFAAADA+gAAOpgBA==,aO48gA=="),
    )
    .unwrap()
    .parameters()
    .unwrap()
    .clone();
    let mut p = retina::codec::VideoPacketizer::new(
        &parameters,
        retina::codec::PacketizeOptions::default()
            .max_payload_size(max_payload_size)
            .parameter_set_insertion(retina::codec::ParameterSetInsertion::Never)
            .aggregate(false),
    )
    .unwrap();
    let mut sender = retina::rtp::Sender::new(96, 0x4cacc3d1, 24104, 0);
    let mut timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();
    for _ in 0..30 {
        for &f in &frame_sizes {
            dummy_frame[0..4].copy_from_slice(&f.to_be_bytes()[..]);
            let frame = &dummy_frame[..(usize::try_from(f).unwrap() + 4)];
            p.push_frame(
                retina::codec::FrameInfo::new(timestamp).with_random_access_point(true),
                retina::codec::h26x::Framing::FourByteLength,
                frame,
                &mut sender.sink(|pkt| {
                    data.push(b'$'); // interleaved data
                    data.push(0); // channel 0
                    data.extend_from_slice(&u16::try_from(pkt.len()).unwrap().to_be_bytes()[..]);
                    pkt.write_to(&mut data);
                }),
            )
            .unwrap();
            timestamp = timestamp.try_add(3000).unwrap();
        }
    }
    Bytes::from(data)
}

/// Counts frames, accumulating each as an owned `Vec<u8>`.
struct Counter(usize);

impl VideoHandler<PacketContext> for Counter {
    fn frame_start(&mut self, _frame_start: &mut VideoFrameStart<'_, PacketContext>) -> Accumulate {
        Accumulate::Yes
    }

    fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, PacketContext>) {
        std::hint::black_box(frame_end.complete_frame(FrameFormat::MP4).unwrap());
        self.0 += 1;
    }

    fn loss(&mut self, loss: &retina::codec::Loss<'_, PacketContext>) {
        panic!("unexpected loss: {:?}", loss.reason());
    }
}

async fn read_to_eof(addr: SocketAddr) {
    let url = Url::parse(&format!("rtsp://{}/", addr)).unwrap();
    let mut session =
        retina::client::Session::describe(url, retina::client::SessionOptions::default())
            .await
            .unwrap();
    session.setup(0, SetupOptions::default()).await.unwrap();
    let Ok(Depacketizer::Video(mut depacketizer)) = session.streams()[0].new_depacketizer() else {
        panic!("expected a video depacketizer");
    };
    let mut session = session.play(PlayOptions::default()).await.unwrap();
    let mut counter = Counter(0);
    while let Some(item) = session.next_item().await {
        match item {
            Ok(PlayingItem::Rtp(pkt)) => depacketizer.push(pkt.packet(), &mut counter),
            o => panic!("bad item: {o:#?}"),
        }
    }
    assert_eq!(counter.0, 30 * 60);
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut g = c.benchmark_group("client");
    let rt = tokio::runtime::Runtime::new().unwrap();
    let data = make_test_data(1440);
    g.throughput(Throughput::Bytes(u64::try_from(data.len()).unwrap()));
    let addr = rt.block_on(serve(data));
    g.bench_function("h264", |b| b.to_async(&rt).iter(|| read_to_eof(addr)));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
