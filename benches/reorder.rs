// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Benchmarks [`Reorderer`] holding many packets at once.

use std::time::{Duration, Instant};

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use retina::buf::MarkBuf;
use retina::rtp::{PacketHeader, ReorderOptions, Reorderer};

const PAYLOAD_LEN: usize = 1400;

/// Packets in each benchmark iteration.
const PACKETS: u16 = 4096;

/// Builds a minimal RTP packet with the given sequence number.
fn raw_rtp(seq: u16) -> Vec<u8> {
    let mut raw = vec![0; 12 + PAYLOAD_LEN];
    raw[0] = 2 << 6; // version 2.
    raw[1] = 96; // payload type.
    raw[2..4].copy_from_slice(&seq.to_be_bytes());
    raw
}

/// Pushes packets with the given sequence numbers, in order, through a fresh
/// `Reorderer`, popping all due packets after each push.
fn run(options: ReorderOptions, packets: &[(Vec<u8>, PacketHeader)]) {
    let mut buf = MarkBuf::new(1 << 16);
    let mut r = Reorderer::new(options);

    // Nothing waits long enough to time out.
    let now = Instant::now();
    for (raw, header) in packets {
        let pos = buf.end();
        buf.extend(raw);
        buf.advance_unparsed(buf.end());
        std::hint::black_box(r.push(&buf, *header, pos, now, ()));
        while let Some(p) = r.pop(&buf, now) {
            std::hint::black_box(p.pin_pos);
        }
    }
}

fn prepare(seqs: impl Iterator<Item = u16>) -> Vec<(Vec<u8>, PacketHeader)> {
    seqs.map(|seq| {
        let raw = raw_rtp(seq);
        let (header, _) = PacketHeader::validate(&raw[..]).unwrap();
        (raw, header)
    })
    .collect()
}

fn options(max_packets: u16) -> ReorderOptions {
    ReorderOptions::default()
        .initial_sequence_number(0)
        .max_delay(Duration::from_secs(3600))
        .max_packets(max_packets)
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut g = c.benchmark_group("reorder");
    g.throughput(Throughput::Elements(u64::from(PACKETS)));

    // Every packet arrives in order; nothing is held past its `pop`.
    let packets = prepare(0..PACKETS);
    g.bench_function("in_order", |b| b.iter(|| run(options(128), &packets)));

    for held in [16, 128, 1024] {
        // One packet in every `held + 1` is lost. The reorderer holds the
        // `held` packets after it until exceeding `max_packets`, then returns
        // them in arrival order.
        let packets = prepare((0..PACKETS).filter(|s| s % (held + 1) != 0));
        g.bench_with_input(BenchmarkId::new("loss", held), &held, |b, &held| {
            b.iter(|| run(options(held - 1), &packets))
        });

        // Each block of `held` packets arrives in reverse order. The
        // reorderer holds all but the last packet to arrive, then returns
        // them in reverse arrival order.
        let packets = prepare((0..PACKETS).map(|s| {
            let block = s - s % held;
            block + held - 1 - s % held
        }));
        g.bench_with_input(BenchmarkId::new("reversed", held), &held, |b, &held| {
            b.iter(|| run(options(held), &packets))
        });

        // Each block of `held` packets arrives odd sequence numbers first,
        // ascending, then even, descending. The even packets go between the
        // odd ones held, mostly away from either end.
        let packets = prepare((0..PACKETS).map(|s| {
            let block = s - s % held;
            let i = s % held;
            let half = held / 2;
            block
                + if i < half {
                    2 * i + 1
                } else {
                    2 * (held - 1 - i)
                }
        }));
        g.bench_with_input(BenchmarkId::new("interleaved", held), &held, |b, &held| {
            b.iter(|| run(options(held), &packets))
        });
    }
    g.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(20);
    targets = criterion_benchmark
}
criterion_main!(benches);
