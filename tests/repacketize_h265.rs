// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! As in `repacketize.rs`, but for H.265. There's no H.265 capture handy, so
//! the upstream stream is synthetic: generated frames packetized with
//! `VideoPacketizer::push_frame`.

mod common;

use std::num::NonZeroU32;

use base64::Engine as _;
use common::{Collector, Feeder, Frame, Pkt, Recorder, Repacketize};
use retina::codec::{
    Accumulate, FrameInfo, Loss, PacketizeOptions, ParameterSetInsertion, VideoData,
    VideoDepacketizer, VideoFrameEnd, VideoFrameStart, VideoHandler, VideoPacketizer,
};
use retina::rtp::Sender;

const VPS: &str = "QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==";
const SPS: &str = "QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=";
const PPS: &str = "RAHA8saNA7NA";

fn fmtp() -> String {
    format!("sprop-vps={VPS};sprop-sps={SPS};sprop-pps={PPS}")
}

fn b64(s: &str) -> Vec<u8> {
    base64::engine::general_purpose::STANDARD.decode(s).unwrap()
}

/// Returns the H.265 NAL type of a NAL or payload header.
fn nal_type(hdr: &[u8]) -> u8 {
    hdr[0] >> 1 & 0b11_1111
}

/// Generates frames with a variety of NAL sizes: a random access point every
/// ten frames, some with a prefix SEI, and one to three slices each.
fn generated_frames() -> Vec<Frame> {
    let mut state = 0x1234_5678u32;
    let mut rand = move |n: u32| {
        state = state.wrapping_mul(1_103_515_245).wrapping_add(12_345);
        (state >> 8) % n
    };
    (0..30)
        .map(|i| {
            let is_random_access_point = i % 10 == 0;
            let mut nals = Vec::new();
            if rand(3) == 0 {
                let mut sei = vec![39 << 1, 0x01]; // PREFIX_SEI_NUT
                sei.extend((0..1 + rand(40)).map(|_| rand(256) as u8));
                nals.push(sei);
            }
            let slice_type = if is_random_access_point { 19 } else { 1 }; // IDR_W_RADL or TRAIL_R
            for s in 0..1 + rand(3) {
                let len = match rand(4) {
                    0 => 1 + rand(30),
                    _ => 1 + rand(4000),
                };
                let mut nal = vec![slice_type << 1, 0x01];
                nal.extend((0..len).map(|_| rand(256) as u8));

                // `first_slice_segment_in_pic_flag`.
                nal[2] = if s == 0 { nal[2] | 0x80 } else { nal[2] & 0x7f };
                nals.push(nal);
            }
            Frame {
                rtp_timestamp: i * 3000,
                is_random_access_point,
                nals,
            }
        })
        .collect()
}

/// Packetizes the generated frames as an upstream server would.
fn upstream_packets(frames: &[Frame]) -> Vec<Pkt> {
    let d = VideoDepacketizer::<()>::new("h265", 90_000, Some(&fmtp())).unwrap();
    let mut p = VideoPacketizer::new(d.parameters().unwrap(), PacketizeOptions::default()).unwrap();
    let mut sender = Sender::new(96, 1, 0, 0);
    let mut out = Vec::new();
    for f in frames {
        let mut data = Vec::new();
        for nal in &f.nals {
            data.extend_from_slice(&(nal.len() as u32).to_be_bytes());
            data.extend_from_slice(nal);
        }
        p.push_frame(
            FrameInfo::new(
                retina::Timestamp::new(
                    i64::from(f.rtp_timestamp),
                    NonZeroU32::new(90_000).unwrap(),
                    0,
                )
                .unwrap(),
            )
            .with_random_access_point(f.is_random_access_point),
            retina::codec::h26x::Framing::FourByteLength,
            &data,
            &mut Recorder::new(&mut sender, &mut out),
        )
        .unwrap();
    }
    out
}

fn repacketize(
    upstream: &[Pkt],
    options: PacketizeOptions,
    initial_seq: u16,
) -> (Vec<Pkt>, String) {
    let mut d = VideoDepacketizer::new("h265", 90_000, Some(&fmtp())).unwrap();
    let mut p = VideoPacketizer::new(d.parameters().unwrap(), options).unwrap();
    let fmtp = p.payload_format().fmtp().unwrap().to_owned();
    let mut sender = Sender::new(96, 0x1234_5678, initial_seq, 0);
    let mut out = Vec::new();
    let mut f = Feeder::new();
    for pkt in upstream {
        f.push(
            &pkt.raw,
            &mut d,
            &mut Repacketize {
                packetizer: &mut p,
                sink: Recorder::new(&mut sender, &mut out),
            },
        );
    }
    (out, fmtp)
}

/// The upstream stream depacketizes to the generated frames, and every
/// combination of options reproduces them exactly.
#[test]
fn round_trip() {
    let reference = generated_frames();
    let upstream = upstream_packets(&reference);
    let mut d = VideoDepacketizer::new("h265", 90_000, Some(&fmtp())).unwrap();
    let mut c = Collector::default();
    let mut f = Feeder::new();
    for pkt in &upstream {
        f.push(&pkt.raw, &mut d, &mut c);
    }
    assert_eq!(c.losses, 0);
    assert_eq!(c.frames, reference);

    let (vps_len, sps_len, pps_len) = (b64(VPS).len(), b64(SPS).len(), b64(PPS).len());
    for max_payload_size in [4, 5, 17, 100, 576, 1200, 1400, 1500, 65000] {
        for aggregate in [false, true] {
            for parameter_set_insertion in [
                ParameterSetInsertion::Never,
                ParameterSetInsertion::EachKeyFrame,
            ] {
                let options = PacketizeOptions::default()
                    .max_payload_size(max_payload_size)
                    .parameter_set_insertion(parameter_set_insertion)
                    .aggregate(aggregate);
                let ctx = format!("{options:?}");
                let (pkts, fmtp) = repacketize(&upstream, options, 65_500);
                let mut d = VideoDepacketizer::new("h265", 90_000, Some(&fmtp)).unwrap();
                let mut c = Collector::default();
                let mut f = Feeder::new();
                let mut saw_ap = false;
                let mut saw_fu = false;
                let mut next_frame_start = true;
                for pkt in &pkts {
                    let header = f.push(&pkt.raw, &mut d, &mut c);
                    let payload = &pkt.raw[12..];
                    assert!(payload.len() <= usize::from(max_payload_size), "{ctx}");
                    saw_ap |= nal_type(payload) == 48;
                    saw_fu |= nal_type(payload) == 49;
                    assert_eq!(pkt.frame_start, next_frame_start, "{ctx}");
                    next_frame_start = header.mark();
                    assert_eq!(pkt.sequence_number, header.sequence_number());
                }
                assert!(next_frame_start, "{ctx}: last packet should have mark");
                assert_eq!(c.losses, 0, "{ctx}");
                assert_eq!(saw_fu, max_payload_size < 4000, "{ctx}: FU usage");

                // An aggregation packet is used iff some frame has two
                // consecutive NALs (including inserted VPS, SPS, and PPS)
                // which fit in one.
                let expect_ap = aggregate
                    && reference.iter().any(|f| {
                        let mut lens: Vec<usize> = Vec::new();
                        if f.is_random_access_point
                            && parameter_set_insertion == ParameterSetInsertion::EachKeyFrame
                        {
                            lens.extend([vps_len, sps_len, pps_len]);
                        }
                        lens.extend(f.nals.iter().map(Vec::len));
                        lens.windows(2)
                            .any(|w| 2 + 2 + w[0] + 2 + w[1] <= usize::from(max_payload_size))
                    });
                assert_eq!(saw_ap, expect_ap, "{ctx}: aggregation packet usage");
                assert_eq!(c.frames.len(), reference.len(), "{ctx}");
                for (i, (a, b)) in c.frames.iter().zip(&reference).enumerate() {
                    assert_eq!(a, b, "{ctx}: frame {i}");
                }
            }
        }
    }
}

/// The repacketized stream is described by an fmtp equivalent to the original.
#[test]
fn payload_format() {
    let upstream = upstream_packets(&generated_frames());
    let (_, fmtp) = repacketize(&upstream, PacketizeOptions::default(), 0);
    assert_eq!(fmtp, self::fmtp());
}

/// With parameter set insertion, every key frame starts with VPS, SPS, and PPS,
/// so a receiver joining there needs no SDP.
#[test]
fn parameter_set_insertion() {
    let upstream = upstream_packets(&generated_frames());
    let (pkts, _) = repacketize(&upstream, PacketizeOptions::default(), 0);
    let rap_starts: Vec<_> = pkts
        .iter()
        .filter(|p| p.frame_start && p.random_access_point)
        .collect();
    assert!(!rap_starts.is_empty());
    for p in rap_starts {
        // An aggregation packet beginning with VPS, SPS, then PPS.
        let mut payload = &p.raw[12..];
        assert_eq!(nal_type(payload), 48);
        payload = &payload[2..];
        for expected in [32, 33, 34] {
            let len = usize::from(u16::from_be_bytes([payload[0], payload[1]]));
            assert_eq!(nal_type(&payload[2..]), expected);
            payload = &payload[2 + len..];
        }
    }

    // A receiver whose depacketizer has no parameters at all can start at any
    // random access point.
    let first_rap = pkts
        .iter()
        .rposition(|p| p.frame_start && p.random_access_point)
        .unwrap();
    let mut d = VideoDepacketizer::new("h265", 90_000, None).unwrap();
    let mut c = Collector::default();
    let mut f = Feeder::new();
    for pkt in &pkts[first_rap..] {
        f.push(&pkt.raw, &mut d, &mut c);
    }
    assert!(c.frames[0].is_random_access_point);
    assert!(d.parameters().is_some());
}

/// A proxy can fix up parameters by wrapping `Repacketize`; downstream sees
/// only the fixed parameters.
#[test]
fn parameter_fixup() {
    // Stand-ins for a rewritten VPS, SPS, and PPS.
    const FIXED_VPS: &str = "QAEMAf//AWAAAAMAkAAAAwAAAwA/LAwAAgAAAwAoAAIAAgACgA==";
    const FIXED_SPS: &str = "QgEBAWAAAAMAkAAAAwAAAwA/oAUCAXFlLkkyS7I=";
    const FIXED_PPS: &str = "RAHA8vAzJA==";

    struct Fixup<'a, S> {
        inner: Repacketize<'a, S>,
        fixed: bool,
    }
    impl<S: retina::codec::PayloadSink> VideoHandler<()> for Fixup<'_, S> {
        fn frame_start(&mut self, fs: &mut VideoFrameStart<'_, ()>) -> Accumulate {
            if !self.fixed {
                fs.set_h265_parameters(&b64(FIXED_VPS), &b64(FIXED_SPS), &b64(FIXED_PPS))
                    .unwrap();
                self.fixed = true;
            }
            self.inner.frame_start(fs)
        }
        fn data(&mut self, data: &VideoData<'_>) {
            VideoHandler::<()>::data(&mut self.inner, data)
        }
        fn frame_end(&mut self, fe: &mut VideoFrameEnd<'_, ()>) {
            self.inner.frame_end(fe)
        }
        fn loss(&mut self, loss: &Loss<'_, ()>) {
            VideoHandler::<()>::loss(&mut self.inner, loss)
        }
    }

    // The upstream stream carries the original parameters in band at each
    // random access point; repeats of them don't undo the fixup.
    let upstream = upstream_packets(&generated_frames());
    let mut d = VideoDepacketizer::new("h265", 90_000, Some(&fmtp())).unwrap();
    let mut p = VideoPacketizer::new(d.parameters().unwrap(), PacketizeOptions::default()).unwrap();
    let mut sender = Sender::new(96, 1, 0, 0);
    let mut out = Vec::new();
    let mut f = Feeder::new();
    let mut fixup_fixed = false;
    for pkt in &upstream {
        let mut h = Fixup {
            inner: Repacketize {
                packetizer: &mut p,
                sink: Recorder::new(&mut sender, &mut out),
            },
            fixed: fixup_fixed,
        };
        f.push(&pkt.raw, &mut d, &mut h);
        fixup_fixed = h.fixed;
    }

    let fixed_fmtp = format!("sprop-vps={FIXED_VPS};sprop-sps={FIXED_SPS};sprop-pps={FIXED_PPS}");
    assert_eq!(p.payload_format().fmtp().unwrap().to_owned(), fixed_fmtp);
    assert_eq!(d.parameters(), Some(p.parameters()));

    // Every key frame downstream carries the fixed parameters, not the originals.
    let fixed_vps = b64(FIXED_VPS);
    let mut raps = 0;
    for pkt in out
        .iter()
        .filter(|p| p.frame_start && p.random_access_point)
    {
        let payload = &pkt.raw[12..];
        assert_eq!(nal_type(payload), 48);
        assert_eq!(&payload[4..4 + fixed_vps.len()], &fixed_vps[..]);
        raps += 1;
    }
    assert!(raps > 1);
}

/// A sink which is congested as the test says.
struct Throttled {
    sender: Sender,
    out: Vec<Pkt>,
    congested: bool,
}

impl retina::codec::PayloadSink for Throttled {
    fn payload(&mut self, payload: &retina::codec::Payload<'_>) {
        let pkt = self
            .sender
            .packet(payload.timestamp(), payload.mark(), payload.data());
        self.out.push(Pkt::new(payload, &pkt));
    }

    fn discontinuity(&mut self) {
        self.sender.skip();
    }

    fn congested(&self) -> bool {
        self.congested
    }
}

/// Throttling a congested sink damages at most one frame, marked so the
/// receiver knows which, without sequence number gaps; the receiver resumes at
/// the next random access point with frames identical to the originals.
#[test]
fn throttle() {
    let reference = generated_frames();
    let upstream = upstream_packets(&reference);

    // Congestion must end before the last random access point, so the
    // receiver has somewhere to resume.
    let last_rap = upstream
        .iter()
        .rposition(|p| p.frame_start && p.random_access_point)
        .unwrap();
    let mut saw_truncation = false;
    let mut saw_clean_drop = false;
    for start in 0..last_rap - 3 {
        let ctx = format!("congested from upstream packet {start}");
        let mut d = VideoDepacketizer::new("h265", 90_000, Some(&fmtp())).unwrap();
        let options = PacketizeOptions::default().max_payload_size(500);
        let mut p = VideoPacketizer::new(d.parameters().unwrap(), options).unwrap();
        let mut sink = Throttled {
            sender: Sender::new(96, 1, 0, 0),
            out: Vec::new(),
            congested: false,
        };
        let mut f = Feeder::new();
        for (i, pkt) in upstream.iter().enumerate() {
            sink.congested = (start..start + 3).contains(&i);
            f.push(
                &pkt.raw,
                &mut d,
                &mut Repacketize {
                    packetizer: &mut p,
                    sink: &mut sink,
                },
            );
        }
        let truncated = sink.out.iter().filter(|p| p.raw[12] & 0x80 != 0).count();
        assert!(truncated <= 1, "{ctx}");

        let mut d = VideoDepacketizer::new("h265", 90_000, Some(&fmtp())).unwrap();
        let mut c = Collector::default();
        let mut f = Feeder::new();
        for (i, pkt) in sink.out.iter().enumerate() {
            assert_eq!(pkt.sequence_number, i as u16, "{ctx}");
            f.push(&pkt.raw, &mut d, &mut c);
        }
        assert_eq!(c.corrupt, truncated, "{ctx}");
        assert_eq!(c.losses, c.corrupt, "{ctx}: no packet loss");

        // Every frame received matches the original, and they're a prefix
        // and a suffix starting at a random access point.
        let mut ref_iter = reference.iter().peekable();
        let mut skipped = false;
        for frame in &c.frames {
            let mut this_skipped = false;
            while ref_iter
                .peek()
                .is_some_and(|r| r.rtp_timestamp != frame.rtp_timestamp)
            {
                ref_iter.next();
                this_skipped = true;
            }
            if this_skipped {
                assert!(!skipped, "{ctx}: one gap only");
                assert!(frame.is_random_access_point, "{ctx}: resumes at a RAP");
                skipped = true;
            }
            assert_eq!(Some(frame), ref_iter.next(), "{ctx}");
        }
        assert!(
            skipped,
            "{ctx}: something was dropped; {} packets, {} frames, first ts {:?}",
            sink.out.len(),
            c.frames.len(),
            c.frames.first().map(|f| f.rtp_timestamp)
        );
        saw_truncation |= truncated == 1;
        saw_clean_drop |= truncated == 0;
    }
    assert!(saw_truncation && saw_clean_drop);
}
