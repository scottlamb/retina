// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Round trip through the send side, using only the public API:
//! depacketize a real capture, repacketize it at various payload sizes, then
//! depacketize the result and check it matches.

mod common;

use common::{Collector, Feeder, Frame, Pkt, Recorder, Repacketize, rtp};
use retina::codec::{
    Accumulate, Loss, ParameterSetInsertion, VideoData, VideoDepacketizer, VideoFrameEnd,
    VideoFrameStart, VideoHandler, VideoPacketizer, VideoPacketizerOptions, VideoParameters,
};
use retina::rtp::{Sender, SenderOptions};

// See `benches/depacketize.rs`. Big Buck Bunny is (c) copyright 2008, Blender
// Foundation, licensed via Creative Commons Attribution 3.0.
const BUNNY: &[u8] = include_bytes!("../benches/bunny.rtsp");
const BUNNY_FMTP: &str = "packetization-mode=1;profile-level-id=42C01E;sprop-parameter-sets=Z0LAHtkDxWhAAAADAEAAAAwDxYuS,aMuMsg==";

/// Returns the RTP packets of the capture's H.264 stream.
fn bunny_video_packets() -> Vec<&'static [u8]> {
    let mut remaining = BUNNY;
    let mut pkts = Vec::new();
    while !remaining.is_empty() {
        assert_eq!(remaining[0], b'$');
        let channel_id = remaining[1];
        let len = u16::from_be_bytes([remaining[2], remaining[3]]);
        let (data, after) = remaining.split_at(4 + usize::from(len));
        remaining = after;
        if channel_id == 2 {
            pkts.push(&data[4..]);
        }
    }
    pkts
}

fn reference_frames() -> Vec<Frame> {
    let mut d = VideoDepacketizer::new("h264", 90_000, Some(BUNNY_FMTP)).unwrap();
    let mut c = Collector::default();
    let mut f = Feeder::new();
    for pkt in bunny_video_packets() {
        f.push(pkt, &mut d, &mut c);
    }
    assert_eq!(c.losses, 0);
    assert!(c.frames.len() > 10);
    c.frames
}

fn repacketize(
    options: VideoPacketizerOptions,
    max_payload_size: u16,
    initial_seq: u16,
) -> (Vec<Pkt>, String) {
    let mut d = VideoDepacketizer::new("h264", 90_000, Some(BUNNY_FMTP)).unwrap();
    let mut p = VideoPacketizer::new(d.parameters().unwrap(), options).unwrap();
    let fmtp = p.payload_format().fmtp().unwrap().to_owned();
    let mut sender = Sender::new(
        96,
        SenderOptions::default()
            .ssrc(0x1234_5678)
            .initial_sequence_number(initial_seq)
            .timestamp_offset(0)
            .max_payload_size(max_payload_size),
    );
    let mut out = Vec::new();
    let mut f = Feeder::new();
    for pkt in bunny_video_packets() {
        f.push(
            pkt,
            &mut d,
            &mut Repacketize {
                packetizer: &mut p,
                sink: Recorder::new(&mut sender, &mut out),
            },
        );
    }
    (out, fmtp)
}

/// Every combination of options reproduces the original frames exactly. The
/// depacketizer removes parameter sets from frame data, so inserting them
/// doesn't change that.
#[test]
fn round_trip() {
    let reference = reference_frames();
    for max_payload_size in [3, 4, 5, 17, 100, 576, 1200, 1400, 1500, 65000] {
        for aggregate in [false, true] {
            for parameter_set_insertion in [
                ParameterSetInsertion::Never,
                ParameterSetInsertion::EachKeyFrame,
            ] {
                let options = VideoPacketizerOptions::default()
                    .parameter_set_insertion(parameter_set_insertion)
                    .aggregate(aggregate);
                let ctx = format!("{options:?}, max_payload_size={max_payload_size}");
                let (pkts, fmtp) = repacketize(options, max_payload_size, 65_500);
                let mut d = VideoDepacketizer::new("h264", 90_000, Some(&fmtp)).unwrap();
                let mut c = Collector::default();
                let mut f = Feeder::new();
                let mut saw_stap_a = false;
                let mut next_frame_start = true;
                for pkt in &pkts {
                    let header = f.push(&pkt.raw, &mut d, &mut c);
                    let payload = &pkt.raw[12..];
                    assert!(payload.len() <= usize::from(max_payload_size), "{ctx}");
                    saw_stap_a |= payload[0] & 0x1f == 24;
                    assert_eq!(pkt.frame_start, next_frame_start, "{ctx}");
                    next_frame_start = header.mark();
                    assert_eq!(pkt.sequence_number, header.sequence_number());
                }
                assert!(next_frame_start, "{ctx}: last packet should have mark");
                assert_eq!(c.losses, 0, "{ctx}");

                // A STAP-A is used iff some frame has two consecutive NALs
                // (including inserted SPS and PPS) which fit in one.
                let (sps_len, pps_len) = sprop_lens(&fmtp);
                let expect_stap_a = aggregate
                    && reference.iter().any(|f| {
                        let mut lens: Vec<usize> = Vec::new();
                        if f.is_random_access_point
                            && parameter_set_insertion == ParameterSetInsertion::EachKeyFrame
                        {
                            lens.extend([sps_len, pps_len]);
                        }
                        lens.extend(f.nals.iter().map(Vec::len));
                        lens.windows(2)
                            .any(|w| 1 + 2 + w[0] + 2 + w[1] <= usize::from(max_payload_size))
                    });
                assert_eq!(saw_stap_a, expect_stap_a, "{ctx}: STAP-A usage");
                assert_eq!(c.frames.len(), reference.len(), "{ctx}");
                for (i, (a, b)) in c.frames.iter().zip(&reference).enumerate() {
                    assert_eq!(a, b, "{ctx}: frame {i}");
                }
            }
        }
    }
}

/// Returns the lengths of the SPS and PPS in an H.264 fmtp.
fn sprop_lens(fmtp: &str) -> (usize, usize) {
    use base64::Engine as _;
    let sprop = fmtp.split_once("sprop-parameter-sets=").unwrap().1;
    let (sps, pps) = sprop.split_once(',').unwrap();
    let d = |s| {
        base64::engine::general_purpose::STANDARD
            .decode(s)
            .unwrap()
            .len()
    };
    (d(sps), d(pps))
}

/// The repacketized stream is described by an fmtp equivalent to the original.
#[test]
fn payload_format() {
    let (_, fmtp) = repacketize(VideoPacketizerOptions::default(), 1400, 0);
    assert_eq!(fmtp, BUNNY_FMTP);
}

/// With parameter set insertion, every key frame starts with SPS and PPS, so a
/// receiver joining there needs no SDP.
#[test]
fn parameter_set_insertion() {
    let (pkts, _) = repacketize(VideoPacketizerOptions::default(), 1400, 0);
    let rap_starts: Vec<_> = pkts
        .iter()
        .filter(|p| p.frame_start && p.random_access_point)
        .collect();
    assert!(!rap_starts.is_empty());
    for p in rap_starts {
        // A STAP-A beginning with SPS then PPS.
        let payload = &p.raw[12..];
        assert_eq!(payload[0] & 0x1f, 24);
        assert_eq!(payload[3] & 0x1f, 7);
        let sps_len = usize::from(u16::from_be_bytes([payload[1], payload[2]]));
        assert_eq!(payload[3 + sps_len + 2] & 0x1f, 8);
    }

    // A receiver whose depacketizer has no parameters at all can start at any
    // random access point.
    let (pkts, _) = repacketize(VideoPacketizerOptions::default(), 1400, 0);
    let first_rap = pkts
        .iter()
        .rposition(|p| p.frame_start && p.random_access_point)
        .unwrap();
    let mut d = VideoDepacketizer::new("h264", 90_000, None).unwrap();
    let mut c = Collector::default();
    let mut f = Feeder::new();
    for pkt in &pkts[first_rap..] {
        f.push(&pkt.raw, &mut d, &mut c);
    }
    assert!(c.frames[0].is_random_access_point);
    assert!(d.parameters().is_some());
}

/// Upstream quirks don't reach downstream: here, an Annex B separator inside a
/// FU-A becomes two properly separated NALs.
#[test]
fn cleans_annex_b_in_fu_a() {
    let mut d = VideoDepacketizer::new("h264", 90_000, Some(BUNNY_FMTP)).unwrap();
    let mut p = VideoPacketizer::new(
        d.parameters().unwrap(),
        VideoPacketizerOptions::default().parameter_set_insertion(ParameterSetInsertion::Never),
    )
    .unwrap();
    let mut sender = Sender::new(
        96,
        SenderOptions::default()
            .ssrc(1)
            .initial_sequence_number(0)
            .timestamp_offset(0),
    );
    let mut out = Vec::new();
    let mut f = Feeder::new();
    for pkt in [
        rtp(0, 0, false, b"\x1c\x86sei\x00\x00"), // FU-A start of an SEI...
        rtp(1, 0, true, b"\x1c\x46\x01\x65idr"),  // ...with an IDR slice inside.
    ] {
        f.push(
            &pkt,
            &mut d,
            &mut Repacketize {
                packetizer: &mut p,
                sink: Recorder::new(&mut sender, &mut out),
            },
        );
    }
    assert_eq!(out.len(), 1);
    assert_eq!(
        &out[0].raw[12..],
        b"\x78\x00\x04\x06sei\x00\x04\x65idr", // STAP-A of SEI, IDR.
    );
}

/// A proxy can fix up parameters (§3.5 of `design/server-api.md`) by wrapping
/// `Repacketize`; downstream sees only the fixed parameters.
#[test]
fn parameter_fixup() {
    // Stand-ins for a rewritten SPS and PPS.
    const SPS: &[u8] = b"\x67\x64\x00\x1e\xac\x2c\x6a\x82\xc0\xf6\x9b\x82\x80\x82\xa0\x00\x00\x03\x00\x20\x00\x00\x03\x03\xd0\x80";
    const PPS: &[u8] = b"\x68\xee\x31\xb2\x1b";

    struct Fixup<'a, S> {
        inner: Repacketize<'a, S>,
        fixed: bool,
    }
    impl<S: retina::codec::PayloadSink> VideoHandler<()> for Fixup<'_, S> {
        fn frame_start(&mut self, fs: &mut VideoFrameStart<'_, ()>) -> Accumulate {
            // Bunny's parameters come from the SDP and never change, so fix
            // them once. A real proxy would also fix them when
            // `has_new_parameters()`.
            if !self.fixed {
                let p = VideoParameters::from_h264_parameter_sets([SPS, PPS]).unwrap();
                fs.set_parameters(&p).unwrap();
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

    let mut d = VideoDepacketizer::new("h264", 90_000, Some(BUNNY_FMTP)).unwrap();
    let mut p =
        VideoPacketizer::new(d.parameters().unwrap(), VideoPacketizerOptions::default()).unwrap();
    let mut sender = Sender::new(
        96,
        SenderOptions::default()
            .ssrc(1)
            .initial_sequence_number(0)
            .timestamp_offset(0),
    );
    let mut out = Vec::new();
    let mut f = Feeder::new();
    let mut fixup_fixed = false;
    for pkt in bunny_video_packets() {
        let mut h = Fixup {
            inner: Repacketize {
                packetizer: &mut p,
                sink: Recorder::new(&mut sender, &mut out),
            },
            fixed: fixup_fixed,
        };
        f.push(pkt, &mut d, &mut h);
        fixup_fixed = h.fixed;
    }

    // The upstream depacketizer and packetizer both reflect the fixup.
    let fixed = VideoParameters::from_h264_parameter_sets([SPS, PPS]).unwrap();
    assert_eq!(d.parameters(), Some(&fixed));
    assert_eq!(p.parameters(), &fixed);
    assert_eq!(
        sprop_lens(p.payload_format().fmtp().unwrap()),
        (SPS.len(), PPS.len())
    );

    // Every key frame downstream carries the fixed parameters, not the originals.
    let mut raps = 0;
    for pkt in out
        .iter()
        .filter(|p| p.frame_start && p.random_access_point)
    {
        let payload = &pkt.raw[12..];
        assert_eq!(payload[0] & 0x1f, 24);
        assert_eq!(&payload[3..3 + SPS.len()], SPS);
        raps += 1;
    }
    assert!(raps > 1);
}

/// Repacketization streams: after each upstream packet, the packetizer holds
/// back at most one payload's worth of the data it has been given.
#[test]
fn streams() {
    /// Counts bytes of NAL data passed to the inner handler.
    struct Counting<'a, H> {
        inner: H,
        bytes: &'a mut usize,
    }
    impl<H: VideoHandler<()>> VideoHandler<()> for Counting<'_, H> {
        fn frame_start(&mut self, fs: &mut VideoFrameStart<'_, ()>) -> Accumulate {
            self.inner.frame_start(fs)
        }
        fn data(&mut self, data: &VideoData<'_>) {
            *self.bytes += data.len();
            self.inner.data(data)
        }
        fn frame_end(&mut self, fe: &mut VideoFrameEnd<'_, ()>) {
            self.inner.frame_end(fe)
        }
        fn loss(&mut self, loss: &Loss<'_, ()>) {
            self.inner.loss(loss)
        }
    }

    const MAX_PAYLOAD_SIZE: u16 = 500;
    let mut d = VideoDepacketizer::new("h264", 90_000, Some(BUNNY_FMTP)).unwrap();
    let mut p =
        VideoPacketizer::new(d.parameters().unwrap(), VideoPacketizerOptions::default()).unwrap();
    let mut sender = Sender::new(
        96,
        SenderOptions::default()
            .ssrc(1)
            .initial_sequence_number(0)
            .timestamp_offset(0)
            .max_payload_size(MAX_PAYLOAD_SIZE),
    );
    let mut out = Vec::new();
    let mut f = Feeder::new();
    let mut in_bytes = 0;
    let mut max_behind = 0;
    for pkt in bunny_video_packets() {
        f.push(
            pkt,
            &mut d,
            &mut Counting {
                inner: Repacketize {
                    packetizer: &mut p,
                    sink: Recorder::new(&mut sender, &mut out),
                },
                bytes: &mut in_bytes,
            },
        );

        // Output payloads also include packetization headers and inserted
        // parameter sets, so this is conservative.
        let out_bytes: usize = out.iter().map(|o| o.raw.len() - 12).sum();
        max_behind = max_behind.max(in_bytes.saturating_sub(out_bytes));
    }
    assert!(
        max_behind <= usize::from(MAX_PAYLOAD_SIZE),
        "held back up to {max_behind} bytes"
    );
    assert!(max_behind > 0);
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

    fn max_payload_size(&self) -> u16 {
        self.sender.max_payload_size()
    }
}

/// Throttling a congested sink damages at most one frame, marked so the
/// receiver knows which, without sequence number gaps; the receiver resumes at
/// the next random access point with frames identical to the originals.
#[test]
fn throttle() {
    let reference = reference_frames();
    let mut saw_truncation = false;
    let mut saw_clean_drop = false;
    for start in 0..200 {
        let ctx = format!("congested from upstream packet {start}");
        let mut d = VideoDepacketizer::new("h264", 90_000, Some(BUNNY_FMTP)).unwrap();
        let options = VideoPacketizerOptions::default();
        let mut p = VideoPacketizer::new(d.parameters().unwrap(), options).unwrap();
        let mut sink = Throttled {
            sender: Sender::new(
                96,
                SenderOptions::default()
                    .ssrc(1)
                    .initial_sequence_number(0)
                    .timestamp_offset(0)
                    .max_payload_size(500),
            ),
            out: Vec::new(),
            congested: false,
        };
        let mut f = Feeder::new();
        for (i, pkt) in bunny_video_packets().into_iter().enumerate() {
            sink.congested = (start..start + 3).contains(&i);
            f.push(
                pkt,
                &mut d,
                &mut Repacketize {
                    packetizer: &mut p,
                    sink: &mut sink,
                },
            );
        }
        let truncated = sink.out.iter().filter(|p| p.raw[12] & 0x80 != 0).count();
        assert!(truncated <= 1, "{ctx}");

        let mut d = VideoDepacketizer::new("h264", 90_000, Some(BUNNY_FMTP)).unwrap();
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
