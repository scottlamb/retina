// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! `VideoFrameEnd::is_decodable` with open GOPs: leading pictures which
//! reference pictures before their random access point are decodable only if
//! decoding didn't start at that random access point.

mod common;

use std::num::NonZeroU32;

use common::{Feeder, Pkt, Recorder};
use retina::codec::h26x::Framing;
use retina::codec::{
    Accumulate, FrameFormat, VideoDepacketizer, VideoFrameEnd, VideoFrameInfo, VideoFrameStart,
    VideoHandler, VideoPacketizer, VideoPacketizerOptions, VideoParameters,
};
use retina::rtp::{Sender, SenderOptions};

/// 24 frames from `x264 --open-gop --keyint 8 --bframes 2 --b-adapt 0
/// --b-pyramid none`, 64x64. In output order, frames are `IBBPBBPB` repeated.
/// In decoding order (as indexed here), frames 0 (an IDR), 7, and 15 (I frames
/// with recovery point SEI messages) are random access points; 7 and 15 are
/// each followed by a B frame which precedes them in output order and
/// references the previous GOP.
const OPEN_GOP: &[u8] = include_bytes!("testdata/open_gop.h264");

/// The random access points' indices, as described above.
const RANDOM_ACCESS_POINTS: [usize; 3] = [0, 7, 15];

/// A NAL unit within an Annex B stream: the position of its start code
/// (including any leading zero byte), and its body (header included).
struct Nal<'a> {
    start: usize,
    body: &'a [u8],
}

/// Splits an Annex B stream into NAL units.
fn nals(stream: &[u8]) -> Vec<Nal<'_>> {
    let mut starts = Vec::new();
    let mut i = 0;
    while i + 3 <= stream.len() {
        if stream[i..i + 3] == [0, 0, 1] {
            starts.push((
                if i > 0 && stream[i - 1] == 0 {
                    i - 1
                } else {
                    i
                },
                i + 3,
            ));
            i += 3;
        } else {
            i += 1;
        }
    }
    starts
        .iter()
        .enumerate()
        .map(|(n, &(start, body))| {
            let end = starts.get(n + 1).map_or(stream.len(), |&(s, _)| s);
            Nal {
                start,
                body: &stream[body..end],
            }
        })
        .collect()
}

/// Splits an H.264 Annex B stream into access units, following H.264
/// section 7.4.1.2.3 as far as this stream needs: after a slice, an SEI,
/// SPS, PPS, access unit delimiter, or a slice with `first_mb_in_slice` 0
/// begins a new access unit. Returns each access unit's data and whether it's
/// disposable (has `nal_ref_idc` 0).
fn access_units(stream: &[u8]) -> Vec<(&[u8], bool)> {
    let mut out = Vec::new();
    let mut cur: Option<(usize, bool)> = None; // (start, is_disposable)
    let mut seen_slice = false;
    for nal in nals(stream) {
        let t = nal.body[0] & 0b1_1111;
        let first_mb_zero = nal.body.get(1).is_some_and(|&b| b & 0x80 != 0);
        if seen_slice && (matches!(t, 6..=9) || (matches!(t, 1 | 5) && first_mb_zero)) {
            let (start, disposable) = cur.take().unwrap();
            out.push((&stream[start..nal.start], disposable));
            seen_slice = false;
        }
        let (_, disposable) = cur.get_or_insert((nal.start, true));
        if matches!(t, 1..=5) {
            seen_slice = true;
            *disposable &= nal.body[0] & 0b0110_0000 == 0;
        }
    }
    let (start, disposable) = cur.unwrap();
    out.push((&stream[start..], disposable));
    out
}

/// Packetizes the stream, returning packets and the first packet index of each frame.
fn packets(max_payload_size: u16) -> (Vec<Pkt>, Vec<usize>) {
    // The stream repeats its SPS and PPS at each random access point; use the first.
    let nals = nals(OPEN_GOP);
    let first = |t| nals.iter().map(|n| n.body).find(|b| b[0] & 0b1_1111 == t);
    let parameters =
        VideoParameters::from_h264_parameter_sets([first(7).unwrap(), first(8).unwrap()]).unwrap();
    let mut sender = Sender::new(
        96,
        SenderOptions::default()
            .ssrc(1)
            .initial_sequence_number(0)
            .timestamp_offset(0)
            .max_payload_size(max_payload_size),
    );
    let mut p = VideoPacketizer::new(&parameters, VideoPacketizerOptions::default()).unwrap();
    let mut out = Vec::new();
    let mut starts = Vec::new();
    for (i, (data, disposable)) in access_units(OPEN_GOP).into_iter().enumerate() {
        starts.push(out.len());
        p.push_frame(
            VideoFrameInfo::new(
                retina::Timestamp::new(i as i64 * 9000, NonZeroU32::new(90_000).unwrap(), 0)
                    .unwrap(),
            )
            .with_random_access_point(RANDOM_ACCESS_POINTS.contains(&i))
            .with_disposable(disposable),
            FrameFormat::MP4.with_h26x_framing(Framing::AnnexB),
            data,
            &mut Recorder::new(&mut sender, &mut out),
        )
        .unwrap();
    }
    assert_eq!(starts.len(), 24);
    (out, starts)
}

/// Records `(is_decodable at start, is_decodable at end)` per frame.
#[derive(Default)]
struct H(Vec<(bool, bool)>, Option<bool>);

impl VideoHandler<()> for H {
    fn frame_start(&mut self, fs: &mut VideoFrameStart<'_, ()>) -> Accumulate {
        self.1 = Some(fs.is_decodable());
        Accumulate::No
    }

    fn frame_end(&mut self, fe: &mut VideoFrameEnd<'_, ()>) {
        let start = self.1.take().unwrap();
        self.0.push((start, fe.is_decodable()));
    }
}

/// Depacketizes `pkts`, returning `is_decodable` for each frame (checking
/// that it's the same at start and end).
fn decodable<'a>(pkts: impl IntoIterator<Item = &'a Pkt>) -> Vec<bool> {
    let mut d = VideoDepacketizer::new("h264", 90_000, None).unwrap();
    let mut f = Feeder::new();
    let mut h = H::default();
    for pkt in pkts {
        f.push(&pkt.raw, &mut d, &mut h);
    }
    h.0.into_iter()
        .map(|(start, end)| {
            assert_eq!(start, end);
            end
        })
        .collect()
}

/// Expected `is_decodable` for frames `range`, given which random access
/// points' (7 and/or 15) leading pictures can't be decoded, and that frames in
/// `tainted` can't be decoded.
fn expected(
    range: std::ops::Range<usize>,
    undecodable_rasl: &[usize],
    tainted: std::ops::Range<usize>,
) -> Vec<bool> {
    range
        .map(|i| !tainted.contains(&i) && !undecodable_rasl.iter().any(|&rap| i == rap + 1))
        .collect()
}

#[test]
fn open_gop() {
    for max_payload_size in [1400, 16, 3] {
        let (pkts, starts) = packets(max_payload_size);

        // From the start: everything is decodable.
        assert_eq!(
            decodable(&pkts),
            expected(0..24, &[], 0..0),
            "max_payload_size={max_payload_size}"
        );

        // From the second GOP: its leading picture isn't decodable.
        assert_eq!(
            decodable(&pkts[starts[7]..]),
            expected(7..24, &[7], 0..0),
            "max_payload_size={max_payload_size}"
        );

        // Loss of frame 9 (a P frame): taints frames until the next random
        // access point, and that GOP's leading picture.
        let lossy = pkts[..starts[9]].iter().chain(&pkts[starts[10]..]);
        let mut want = expected(0..24, &[15], 9..15);
        want.remove(9);
        assert_eq!(
            decodable(lossy),
            want,
            "max_payload_size={max_payload_size}"
        );
    }
}
