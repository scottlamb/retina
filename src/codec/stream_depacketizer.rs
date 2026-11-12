// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Depacketization of an RTP stream received outside [`crate::client`].

use std::num::NonZeroU16;

use super::{CodecItem, Depacketizer, FrameFormat, ParametersRef};
use crate::buf::{MarkBuf, PacketRef};
use crate::client::Timeline;
use crate::rtp::{PacketHeader, PacketMeta};

/// Initial size of the buffer that holds payloads until their frame is
/// complete. It grows as needed: a keyframe larger than this still fits.
const INITIAL_BUF_CAPACITY: usize = 64 * 1024;

/// Turns one RTP stream received by something other than [`crate::client`]
/// into [`CodecItem`]s.
///
/// This is the receiving half of an RTSP server that accepts `ANNOUNCE` and
/// `RECORD`, or of any program that gets RTP packets on its own. Each packet's
/// header is checked, the stream's SSRC and sequence numbers are followed, its
/// 32-bit timestamps are placed on a non-wrapping timeline, and the payload
/// goes to the codec's depacketizer. The caller describes the stream from its
/// SDP media description, as the client does from the `DESCRIBE` response.
///
/// Timestamps are not policed: a sender that jumps its clock produces a
/// [`crate::Timestamp`] that jumps too, rather than an error. Packets are
/// expected in order, as TCP delivers them; one older than the last is
/// skipped.
#[derive(Debug)]
pub struct StreamDepacketizer {
    depacketizer: Depacketizer,
    buf: MarkBuf,
    timeline: Timeline,
    ssrc: Option<u32>,
    next_seq: Option<u16>,
}

impl StreamDepacketizer {
    /// Creates a depacketizer for a stream of `media` (`video`, `audio`, ...)
    /// described by its `rtpmap` (`encoding_name`, `clock_rate`, `channels`)
    /// and `fmtp` (`format_specific_params`) attributes.
    pub fn new(
        media: &str,
        encoding_name: &str,
        clock_rate: u32,
        channels: Option<NonZeroU16>,
        format_specific_params: Option<&str>,
    ) -> Result<Self, String> {
        Ok(Self {
            depacketizer: Depacketizer::new(
                media,
                encoding_name,
                clock_rate,
                channels,
                format_specific_params,
            )?,
            buf: MarkBuf::new(INITIAL_BUF_CAPACITY),
            timeline: Timeline::new(None, clock_rate, None)?,
            ssrc: None,
            next_seq: None,
        })
    }

    /// Sets the format of video frames, as
    /// [`crate::client::SessionOptions`] does for the client.
    pub fn set_frame_format(&mut self, format: FrameFormat) {
        self.depacketizer.set_frame_format(format);
    }

    /// Supplies one RTP packet: header and payload, as carried in an
    /// interleaved data frame or a UDP datagram.
    ///
    /// A packet from another SSRC is an error: the sender changed, and nothing
    /// it sends joins what came before. After an error from this or from
    /// [`StreamDepacketizer::pull`], the stream should be dropped.
    ///
    /// Between two calls, call [`StreamDepacketizer::pull`] until it returns
    /// `None`.
    pub fn push(&mut self, pkt: &[u8]) -> Result<(), String> {
        let (header, payload) =
            PacketHeader::validate(pkt).map_err(|e| format!("corrupt RTP packet: {e}"))?;
        let ssrc = header.ssrc();
        let sequence_number = header.sequence_number();
        match self.ssrc {
            Some(expected) if expected != ssrc => {
                return Err(format!(
                    "wrong ssrc {ssrc:08x} at seq={sequence_number}; expecting ssrc {expected:08x}"
                ));
            }
            _ => self.ssrc = Some(ssrc),
        }
        let loss = sequence_number.wrapping_sub(self.next_seq.unwrap_or(sequence_number));
        if loss > 0x80_00 {
            log::debug!(
                "skipping out-of-order seq={sequence_number} when expecting seq={:?}",
                self.next_seq
            );
            return Ok(());
        }
        let timestamp = self.timeline.advance_to(header.timestamp())?;
        self.next_seq = Some(sequence_number.wrapping_add(1));

        let payload = &pkt[usize::from(payload.start)..usize::from(payload.end)];
        let pos = self.buf.append(payload);
        let meta = PacketMeta {
            ctx: crate::PacketContext::dummy(),
            stream_id: 0,
            timestamp,
            sequence_number,
            ssrc,
            mark: header.mark(),
            loss,
        };
        self.depacketizer
            .push(&PacketRef::new(meta, &self.buf, pos, payload.len() as u16))
    }

    /// Retrieves a completed frame, if any.
    pub fn pull(&mut self) -> Option<Result<CodecItem, String>> {
        self.depacketizer
            .pull()
            .map(|r| r.map_err(|e| format!("seq={}: {}", e.sequence_number, e.description)))
    }

    /// The stream's parameters: from the `fmtp` attribute if it carried them,
    /// otherwise from the stream once they arrive in it.
    pub fn parameters(&self) -> Option<ParametersRef<'_>> {
        self.depacketizer.parameters()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rtp::build_raw_rtp;

    const SPROP: &str = "packetization-mode=1;profile-level-id=64001E;\
                         sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA";

    fn h264() -> StreamDepacketizer {
        StreamDepacketizer::new("video", "h264", 90_000, None, Some(SPROP)).unwrap()
    }

    fn rtp(seq: u16, ts: u32, ssrc: u32, mark: bool, payload: &[u8]) -> bytes::Bytes {
        build_raw_rtp(seq, ts, 96, ssrc, mark, payload.iter().copied()).unwrap()
    }

    fn frames(d: &mut StreamDepacketizer) -> Vec<CodecItem> {
        std::iter::from_fn(|| d.pull())
            .map(Result::unwrap)
            .collect()
    }

    fn video(item: &CodecItem) -> &super::super::VideoFrame {
        match item {
            CodecItem::VideoFrame(f) => f,
            other => panic!("expected a video frame, got {other:?}"),
        }
    }

    #[test]
    fn single_nal_and_fragmented_frames() {
        let mut d = h264();
        d.push(&rtp(10, 1000, 7, true, b"\x65idr slice")).unwrap();
        let got = frames(&mut d);
        assert_eq!(got.len(), 1);
        let f = video(&got[0]);
        assert!(f.is_random_access_point());
        assert_eq!(f.timestamp().elapsed(), 0);

        // FU-A: a non-IDR slice in three packets, one frame 3000 ticks later.
        d.push(&rtp(11, 4000, 7, false, b"\x7c\x81start ")).unwrap();
        assert!(frames(&mut d).is_empty());
        d.push(&rtp(12, 4000, 7, false, b"\x7c\x01middle "))
            .unwrap();
        assert!(frames(&mut d).is_empty());
        d.push(&rtp(13, 4000, 7, true, b"\x7c\x41end")).unwrap();
        let got = frames(&mut d);
        assert_eq!(got.len(), 1);
        let f = video(&got[0]);
        assert!(!f.is_random_access_point());
        assert_eq!(f.timestamp().elapsed(), 3000);
        assert!(d.parameters().is_some());
    }

    #[test]
    fn timestamps_continue_across_the_wrap() {
        let mut d = h264();
        d.push(&rtp(0, u32::MAX - 999, 7, true, b"\x65before"))
            .unwrap();
        assert_eq!(video(&frames(&mut d)[0]).timestamp().elapsed(), 0);
        d.push(&rtp(1, 2000, 7, true, b"\x41after")).unwrap();
        assert_eq!(video(&frames(&mut d)[0]).timestamp().elapsed(), 3000);
    }

    #[test]
    fn another_ssrc_is_an_error() {
        let mut d = h264();
        d.push(&rtp(0, 0, 7, true, b"\x65idr")).unwrap();
        frames(&mut d);
        let err = d.push(&rtp(1, 3000, 8, true, b"\x41p")).unwrap_err();
        assert!(err.contains("wrong ssrc"), "{err}");
    }

    #[test]
    fn older_packet_is_skipped() {
        let mut d = h264();
        d.push(&rtp(5, 0, 7, true, b"\x65idr")).unwrap();
        assert_eq!(frames(&mut d).len(), 1);
        d.push(&rtp(4, 0, 7, true, b"\x65stale")).unwrap();
        assert!(frames(&mut d).is_empty());
        d.push(&rtp(6, 3000, 7, true, b"\x41next")).unwrap();
        assert_eq!(frames(&mut d).len(), 1);
    }

    #[test]
    fn corrupt_packet_is_an_error() {
        let mut d = h264();
        assert!(d.push(b"\x80\x60").unwrap_err().contains("corrupt"));
    }

    #[test]
    fn g711_packets_become_audio_frames() {
        let mut d = StreamDepacketizer::new("audio", "pcma", 8_000, None, None).unwrap();
        for (seq, ts) in [(0, 0), (1, 160)] {
            d.push(&rtp(seq, ts, 9, false, &[0xd5; 160])).unwrap();
            let got = frames(&mut d);
            assert_eq!(got.len(), 1);
            match &got[0] {
                CodecItem::AudioFrame(f) => {
                    assert_eq!(f.data().len(), 160);
                    assert_eq!(f.timestamp().elapsed(), i64::from(ts));
                }
                other => panic!("expected an audio frame, got {other:?}"),
            }
        }
    }
}
