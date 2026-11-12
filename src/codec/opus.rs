// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Opus audio as specified in [RFC 7587](https://datatracker.ietf.org/doc/html/rfc7587).
//!
//! Each RTP packet carries exactly one Opus packet, which may hold several Opus
//! frames. The only thing to work out is how long it lasts, which is read from
//! its table-of-contents byte, as in
//! [RFC 6716 section 3.1](https://datatracker.ietf.org/doc/html/rfc6716#section-3.1).

use std::num::{NonZeroU16, NonZeroU32};

use bytes::Bytes;

use crate::buf::PacketRef;
use crate::codec::DepacketizeError;

use super::AudioParameters;

/// The RTP clock rate of Opus, whatever rate the stream was encoded at, as in
/// [RFC 7587 section 4.1](https://datatracker.ietf.org/doc/html/rfc7587#section-4.1).
const FIXED_CLOCK_RATE: u32 = 48_000;

/// The most a packet may last, 120 ms, as in
/// [RFC 6716 section 3.4](https://datatracker.ietf.org/doc/html/rfc6716#section-3.4).
const MAX_SAMPLES_PER_PACKET: u32 = 5_760;

/// How long a packet lasts in samples at 48 kHz, or `None` if it is malformed.
fn samples_in_packet(packet: &[u8]) -> Option<NonZeroU32> {
    let toc = *packet.first()?;
    let config = toc >> 3;
    let samples_per_frame = match config {
        0..=11 => [480, 960, 1_920, 2_880][usize::from(config & 0b11)], // SILK-only.
        12..=15 => [480, 960][usize::from(config & 0b1)],               // Hybrid.
        _ => [120, 240, 480, 960][usize::from(config & 0b11)],          // CELT-only.
    };
    let frames = match toc & 0b11 {
        0 => 1,
        1 | 2 => 2,
        _ => u32::from(*packet.get(1)? & 0b11_1111),
    };
    let samples = samples_per_frame * frames;
    if samples > MAX_SAMPLES_PER_PACKET {
        return None;
    }
    NonZeroU32::new(samples)
}

#[derive(Debug)]
pub(crate) struct Depacketizer {
    pending: Option<super::AudioFrame>,
    parameters: AudioParameters,
}

impl Depacketizer {
    /// Creates a new Depacketizer.
    pub(super) fn new(clock_rate: u32, channels: Option<NonZeroU16>) -> Result<Self, String> {
        if clock_rate != FIXED_CLOCK_RATE {
            return Err(format!(
                "Expected clock rate of {FIXED_CLOCK_RATE} for Opus, got {clock_rate}"
            ));
        }
        Ok(Self {
            pending: None,
            parameters: AudioParameters {
                rfc6381_codec: Some("Opus".to_owned()),
                frame_length: None, // variable
                clock_rate: FIXED_CLOCK_RATE,
                // The rtpmap attribute always says 2, whatever the packets hold.
                channels: channels.unwrap_or(const { NonZeroU16::new(2).unwrap() }),
                extra_data: Vec::new(),
                codec: super::AudioParametersCodec::Other,
            },
        })
    }

    pub(super) fn parameters(&self) -> Option<super::ParametersRef<'_>> {
        Some(super::ParametersRef::Audio(&self.parameters))
    }

    pub(super) fn push(&mut self, pkt: &PacketRef<'_>) -> Result<(), String> {
        assert!(self.pending.is_none());
        let (s1, s2) = pkt.payload().slices();
        let mut payload = Vec::with_capacity(crate::to_usize(pkt.payload_len()));
        payload.extend_from_slice(s1);
        payload.extend_from_slice(s2);
        let frame_length = samples_in_packet(&payload).ok_or_else(|| {
            format!(
                "Invalid Opus packet: {:#?}",
                crate::hex::LimitedHex::new(&payload, 64),
            )
        })?;
        self.pending = Some(super::AudioFrame {
            ctx: pkt.meta.ctx,
            loss: pkt.meta.loss,
            stream_id: pkt.meta.stream_id,
            timestamp: pkt.meta.timestamp,
            frame_length,
            data: Bytes::from(payload),
        });
        Ok(())
    }

    pub(super) fn pull(&mut self) -> Option<Result<super::CodecItem, DepacketizeError>> {
        self.pending
            .take()
            .map(|f| Ok(super::CodecItem::AudioFrame(f)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::buf::{MarkBuf, PacketRef};
    use crate::{PacketContext, codec::CodecItem, rtp::ReceivedPacketBuilder};

    /// A packet of `config` with the given frame count code and following bytes.
    fn packet(config: u8, code: u8, rest: &[u8]) -> Vec<u8> {
        let mut packet = vec![config << 3 | code];
        packet.extend_from_slice(rest);
        packet
    }

    const TIMESTAMP: crate::Timestamp = crate::Timestamp {
        timestamp: 960,
        clock_rate: NonZeroU32::new(FIXED_CLOCK_RATE).unwrap(),
        start: 0,
    };

    fn push(d: &mut Depacketizer, buf: &mut MarkBuf, payload: &[u8]) -> Result<(), String> {
        let pkt = ReceivedPacketBuilder {
            ctx: PacketContext::dummy(),
            stream_id: 0,
            sequence_number: 0,
            timestamp: TIMESTAMP,
            payload_type: 111,
            ssrc: 0,
            mark: false,
            loss: 0,
        }
        .build(payload.iter().copied())
        .unwrap();
        let pos = buf.end();
        buf.extend(pkt.payload());
        buf.advance_unparsed(buf.end());
        let meta = crate::rtp::PacketMeta::from_received(&pkt);
        d.push(&PacketRef::new(meta, buf, pos, payload.len() as u16))
    }

    #[test]
    fn duration_by_config() {
        for (configs, durations) in [
            (0..=3, [480, 960, 1_920, 2_880]),  // SILK narrowband.
            (4..=7, [480, 960, 1_920, 2_880]),  // SILK mediumband.
            (8..=11, [480, 960, 1_920, 2_880]), // SILK wideband.
            (16..=19, [120, 240, 480, 960]),    // CELT narrowband.
            (20..=23, [120, 240, 480, 960]),    // CELT wideband.
            (24..=27, [120, 240, 480, 960]),    // CELT super-wideband.
            (28..=31, [120, 240, 480, 960]),    // CELT fullband.
        ] {
            for (config, duration) in configs.zip(durations) {
                assert_eq!(
                    samples_in_packet(&packet(config, 0, &[])).map(NonZeroU32::get),
                    Some(duration),
                    "config {config}"
                );
            }
        }
        for (config, duration) in [(12, 480), (13, 960), (14, 480), (15, 960)] {
            assert_eq!(
                samples_in_packet(&packet(config, 0, &[])).map(NonZeroU32::get),
                Some(duration),
                "hybrid config {config}"
            );
        }
    }

    #[test]
    fn duration_by_frame_count() {
        let samples =
            |code, rest: &[u8]| samples_in_packet(&packet(31, code, rest)).map(NonZeroU32::get);
        assert_eq!(samples(0, &[]), Some(960));
        assert_eq!(samples(1, &[]), Some(1_920));
        assert_eq!(samples(2, &[]), Some(1_920));
        assert_eq!(samples(3, &[3]), Some(2_880));

        // The padding and variable-bitrate flags are not part of the count.
        assert_eq!(samples(3, &[0b1100_0011]), Some(2_880));
    }

    #[test]
    fn malformed_packets() {
        assert_eq!(samples_in_packet(&[]), None);

        // Code 3 without its frame count byte, or with no frames.
        assert_eq!(samples_in_packet(&packet(31, 3, &[])), None);
        assert_eq!(samples_in_packet(&packet(31, 3, &[0])), None);

        // More than 120 ms: the limit itself passes.
        assert!(samples_in_packet(&packet(31, 3, &[6])).is_some());
        assert_eq!(samples_in_packet(&packet(31, 3, &[7])), None);
        assert_eq!(
            samples_in_packet(&packet(3, 1, &[])).map(NonZeroU32::get),
            Some(5_760)
        );
        assert_eq!(samples_in_packet(&packet(3, 3, &[3])), None);
    }

    #[test]
    fn depacketize() {
        let mut d = Depacketizer::new(48_000, NonZeroU16::new(2)).unwrap();
        let mut buf = MarkBuf::new(65536);
        let payload = packet(31, 0, &[1, 2, 3]);

        push(&mut d, &mut buf, &payload).unwrap();

        let Some(Ok(CodecItem::AudioFrame(frame))) = d.pull() else {
            panic!("expected an audio frame");
        };
        assert_eq!(&frame.data[..], &payload[..]);
        assert_eq!(frame.frame_length.get(), 960);
        assert_eq!(frame.timestamp, TIMESTAMP);
        assert!(d.pull().is_none());
    }

    #[test]
    fn a_malformed_packet_is_refused() {
        let mut d = Depacketizer::new(48_000, None).unwrap();
        let mut buf = MarkBuf::new(65536);

        let e = push(&mut d, &mut buf, &packet(31, 3, &[0])).unwrap_err();

        assert!(e.starts_with("Invalid Opus packet"), "{e}");
        assert!(d.pull().is_none());
    }

    #[test]
    fn parameters() {
        let d = Depacketizer::new(48_000, None).unwrap();
        let Some(super::super::ParametersRef::Audio(p)) = d.parameters() else {
            panic!("expected audio parameters");
        };
        assert_eq!(p.rfc6381_codec(), Some("Opus"));
        assert_eq!(p.clock_rate(), 48_000);
        assert_eq!(p.frame_length(), None);
    }

    #[test]
    fn another_clock_rate_is_refused() {
        assert!(Depacketizer::new(16_000, None).is_err());
    }
}
