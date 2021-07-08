// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! G.723.1 audio as specified in [RFC 3551 section 4.5.3](https://datatracker.ietf.org/doc/html/rfc3551#section-4.5.3).

use std::num::NonZeroU32;

use bytes::Bytes;
use pretty_hex::PrettyHex;

#[derive(Debug)]
pub(crate) struct Depacketizer {
    parameters: super::Parameters,
    pending: Option<super::AudioFrame>,
}

impl Depacketizer {
    /// Creates a new Depacketizer.
    pub(super) fn new(clock_rate: u32) -> Result<Self, String> {
        if clock_rate != 8_000 {
            return Err(format!(
                "Expected clock rate of 8000 for G.723, got {}",
                clock_rate
            ));
        }
        Ok(Self {
            parameters: super::Parameters::Audio(super::AudioParameters {
                rfc6381_codec: None,
                frame_length: NonZeroU32::new(240),
                clock_rate,
                extra_data: Bytes::new(),
                config: super::AudioCodecConfig::Other,
            }),
            pending: None,
        })
    }

    pub(super) fn parameters(&self) -> Option<&super::Parameters> {
        Some(&self.parameters)
    }

    fn validate(pkt: &crate::client::rtp::Packet) -> bool {
        let expected_hdr_bits = match pkt.payload.len() {
            24 => 0b00,
            20 => 0b01,
            4 => 0b10,
            _ => return false,
        };
        let actual_hdr_bits = pkt.payload[0] & 0b11;
        actual_hdr_bits == expected_hdr_bits
    }

    pub(super) fn push(&mut self, pkt: crate::client::rtp::Packet) -> Result<(), String> {
        assert!(self.pending.is_none());
        if !Self::validate(&pkt) {
            return Err(format!(
                "Invalid G.723 packet: {:#?}",
                pkt.payload.hex_dump()
            ));
        }
        self.pending = Some(super::AudioFrame {
            ctx: pkt.ctx,
            loss: pkt.loss,
            stream_id: pkt.stream_id,
            timestamp: pkt.timestamp,
            frame_length: NonZeroU32::new(240).unwrap(),
            data: pkt.payload,
        });
        Ok(())
    }

    pub(super) fn pull(&mut self) -> Option<super::CodecItem> {
        self.pending.take().map(super::CodecItem::AudioFrame)
    }
}
