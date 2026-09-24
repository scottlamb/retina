// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! G.723.1 audio as specified in [RFC 3551 section 4.5.3](https://datatracker.ietf.org/doc/html/rfc3551#section-4.5.3).

use std::num::{NonZeroU16, NonZeroU32};

use crate::buf::PacketRef;

use super::{AudioFrameRef, AudioParameters, Handler};

const FIXED_CLOCK_RATE: u32 = 8_000;

#[derive(Debug)]
pub(crate) struct Depacketizer {
    parameters: AudioParameters,
}

impl Depacketizer {
    /// Creates a new Depacketizer.
    pub(super) fn new(clock_rate: u32) -> Result<Self, String> {
        if clock_rate != FIXED_CLOCK_RATE {
            return Err(format!(
                "Expected clock rate of {FIXED_CLOCK_RATE} for G.723, got {clock_rate}"
            ));
        }
        Ok(Self {
            parameters: AudioParameters {
                rfc6381_codec: None,
                frame_length: NonZeroU32::new(240),
                clock_rate: FIXED_CLOCK_RATE,
                channels: const { NonZeroU16::new(1).unwrap() },
                extra_data: Vec::new(),
                codec: super::AudioParametersCodec::Other,
            },
        })
    }

    pub(super) fn parameters(&self) -> Option<super::ParametersRef<'_>> {
        Some(super::ParametersRef::Audio(&self.parameters))
    }

    fn validate(payload: &[u8]) -> bool {
        let expected_hdr_bits = match payload.len() {
            24 => 0b00,
            20 => 0b01,
            4 => 0b10,
            _ => return false,
        };
        let actual_hdr_bits = payload[0] & 0b11;
        actual_hdr_bits == expected_hdr_bits
    }

    /// Supplies a new packet, delivering any resulting events to `handler`.
    pub(super) fn push_with<Ctx>(
        &mut self,
        pkt: &PacketRef<'_, Ctx>,
        handler: &mut impl Handler<Ctx>,
    ) -> Result<(), String> {
        let (s1, s2) = pkt.payload().slices();
        let joined;
        let payload = if s2.is_empty() {
            s1
        } else {
            joined = [s1, s2].concat();
            &joined[..]
        };
        if !Self::validate(payload) {
            return Err(format!(
                "Invalid G.723 packet: {:#?}",
                crate::hex::LimitedHex::new(payload, 64),
            ));
        }
        handler.audio_frame(&AudioFrameRef {
            ctx: &pkt.meta.ctx,
            timestamp: pkt.meta.timestamp,
            frame_length: NonZeroU32::new(240).unwrap(),
            loss: pkt.meta.loss,
            data: payload,
        });
        Ok(())
    }
}
