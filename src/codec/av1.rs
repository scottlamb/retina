// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [AV1](https://aomediacodec.github.io/av1-spec/)-encoded video.
//! [RTP Payload Format for AV1](https://aomediacodec.github.io/av1-rtp-spec/)
//!
//! [`rtp`] reassembles temporal units from RTP packets; [`obu`] parses the OBUs
//! a depacketizer and an ISO BMFF writer need (sequence header, `av1C`, the
//! RFC 6381 codec string, random access).
//!
//! Output frames are AV1 temporal units in the Low Overhead Bitstream Format: one temporal
//! delimiter first, then every OBU with its size field (padding and tile lists removed). That
//! is the sample format GStreamer's `isofmp4mux` writes for AV1 in ISO BMFF. Parameters (`av1C`, the RFC 6381 codec string, the frame size)
//! come from the sequence header; a changed sequence header sets `has_new_parameters`.
//!
//! Unlike retina's other depacketizers, a malformed packet does not end the session: the
//! partial temporal unit is dropped, and the next one carries the count in `loss()`. A camera
//! that sends one bad packet should cost one frame, not a reconnect.

pub(crate) mod obu;
pub(crate) mod rtp;

use std::collections::VecDeque;

use bytes::Bytes;
use rtp::{Av1RtpPacket, Depacketizer as Av1Depacketizer, Limits};

use crate::buf::PacketRef;
use crate::codec::{
    AllPixelDimensions, CodecItem, DepacketizeError, ParametersRef, VideoFrame, VideoParameters,
    VideoParametersCodec,
};

/// Most temporal units waiting for `pull` (the depacketizer can finish two from one packet).
const MAX_PENDING: usize = 4;
/// Packet timestamps remembered to give each finished unit its own `Timestamp` and context.
const MAX_STARTS: usize = 8;

#[derive(Debug)]
pub(crate) struct Depacketizer {
    inner: Av1Depacketizer,
    params: Option<VideoParameters>,
    /// The raw sequence header OBU the parameters were built from.
    seq_header: Option<Vec<u8>>,
    /// (extended RTP timestamp, its `Timestamp`, the first packet's context) per unit in flight.
    starts: VecDeque<(i64, crate::Timestamp, crate::PacketContext)>,
    pending: VecDeque<VideoFrame>,
    /// Packets refused as malformed (each also counted as loss on the next unit).
    malformed_packets: u64,
}

impl Depacketizer {
    pub(super) fn new(clock_rate: u32) -> Result<Self, String> {
        // RTP Payload Format for AV1 §7.1: the clock rate is 90000.
        if clock_rate != 90_000 {
            return Err(format!("AV1 clock rate {clock_rate} is not 90000"));
        }
        Ok(Depacketizer {
            inner: Av1Depacketizer::new(Limits::default()),
            params: None,
            seq_header: None,
            starts: VecDeque::new(),
            pending: VecDeque::new(),
            malformed_packets: 0,
        })
    }

    pub(super) fn parameters(&self) -> Option<ParametersRef<'_>> {
        self.params.as_ref().map(ParametersRef::Video)
    }

    pub(super) fn push(&mut self, pkt: &PacketRef<'_>) -> Result<(), String> {
        let meta = &pkt.meta;
        let ts = meta.timestamp.timestamp();
        if !self.starts.iter().any(|(t, _, _)| *t == ts) {
            if self.starts.len() >= MAX_STARTS {
                self.starts.pop_front();
            }
            self.starts.push_back((ts, meta.timestamp, meta.ctx));
        }
        let (s1, s2) = pkt.payload().slices();
        let mut payload = Vec::with_capacity(s1.len().saturating_add(s2.len()));
        payload.extend_from_slice(s1);
        payload.extend_from_slice(s2);
        if self
            .inner
            .push(Av1RtpPacket {
                timestamp: ts,
                mark: meta.mark,
                loss: meta.loss,
                payload: &payload,
            })
            .is_err()
        {
            self.malformed_packets = self.malformed_packets.saturating_add(1);
        }
        while let Some(tu) = self.inner.pull() {
            let (timestamp, start_ctx) =
                match self.starts.iter().position(|(t, _, _)| *t == tu.timestamp) {
                    Some(i) => {
                        let found = self.starts.get(i).map(|(_, t, c)| (*t, *c));
                        // Everything up to and including this unit's start is done.
                        self.starts.drain(..=i);
                        found.unwrap_or((meta.timestamp, meta.ctx))
                    }
                    None => (meta.timestamp, meta.ctx),
                };
            let has_new_parameters = self.update_parameters(&tu.data);
            if self.pending.len() >= MAX_PENDING {
                // The caller must pull between pushes (retina's contract); refusing here keeps
                // memory bounded if it does not.
                return Err("AV1 depacketizer: frames not pulled".to_owned());
            }
            self.pending.push_back(VideoFrame {
                start_ctx,
                end_ctx: meta.ctx,
                has_new_parameters,
                loss: tu.loss,
                timestamp,
                stream_id: meta.stream_id,
                is_random_access_point: tu.random_access,
                is_disposable: false,
                data: tu.data,
            });
        }
        Ok(())
    }

    pub(super) fn pull(&mut self) -> Option<Result<CodecItem, DepacketizeError>> {
        self.pending
            .pop_front()
            .map(|f| Ok(CodecItem::VideoFrame(f)))
    }

    /// Rebuild the parameters when this unit carries a sequence header different from the
    /// current one. Returns true when they changed.
    fn update_parameters(&mut self, tu: &[u8]) -> bool {
        let Ok(Some(seq)) = obu::find_sequence_header(tu) else {
            return false;
        };
        if self.seq_header.as_deref() == Some(seq) {
            return false;
        }
        let Ok(Some(header)) = obu::iter_obus(seq).next().transpose() else {
            return false;
        };
        let Ok(info) = obu::parse_sequence_header(header.payload) else {
            return false;
        };
        let Ok(av1c) = obu::av1c_record(seq, &info) else {
            return false;
        };
        let w = u16::try_from(info.max_frame_width).unwrap_or(u16::MAX);
        let h = u16::try_from(info.max_frame_height).unwrap_or(u16::MAX);
        self.params = Some(VideoParameters {
            all_pixel_dimensions: AllPixelDimensions {
                coded: (w, h),
                display: (w, h),
            },
            rfc6381_codec: obu::codec_string(&info),
            pixel_aspect_ratio: None,
            frame_rate: None,
            extra_data: Bytes::from(av1c),
            codec: VideoParametersCodec::Av1,
        });
        self.seq_header = Some(seq.to_vec());
        true
    }
}
