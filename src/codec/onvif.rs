// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! ONVIF metadata streams.
//!
//! See the
//! [ONVIF Streaming Specification](https://www.onvif.org/specs/stream/ONVIF-Streaming-Spec.pdf)
//! version 19.12 section 5.2.1.1. The RTP layer muxing is simple: RTP packets with the MARK
//! bit set end messages.

use bytes::{Buf, BufMut, BytesMut};

use super::CodecItem;

#[derive(Copy, Clone, Debug)]
pub enum CompressionType {
    Uncompressed,
    GzipCompressed,
    ExiDefault,
    ExiInBand,
}

#[derive(Debug)]
pub(crate) struct Depacketizer {
    compression_type: CompressionType,
    state: State,
    high_water_size: usize,
}

#[derive(Debug)]
enum State {
    Idle,
    InProgress(InProgress),
    Ready(super::MessageFrame),
}

#[derive(Debug)]
struct InProgress {
    ctx: crate::PacketContext,
    timestamp: crate::Timestamp,
    data: BytesMut,
    loss: u16,
}

impl Depacketizer {
    pub(super) fn new(compression_type: CompressionType) -> Self {
        Depacketizer {
            compression_type,
            state: State::Idle,
            high_water_size: 0,
        }
    }

    pub(super) fn parameters(&self) -> Option<super::Parameters> {
        Some(super::Parameters::Message(super::MessageParameters(
            self.compression_type,
        )))
    }

    pub(super) fn push(&mut self, pkt: crate::client::rtp::Packet) -> Result<(), String> {
        if pkt.loss > 0 {
            if let State::InProgress(in_progress) = &self.state {
                log::debug!(
                    "Discarding {}-byte message prefix due to loss of {} RTP packets",
                    in_progress.data.len(),
                    pkt.loss
                );
                self.state = State::Idle;
            }
        }
        let mut in_progress = match std::mem::replace(&mut self.state, State::Idle) {
            State::InProgress(in_progress) => {
                if in_progress.timestamp.timestamp != pkt.timestamp.timestamp {
                    return Err(format!(
                        "Timestamp changed from {} to {} with message in progress",
                        &in_progress.timestamp, &pkt.timestamp,
                    ));
                }
                in_progress
            }
            State::Ready(..) => panic!("push while in state ready"),
            State::Idle => {
                if pkt.mark {
                    // fast-path: avoid copy.
                    self.state = State::Ready(super::MessageFrame {
                        stream_id: pkt.stream_id,
                        loss: pkt.loss,
                        ctx: pkt.ctx,
                        timestamp: pkt.timestamp,
                        data: pkt.payload,
                    });
                    return Ok(());
                }
                InProgress {
                    loss: pkt.loss,
                    ctx: pkt.ctx,
                    timestamp: pkt.timestamp,
                    data: BytesMut::with_capacity(self.high_water_size),
                }
            }
        };
        in_progress.data.put(pkt.payload);
        if pkt.mark {
            self.high_water_size =
                std::cmp::max(self.high_water_size, in_progress.data.remaining());
            self.state = State::Ready(super::MessageFrame {
                stream_id: pkt.stream_id,
                ctx: in_progress.ctx,
                timestamp: in_progress.timestamp,
                data: in_progress.data.freeze(),
                loss: in_progress.loss,
            });
        } else {
            self.state = State::InProgress(in_progress);
        }
        Ok(())
    }

    pub(super) fn pull(&mut self) -> Option<CodecItem> {
        match std::mem::replace(&mut self.state, State::Idle) {
            State::Ready(message) => Some(CodecItem::MessageFrame(message)),
            s => {
                self.state = s;
                None
            }
        }
    }
}
