// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! ONVIF metadata streams.
//!
//! See the
//! [ONVIF Streaming Specification](https://www.onvif.org/specs/stream/ONVIF-Streaming-Spec.pdf)
//! version 19.12 section 5.2.1.1. The RTP layer muxing is simple: RTP packets with the MARK
//! bit set end messages.

use crate::buf::PacketRef;

use super::{MessageFrameRef, MessageHandler, MessageParameters};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CompressionType {
    Uncompressed,
    GzipCompressed,
    ExiDefault,
    ExiInBand,
}

#[derive(Debug)]
pub(crate) struct Depacketizer<Ctx> {
    parameters: MessageParameters,

    /// The message in progress, if any.
    in_progress: Option<InProgress<Ctx>>,
    high_water_size: usize,
}

#[derive(Debug)]
struct InProgress<Ctx> {
    ctx: Ctx,
    timestamp: crate::Timestamp,
    data: Vec<u8>,
    loss: u16,
}

impl<Ctx: Clone> Depacketizer<Ctx> {
    pub(super) fn new(compression_type: CompressionType) -> Self {
        Depacketizer {
            parameters: MessageParameters(compression_type),
            in_progress: None,
            high_water_size: 0,
        }
    }

    pub(super) fn parameters(&self) -> &super::MessageParameters {
        &self.parameters
    }

    /// Supplies a new packet, delivering any resulting events to `handler`.
    pub(super) fn push_with(
        &mut self,
        pkt: &PacketRef<'_, Ctx>,
        handler: &mut impl MessageHandler<Ctx>,
    ) -> Result<(), String> {
        if pkt.meta.loss > 0
            && let Some(in_progress) = &self.in_progress
        {
            log::debug!(
                "Discarding {}-byte message prefix due to loss of {} RTP packets",
                in_progress.data.len(),
                pkt.meta.loss,
            );
            self.in_progress = None;
        }
        let (s1, s2) = pkt.payload().slices();
        let mut in_progress = match self.in_progress.take() {
            Some(in_progress) => {
                if in_progress.timestamp.timestamp != pkt.meta.timestamp.timestamp {
                    return Err(format!(
                        "Timestamp changed from {} to {} with message in progress",
                        in_progress.timestamp, pkt.meta.timestamp,
                    ));
                }
                in_progress
            }
            None => {
                if pkt.meta.mark {
                    let joined;
                    let data = if s2.is_empty() {
                        s1
                    } else {
                        joined = [s1, s2].concat();
                        &joined[..]
                    };
                    handler.message_frame(&MessageFrameRef {
                        ctx: &pkt.meta.ctx,
                        timestamp: pkt.meta.timestamp,
                        loss: pkt.meta.loss,
                        data,
                    });
                    return Ok(());
                }
                InProgress {
                    loss: pkt.meta.loss,
                    ctx: pkt.meta.ctx.clone(),
                    timestamp: pkt.meta.timestamp,
                    data: Vec::with_capacity(self.high_water_size),
                }
            }
        };
        in_progress.data.extend_from_slice(s1);
        in_progress.data.extend_from_slice(s2);
        if pkt.meta.mark {
            self.high_water_size = std::cmp::max(self.high_water_size, in_progress.data.len());
            handler.message_frame(&MessageFrameRef {
                ctx: &in_progress.ctx,
                timestamp: in_progress.timestamp,
                loss: in_progress.loss,
                data: &in_progress.data,
            });
        } else {
            self.in_progress = Some(in_progress);
        }
        Ok(())
    }
}
