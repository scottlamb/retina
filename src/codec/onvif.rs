// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! ONVIF metadata streams.
//!
//! See the
//! [ONVIF Streaming Specification](https://www.onvif.org/specs/stream/ONVIF-Streaming-Spec.pdf)
//! version 19.12 section 5.2.1.1. The RTP layer muxing is simple: RTP packets with the MARK
//! bit set end messages.

use crate::rtp::ReceivedPacketRef;

use super::{MessageFrameRef, MessageHandler, MessageParameters};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CompressionType {
    Uncompressed,
    GzipCompressed,
    ExiDefault,
    ExiInBand,
}

/// The default for [`super::MessageDepacketizer::set_max_message_bytes`].
pub(super) const DEFAULT_MAX_MESSAGE_BYTES: usize = 1 << 20;

#[derive(Debug)]
pub(crate) struct Depacketizer<Ctx> {
    parameters: MessageParameters,
    state: State<Ctx>,

    /// The data of the in-progress message, if any.
    ///
    /// This is kept between messages to reuse the allocation.
    data: Vec<u8>,

    /// See [`super::MessageDepacketizer::set_max_message_bytes`].
    max_message_bytes: usize,
}

#[derive(Debug)]
enum State<Ctx> {
    Idle,

    /// A message is in progress; its data so far is in `data`.
    InProgress {
        ctx: Ctx,
        timestamp: crate::Timestamp,
    },

    /// A message with this RTP timestamp exceeded `max_message_bytes`; skip
    /// the rest of it.
    Skipping {
        timestamp: i64,
    },
}

impl<Ctx: Clone> Depacketizer<Ctx> {
    pub(super) fn new(compression_type: CompressionType) -> Self {
        Depacketizer {
            parameters: MessageParameters(compression_type),
            state: State::Idle,
            data: Vec::new(),
            max_message_bytes: DEFAULT_MAX_MESSAGE_BYTES,
        }
    }

    pub(super) fn set_max_message_bytes(&mut self, max_message_bytes: usize) {
        self.max_message_bytes = max_message_bytes;
    }

    pub(super) fn parameters(&self) -> &super::MessageParameters {
        &self.parameters
    }

    /// Supplies a new packet, delivering any resulting events to `handler`.
    pub(super) fn push(
        &mut self,
        pkt: &ReceivedPacketRef<'_, Ctx>,
        handler: &mut impl MessageHandler<Ctx>,
    ) {
        if !pkt.meta.continuity.is_contiguous() {
            if let State::InProgress { .. } = self.state {
                tracing::debug!(
                    continuity = ?pkt.meta.continuity,
                    "Discarding {}-byte message prefix",
                    self.data.len(),
                );
            }
            self.abandon();
        }
        match &self.state {
            State::InProgress { timestamp, .. }
                if timestamp.timestamp != pkt.meta.timestamp.timestamp =>
            {
                let description = format!(
                    "Timestamp changed from {} to {} with message in progress",
                    timestamp, pkt.meta.timestamp,
                );
                self.abandon();

                // Treat this packet as the start of a new message, below.
                super::report_corrupt(pkt, description, |l| handler.loss(l));
            }
            &State::Skipping { timestamp } => {
                if timestamp == pkt.meta.timestamp.timestamp {
                    if pkt.meta.mark {
                        self.state = State::Idle;
                    }
                    return;
                }
                self.state = State::Idle;
            }
            _ => {}
        }
        let (s1, s2) = pkt.payload().slices();
        if self.data.len() + s1.len() + s2.len() > self.max_message_bytes {
            self.abandon();
            if !pkt.meta.mark {
                self.state = State::Skipping {
                    timestamp: pkt.meta.timestamp.timestamp,
                };
            }
            handler.loss(&super::Loss {
                ctx: &pkt.meta.ctx,
                reason: super::LossReason::TooLarge {
                    limit: self.max_message_bytes,
                },
            });
            return;
        }
        if let State::Idle = self.state {
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
                    data,
                });
                return;
            }
            self.state = State::InProgress {
                ctx: pkt.meta.ctx.clone(),
                timestamp: pkt.meta.timestamp,
            };
        }
        self.data.extend_from_slice(s1);
        self.data.extend_from_slice(s2);
        if pkt.meta.mark {
            let State::InProgress { ctx, timestamp } =
                std::mem::replace(&mut self.state, State::Idle)
            else {
                unreachable!()
            };
            handler.message_frame(&MessageFrameRef {
                ctx: &ctx,
                timestamp,
                data: &self.data,
            });
            self.data.clear();
        }
    }

    /// Discards any in-progress message.
    fn abandon(&mut self) {
        self.state = State::Idle;
        self.data.clear();
    }
}
