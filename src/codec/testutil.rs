// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! A test harness which accumulates each frame, for tests which examine a
//! single codec's depacketizer frame by frame.

use std::collections::VecDeque;
use std::num::NonZeroU32;

use super::{
    Accumulate, AudioFrameRef, AudioHandler, FrameFormat, Loss, LossReason, MessageFrameRef,
    MessageHandler, VideoFrameEnd, VideoFrameStart, VideoHandler,
};
use crate::PacketContext;
use crate::rtp::ReceivedPacketRef;

/// Frames and errors from a depacketizer, in order.
#[derive(Debug, Default)]
pub(crate) struct Pending {
    items: VecDeque<Result<Item, String>>,

    /// Packets lost since the previous frame.
    loss: u16,
}

impl Pending {
    /// Supplies `pkt` to a codec's depacketizer via `push`, first reporting
    /// packet loss as the public depacketizers do.
    ///
    /// Panics if items from a previous packet haven't been pulled.
    pub(crate) fn push(
        &mut self,
        pkt: &ReceivedPacketRef<'_, PacketContext>,
        format: FrameFormat,
        push: impl FnOnce(&mut Collector<'_>),
    ) {
        if let Some(i) = self.items.front() {
            panic!("push with data already pending: {i:?}");
        }
        let mut c = Collector::new(self, format);
        super::report_packet_loss(pkt, |l| c.on_loss(l));
        push(&mut c);
    }

    /// Supplies a packet to a codec's depacketizer which reports packet loss
    /// itself, as the H.264 and H.265 depacketizers do.
    ///
    /// Panics if items from a previous packet haven't been pulled.
    #[cfg_attr(not(any(feature = "h264", feature = "h265")), allow(dead_code))]
    pub(crate) fn push_reporting_loss(
        &mut self,
        format: FrameFormat,
        push: impl FnOnce(&mut Collector<'_>),
    ) {
        if let Some(i) = self.items.front() {
            panic!("push with data already pending: {i:?}");
        }
        push(&mut Collector::new(self, format));
    }

    pub(crate) fn pull(&mut self) -> Option<Result<Item, String>> {
        self.items.pop_front()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Item {
    Video(VideoFrame),
    Audio(AudioFrame),
    Message(MessageFrame),
}

#[derive(PartialEq, Eq)]
pub(crate) struct VideoFrame {
    pub(crate) start_ctx: PacketContext,
    pub(crate) end_ctx: PacketContext,
    pub(crate) has_new_parameters: bool,
    pub(crate) loss: u16,
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) is_random_access_point: bool,
    pub(crate) is_disposable: bool,
    pub(crate) data: Vec<u8>,
}

#[cfg_attr(not(feature = "h264"), allow(dead_code))]
impl VideoFrame {
    pub(crate) fn is_random_access_point(&self) -> bool {
        self.is_random_access_point
    }

    pub(crate) fn data(&self) -> &[u8] {
        &self.data
    }

    pub(crate) fn into_data(self) -> Vec<u8> {
        self.data
    }
}

impl std::fmt::Debug for VideoFrame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VideoFrame")
            .field("timestamp", &self.timestamp)
            .field("start_ctx", &self.start_ctx)
            .field("end_ctx", &self.end_ctx)
            .field("loss", &self.loss)
            .field("has_new_parameters", &self.has_new_parameters)
            .field("is_random_access_point", &self.is_random_access_point)
            .field("is_disposable", &self.is_disposable)
            .field("data", &crate::hex::LimitedHex::new(&self.data, 64))
            .finish()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct AudioFrame {
    pub(crate) ctx: PacketContext,
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) frame_length: NonZeroU32,
    pub(crate) loss: u16,
    pub(crate) data: Vec<u8>,
}

#[cfg_attr(not(feature = "h264"), allow(dead_code))]
impl AudioFrame {
    pub(crate) fn data(&self) -> &[u8] {
        &self.data
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct MessageFrame {
    pub(crate) ctx: PacketContext,
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) loss: u16,
    pub(crate) data: Vec<u8>,
}

/// Accumulates each frame as an [`Item`], queueing corruption as an error.
pub(crate) struct Collector<'a> {
    pending: &'a mut Pending,
    format: FrameFormat,
}

impl<'a> Collector<'a> {
    pub(crate) fn new(pending: &'a mut Pending, format: FrameFormat) -> Self {
        Self { pending, format }
    }

    fn on_loss(&mut self, loss: &Loss<'_, PacketContext>) {
        match loss.reason() {
            LossReason::PacketLoss { packets } => self.pending.loss += packets,
            LossReason::Corrupt(c) => self.pending.items.push_back(Err(c.to_string())),
        }
    }

    fn push(&mut self, item: impl FnOnce(u16) -> Item) {
        let loss = std::mem::take(&mut self.pending.loss);
        self.pending.items.push_back(Ok(item(loss)));
    }
}

impl VideoHandler<PacketContext> for Collector<'_> {
    fn frame_start(&mut self, _frame_start: &mut VideoFrameStart<'_, PacketContext>) -> Accumulate {
        Accumulate::Yes
    }

    fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, PacketContext>) {
        let data = frame_end
            .complete_frame(self.format)
            .expect("frame should be accumulated");
        self.push(|loss| {
            Item::Video(VideoFrame {
                start_ctx: *frame_end.start_ctx(),
                end_ctx: *frame_end.end_ctx(),
                has_new_parameters: frame_end.has_new_parameters(),
                loss,
                timestamp: frame_end.timestamp(),
                is_random_access_point: frame_end.is_random_access_point(),
                is_disposable: frame_end.is_disposable(),
                data,
            })
        });
    }

    fn loss(&mut self, loss: &Loss<'_, PacketContext>) {
        self.on_loss(loss);
    }
}

impl AudioHandler<PacketContext> for Collector<'_> {
    fn audio_frame(&mut self, frame: &AudioFrameRef<'_, PacketContext>) {
        let data = frame.data(self.format).into_owned();
        self.push(|loss| {
            Item::Audio(AudioFrame {
                ctx: *frame.ctx(),
                timestamp: frame.timestamp(),
                frame_length: frame.frame_length(),
                loss,
                data,
            })
        });
    }

    fn loss(&mut self, loss: &Loss<'_, PacketContext>) {
        self.on_loss(loss);
    }
}

impl MessageHandler<PacketContext> for Collector<'_> {
    fn message_frame(&mut self, frame: &MessageFrameRef<'_, PacketContext>) {
        self.push(|loss| {
            Item::Message(MessageFrame {
                ctx: *frame.ctx(),
                timestamp: frame.timestamp(),
                loss,
                data: frame.data().to_vec(),
            })
        });
    }

    fn loss(&mut self, loss: &Loss<'_, PacketContext>) {
        self.on_loss(loss);
    }
}
