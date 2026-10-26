// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Whole-frame demuxing, similar to Retina 0.4's `Demuxed`.
//!
//! Retina's depacketizers deliver events to a handler, which can stream video
//! frames as packets arrive. This instead accumulates each frame into a
//! `Vec<u8>`, which is simplest when frames go somewhere that wants them whole,
//! such as an `.mp4` file. It's meant to be copied and adapted.

use std::{collections::VecDeque, sync::Arc};

use anyhow::{Error, anyhow};
use retina::PacketContext;
use retina::client::{Playing, PlayingItem, Session};
use retina::codec::{
    Accumulate, AudioFrameRef, AudioHandler, Depacketizer, FrameFormat, Loss, LossReason,
    MessageFrameRef, MessageHandler, VideoFrameEnd, VideoFrameStart, VideoHandler, VideoParameters,
};
use tracing::warn;

/// A frame or RTCP packet, as returned by [`Demuxer::next`].
pub enum Item {
    Video(VideoFrame),
    Audio(Frame),
    Message(Frame),
    Rtcp(retina::rtcp::ReceivedCompoundPacket),
}

#[allow(dead_code)] // not every example uses every field.
pub struct VideoFrame {
    pub stream_id: usize,
    pub timestamp: retina::Timestamp,
    pub start_ctx: PacketContext,

    /// Packets lost (plus instances of corrupt data) since the stream's previous frame.
    pub loss: u16,
    pub is_random_access_point: bool,
    pub has_new_parameters: bool,

    /// The parameters in effect for this frame, if known.
    pub parameters: Option<Arc<VideoParameters>>,
    pub data: Vec<u8>,
}

/// An audio frame or message.
#[allow(dead_code)]
pub struct Frame {
    pub stream_id: usize,
    pub timestamp: retina::Timestamp,
    pub ctx: PacketContext,

    /// As in [`VideoFrame::loss`].
    pub loss: u16,
    pub data: Vec<u8>,
}

/// Demuxes a playing session's streams into whole frames.
pub struct Demuxer {
    streams: Vec<Option<Stream>>,
    format: FrameFormat,
    pending: VecDeque<Item>,
}

struct Stream {
    depacketizer: Depacketizer<PacketContext>,
    loss: u16,
    parameters: Option<Arc<VideoParameters>>,
}

impl Demuxer {
    /// Creates a depacketizer for each of `session`'s set-up streams.
    pub fn new(session: &Session<Playing>, format: FrameFormat) -> Result<Self, Error> {
        let streams = session
            .streams()
            .iter()
            .enumerate()
            .map(|(i, s)| {
                if !s.is_setup() {
                    return Ok(None);
                }
                let depacketizer = s
                    .new_depacketizer()
                    .map_err(|e| anyhow!("can't depacketize stream {i}: {e}"))?;
                Ok(Some(Stream {
                    depacketizer,
                    loss: 0,
                    parameters: None,
                }))
            })
            .collect::<Result<_, Error>>()?;
        Ok(Self {
            streams,
            format,
            pending: VecDeque::new(),
        })
    }

    /// Returns the next item, or `None` at the end of the session.
    ///
    /// This is cancel safe, e.g. within `tokio::select!`.
    pub async fn next(&mut self, session: &mut Session<Playing>) -> Result<Option<Item>, Error> {
        loop {
            if let Some(item) = self.pending.pop_front() {
                return Ok(Some(item));
            }
            let Some(item) = session.next_item().await.transpose()? else {
                return Ok(None);
            };
            match item {
                PlayingItem::Rtp(pkt) => {
                    let stream_id = pkt.stream_id();
                    let stream = self.streams[stream_id]
                        .as_mut()
                        .expect("only set-up streams have packets");
                    let h = &mut Handler {
                        stream_id,
                        format: self.format,
                        loss: &mut stream.loss,
                        parameters: &mut stream.parameters,
                        pending: &mut self.pending,
                    };
                    match &mut stream.depacketizer {
                        Depacketizer::Video(d) => d.push(pkt.packet(), h),
                        Depacketizer::Audio(d) => d.push(pkt.packet(), h),
                        Depacketizer::Message(d) => d.push(pkt.packet(), h),
                        _ => {} // a media type this example doesn't know about.
                    }
                }
                PlayingItem::Rtcp(pkt) => return Ok(Some(Item::Rtcp(pkt))),
                _ => {}
            }
        }
    }
}

/// Queues each frame of a single packet as an [`Item`].
struct Handler<'a> {
    stream_id: usize,
    format: FrameFormat,
    loss: &'a mut u16,
    parameters: &'a mut Option<Arc<VideoParameters>>,
    pending: &'a mut VecDeque<Item>,
}

impl Handler<'_> {
    fn loss(&mut self, loss: &Loss<'_, PacketContext>) {
        let n = match loss.reason() {
            LossReason::PacketLoss { packets, .. } => *packets,
            r => {
                warn!(stream = self.stream_id, reason = ?r, "loss");
                1
            }
        };
        *self.loss = self.loss.saturating_add(n);
    }

    fn frame(&mut self, ctx: &PacketContext, timestamp: retina::Timestamp, data: Vec<u8>) -> Frame {
        Frame {
            stream_id: self.stream_id,
            timestamp,
            ctx: *ctx,
            loss: std::mem::take(self.loss),
            data,
        }
    }
}

impl VideoHandler<PacketContext> for Handler<'_> {
    fn frame_start(&mut self, _frame_start: &mut VideoFrameStart<'_, PacketContext>) -> Accumulate {
        Accumulate::Yes
    }

    fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, PacketContext>) {
        if frame_end.has_new_parameters() || self.parameters.is_none() {
            *self.parameters = frame_end.parameters().cloned().map(Arc::new);
        }
        let data = frame_end
            .complete_frame(self.format)
            .expect("frame_start requested accumulation");
        self.pending.push_back(Item::Video(VideoFrame {
            stream_id: self.stream_id,
            timestamp: frame_end.timestamp(),
            start_ctx: *frame_end.start_ctx(),
            loss: std::mem::take(self.loss),
            is_random_access_point: frame_end.is_random_access_point(),
            has_new_parameters: frame_end.has_new_parameters(),
            parameters: self.parameters.clone(),
            data,
        }));
    }

    fn loss(&mut self, loss: &Loss<'_, PacketContext>) {
        Handler::loss(self, loss);
    }
}

impl AudioHandler<PacketContext> for Handler<'_> {
    fn audio_frame(&mut self, frame: &AudioFrameRef<'_, PacketContext>) {
        let data = frame.data(self.format).into_owned();
        let frame = self.frame(frame.ctx(), frame.timestamp(), data);
        self.pending.push_back(Item::Audio(frame));
    }

    fn loss(&mut self, loss: &Loss<'_, PacketContext>) {
        Handler::loss(self, loss);
    }
}

impl MessageHandler<PacketContext> for Handler<'_> {
    fn message_frame(&mut self, frame: &MessageFrameRef<'_, PacketContext>) {
        let data = frame.data().to_vec();
        let frame = self.frame(frame.ctx(), frame.timestamp(), data);
        self.pending.push_back(Item::Message(frame));
    }

    fn loss(&mut self, loss: &Loss<'_, PacketContext>) {
        Handler::loss(self, loss);
    }
}
