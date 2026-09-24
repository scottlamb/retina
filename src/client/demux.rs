// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Items returned by [`super::Demuxed`], and the handler which builds them.

use std::collections::VecDeque;
use std::num::NonZeroU32;

use bytes::Bytes;

use crate::codec::{
    Accumulate, AudioFrameRef, AudioHandler, FrameFormat, Loss, LossReason, MessageFrameRef,
    MessageHandler, VideoFrameEnd, VideoFrameStart, VideoHandler,
};

/// An item yielded from [`crate::client::Demuxed`]'s [`futures::stream::Stream`] impl.
#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CodecItem {
    VideoFrame(VideoFrame),
    AudioFrame(AudioFrame),
    MessageFrame(MessageFrame),
    Rtcp(crate::rtcp::ReceivedCompoundPacket),
}

/// An audio frame, which consists of one or more samples.
#[derive(Eq, PartialEq)]
pub struct AudioFrame {
    pub(crate) ctx: crate::PacketContext,
    pub(crate) stream_id: usize,
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) frame_length: NonZeroU32,
    pub(crate) loss: u16,
    pub(crate) data: Bytes,
}

impl AudioFrame {
    #[inline]
    pub fn ctx(&self) -> &crate::PacketContext {
        &self.ctx
    }

    #[inline]
    pub fn stream_id(&self) -> usize {
        self.stream_id
    }

    #[inline]
    pub fn timestamp(&self) -> crate::Timestamp {
        self.timestamp
    }

    #[inline]
    pub fn frame_length(&self) -> NonZeroU32 {
        self.frame_length
    }

    /// Returns the number of lost RTP packets before this audio frame. See
    /// [crate::client::ReceivedPacket::loss].
    ///
    /// Note that if loss occurs during a fragmented frame, more than this
    /// number of packets' worth of data may be skipped.
    #[inline]
    pub fn loss(&self) -> u16 {
        self.loss
    }

    /// Returns the frame data in a format that depends on the [`FrameFormat`](crate::codec::FrameFormat) set via
    /// [`crate::client::SetupOptions::frame_format`].
    #[inline]
    pub fn data(&self) -> &[u8] {
        &self.data
    }
}

impl std::fmt::Debug for AudioFrame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AudioFrame")
            .field("stream_id", &self.stream_id)
            .field("ctx", &self.ctx)
            .field("loss", &self.loss)
            .field("timestamp", &self.timestamp)
            .field("frame_length", &self.frame_length)
            .field("data", &crate::hex::LimitedHex::new(&self.data, 64))
            .finish()
    }
}

/// A single message, for `application` media types.
#[derive(Eq, PartialEq)]
pub struct MessageFrame {
    pub(crate) ctx: crate::PacketContext,
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) stream_id: usize,
    pub(crate) loss: u16,
    pub(crate) data: Bytes,
}

impl std::fmt::Debug for MessageFrame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AudioFrame")
            .field("ctx", &self.ctx)
            .field("stream_id", &self.stream_id)
            .field("loss", &self.loss)
            .field("timestamp", &self.timestamp)
            .field("data", &crate::hex::LimitedHex::new(&self.data, 64))
            .finish()
    }
}

impl MessageFrame {
    #[inline]
    pub fn ctx(&self) -> &crate::PacketContext {
        &self.ctx
    }

    #[inline]
    pub fn stream_id(&self) -> usize {
        self.stream_id
    }

    #[inline]
    pub fn timestamp(&self) -> crate::Timestamp {
        self.timestamp
    }

    /// Returns the number of lost RTP packets before this frame. See
    /// [crate::client::ReceivedPacket::loss].
    ///
    /// Note that if loss occurs during a fragmented frame, more than this
    /// number of packets' worth of data may be skipped.
    #[inline]
    pub fn loss(&self) -> u16 {
        self.loss
    }

    #[inline]
    pub fn data(&self) -> &[u8] {
        &self.data
    }
}

/// A single video frame (aka video sample or video access unit).
///
/// Typically this is an encoded picture. It could also be a single field of an interlaced
/// picture.
///
/// Durations aren't specified here; they can be calculated from the timestamp of a following
/// picture, or approximated via the frame rate.
#[derive(Eq, PartialEq)]
pub struct VideoFrame {
    // A pair of contexts: for the start and for the end.
    // Having both can be useful to measure the total time elapsed while receiving the frame.
    pub(crate) start_ctx: crate::PacketContext,
    pub(crate) end_ctx: crate::PacketContext,

    pub(crate) has_new_parameters: bool,
    pub(crate) loss: u16,
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) stream_id: usize,
    pub(crate) is_random_access_point: bool,
    pub(crate) is_disposable: bool,
    pub(crate) data: Vec<u8>,
}

impl VideoFrame {
    #[inline]
    pub fn stream_id(&self) -> usize {
        self.stream_id
    }

    /// Returns true if this frame set new video parameters.
    ///
    /// The parameters can be obtained via [`crate::client::Stream::parameters`].
    #[inline]
    pub fn has_new_parameters(&self) -> bool {
        self.has_new_parameters
    }

    /// Returns the number of lost RTP packets before this video frame. See
    /// [`super::ReceivedPacket::loss`].
    ///
    /// Note that if loss occurs during a fragmented frame, more than this
    /// number of packets' worth of data may be skipped.
    #[inline]
    pub fn loss(&self) -> u16 {
        self.loss
    }

    /// Returns this picture's timestamp in the time base associated with the stream.
    #[inline]
    pub fn timestamp(&self) -> crate::Timestamp {
        self.timestamp
    }

    #[inline]
    pub fn start_ctx(&self) -> &crate::PacketContext {
        &self.start_ctx
    }

    #[inline]
    pub fn end_ctx(&self) -> &crate::PacketContext {
        &self.end_ctx
    }

    /// Returns if this is a "random access point (RAP)" aka "instantaneous
    /// decoding refresh (IDR)" picture.
    ///
    /// The former is defined in ISO/IEC 14496-12; the latter in H.264. Both
    /// mean that this picture can be decoded without any other AND no pictures
    /// following this one depend on any pictures before this one.
    #[inline]
    pub fn is_random_access_point(&self) -> bool {
        self.is_random_access_point
    }

    /// Returns if no other pictures require this one to be decoded correctly.
    ///
    /// In H.264 terms, this is a frame with `nal_ref_idc == 0`.
    #[inline]
    pub fn is_disposable(&self) -> bool {
        self.is_disposable
    }

    /// Returns the data in a codec-specific format.
    ///
    /// The framing depends on the [`FrameFormat`](crate::codec::FrameFormat) set via
    /// [`crate::client::SetupOptions::frame_format`]:
    ///
    /// * [`crate::codec::h26x::Framing::FourByteLength`] (default): each NAL is encoded as a
    ///   `u32` length in big-endian format followed by the NAL contents.
    /// * [`crate::codec::h26x::Framing::AnnexB`]: each NAL is preceded by a 4-byte Annex B
    ///   start code (`00 00 00 01`).
    #[inline]
    pub fn data(&self) -> &[u8] {
        &self.data
    }

    #[inline]
    pub fn into_data(self) -> Vec<u8> {
        self.data
    }
}

impl std::fmt::Debug for VideoFrame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        //use pretty_hex::PrettyHex;
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

/// This is similar to `ErrorInt::RtpPacketError`, but without the connection/stream context, to avoid
/// needing to plumb them through the depacketize stack. `Demuxed` will wrap.
///
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct DepacketizeError {
    pub(crate) pkt_ctx: crate::PacketContext,
    pub(crate) ssrc: u32,
    pub(crate) sequence_number: u16,
    pub(crate) description: String,
}

/// Adapts handler events to [`CodecItem`]s, for [`crate::client::Demuxed`].
///
/// Accumulates every frame, queueing it as a [`CodecItem`]. Queues corruption
/// as an error.
pub(crate) struct LegacyHandler<'a> {
    pub(crate) pending: &'a mut VecDeque<Result<CodecItem, DepacketizeError>>,

    /// The packet being pushed.
    pub(crate) meta: &'a crate::rtp::PacketMeta<crate::PacketContext>,

    pub(crate) stream_id: usize,

    pub(crate) format: FrameFormat,
}

impl LegacyHandler<'_> {
    fn corrupt(&mut self, loss: &Loss<'_, crate::PacketContext>) {
        if let LossReason::Corrupt(c) = loss.reason() {
            self.pending.push_back(Err(DepacketizeError {
                pkt_ctx: *loss.ctx(),
                ssrc: self.meta.ssrc,
                sequence_number: self.meta.sequence_number,
                description: c.to_string(),
            }));
        }
    }
}

impl VideoHandler<crate::PacketContext> for LegacyHandler<'_> {
    fn frame_start(
        &mut self,
        _frame_start: &VideoFrameStart<'_, crate::PacketContext>,
    ) -> Accumulate {
        Accumulate::Yes
    }

    fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, crate::PacketContext>) {
        let data = frame_end
            .complete_frame(self.format)
            .expect("frame should be accumulated");
        self.pending.push_back(Ok(CodecItem::VideoFrame(VideoFrame {
            start_ctx: *frame_end.start_ctx(),
            end_ctx: *frame_end.end_ctx(),
            has_new_parameters: frame_end.has_new_parameters(),
            loss: frame_end.loss(),
            timestamp: frame_end.timestamp(),
            stream_id: self.stream_id,
            is_random_access_point: frame_end.is_random_access_point(),
            is_disposable: frame_end.is_disposable(),
            data,
        })));
    }

    fn loss(&mut self, loss: &Loss<'_, crate::PacketContext>) {
        self.corrupt(loss);
    }
}

impl AudioHandler<crate::PacketContext> for LegacyHandler<'_> {
    fn audio_frame(&mut self, frame: &AudioFrameRef<'_, crate::PacketContext>) {
        self.pending.push_back(Ok(CodecItem::AudioFrame(AudioFrame {
            ctx: *frame.ctx(),
            stream_id: self.stream_id,
            timestamp: frame.timestamp(),
            frame_length: frame.frame_length(),
            loss: frame.loss(),
            data: Bytes::copy_from_slice(&frame.data(self.format)),
        })));
    }

    fn loss(&mut self, loss: &Loss<'_, crate::PacketContext>) {
        self.corrupt(loss);
    }
}

impl MessageHandler<crate::PacketContext> for LegacyHandler<'_> {
    fn message_frame(&mut self, frame: &MessageFrameRef<'_, crate::PacketContext>) {
        self.pending
            .push_back(Ok(CodecItem::MessageFrame(MessageFrame {
                ctx: *frame.ctx(),
                stream_id: self.stream_id,
                timestamp: frame.timestamp(),
                loss: frame.loss(),
                data: Bytes::copy_from_slice(frame.data()),
            })));
    }

    fn loss(&mut self, loss: &Loss<'_, crate::PacketContext>) {
        self.corrupt(loss);
    }
}
