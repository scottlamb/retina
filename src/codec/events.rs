// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Push-through depacketization: the [`Handler`] trait and the events it receives.
//!
//! A depacketizer is fed one RTP packet at a time and calls back into a
//! caller-supplied [`Handler`] as frames begin, as their data arrives, and as
//! they end. Handlers are generic parameters, so methods left at their default
//! (empty) implementations compile to nothing.
//!
//! Video frames produce this sequence of events:
//!
//! 1. [`Handler::frame_start`] exactly once. The handler decides whether the
//!    depacketizer should retain the frame's data until the end
//!    ([`Accumulate::Yes`]) or only stream it ([`Accumulate::No`]).
//! 2. [`Handler::data`] zero or more times, with *unframed* codec units (e.g.
//!    H.264 NAL units), in order.
//! 3. [`Handler::frame_end`] exactly once, unless [`Handler::loss`] intervenes.
//!    If the handler requested accumulation, [`FrameEnd::complete_frame`] or
//!    [`FrameEnd::visit_frame_data`] provide the whole frame with the requested
//!    [`FrameFormat`].
//!
//! Audio and message streams instead produce one [`Handler::audio_frame`] or
//! [`Handler::message_frame`] per frame.
//!
//! `Ctx` is a caller-chosen packet context type, supplied with each packet and
//! handed back with the events it contributed to. Within a [`crate::client`]
//! session it's [`crate::PacketContext`]; a caller depacketizing from a capture
//! file might use a file offset or capture timestamp instead.

#![allow(dead_code)] // TODO: remove when this is public API.

use std::num::NonZeroU32;

use super::{FrameFormat, ParametersRef};

/// Receives depacketization events.
///
/// See the [module-level documentation](self) for the sequence of calls.
pub trait Handler<Ctx> {
    /// A new video frame (access unit) has begun.
    ///
    /// The depacketizer calls this as early as it can determine the frame's
    /// basic properties, which may be before all of its packets have arrived.
    /// The values here are therefore the best knowledge so far; the values on
    /// [`FrameEnd`] are authoritative.
    ///
    /// Return [`Accumulate::Yes`] to have the depacketizer retain the frame's
    /// data for [`FrameEnd::complete_frame`]. [`Handler::data`] events are
    /// delivered either way.
    fn frame_start(&mut self, frame_start: &FrameStart<'_, Ctx>) -> Accumulate;

    /// A chunk of unframed codec unit data. See [`Data`].
    fn data(&mut self, _data: &Data<'_>) {}

    /// The video frame begun by the last [`Handler::frame_start`] is complete.
    fn frame_end(&mut self, _frame_end: &mut FrameEnd<'_, Ctx>) {}

    /// Packets were lost or data was corrupt.
    ///
    /// If a video frame was in progress (`frame_start` was called without a
    /// matching `frame_end`), it has been abandoned: no `frame_end` will follow
    /// for it.
    fn loss(&mut self, _loss: &Loss<'_, Ctx>) {}

    /// A complete audio frame.
    fn audio_frame(&mut self, _frame: &AudioFrameRef<'_, Ctx>) {}

    /// A complete message, for `application` media types.
    fn message_frame(&mut self, _frame: &MessageFrameRef<'_, Ctx>) {}
}

impl<Ctx, H: Handler<Ctx> + ?Sized> Handler<Ctx> for &mut H {
    #[inline]
    fn frame_start(&mut self, frame_start: &FrameStart<'_, Ctx>) -> Accumulate {
        (**self).frame_start(frame_start)
    }

    #[inline]
    fn data(&mut self, data: &Data<'_>) {
        (**self).data(data)
    }

    #[inline]
    fn frame_end(&mut self, frame_end: &mut FrameEnd<'_, Ctx>) {
        (**self).frame_end(frame_end)
    }

    #[inline]
    fn loss(&mut self, loss: &Loss<'_, Ctx>) {
        (**self).loss(loss)
    }

    #[inline]
    fn audio_frame(&mut self, frame: &AudioFrameRef<'_, Ctx>) {
        (**self).audio_frame(frame)
    }

    #[inline]
    fn message_frame(&mut self, frame: &MessageFrameRef<'_, Ctx>) {
        (**self).message_frame(frame)
    }
}

/// Whether the depacketizer should retain a video frame's data until its end.
///
/// Returned from [`Handler::frame_start`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Accumulate {
    /// Retain the frame, so that [`FrameEnd::complete_frame`] and
    /// [`FrameEnd::visit_frame_data`] can supply it.
    Yes,

    /// Don't retain the frame. The handler sees its data only via
    /// [`Handler::data`], and the depacketizer releases buffer space as soon as
    /// each chunk has been delivered.
    No,
}

/// Information about a video frame that has just begun.
///
/// Passed to [`Handler::frame_start`]. Values are the best knowledge so far;
/// see [`FrameEnd`] for authoritative values.
pub struct FrameStart<'a, Ctx> {
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) ctx: &'a Ctx,
    pub(crate) loss: u16,
    pub(crate) is_random_access_point: bool,
    pub(crate) is_disposable: bool,
    pub(crate) has_new_parameters: bool,
    pub(crate) parameters: Option<ParametersRef<'a>>,
}

impl<Ctx> FrameStart<'_, Ctx> {
    /// Returns the frame's timestamp.
    #[inline]
    pub fn timestamp(&self) -> crate::Timestamp {
        self.timestamp
    }

    /// Returns the context of the first packet contributing to this frame.
    #[inline]
    pub fn ctx(&self) -> &Ctx {
        self.ctx
    }

    /// Returns the number of lost RTP packets before this frame.
    #[inline]
    pub fn loss(&self) -> u16 {
        self.loss
    }

    /// Returns if this frame appears to be a random access point.
    ///
    /// See [`FrameEnd::is_random_access_point`].
    #[inline]
    pub fn is_random_access_point(&self) -> bool {
        self.is_random_access_point
    }

    /// Returns if this frame appears to be disposable.
    ///
    /// See [`FrameEnd::is_disposable`].
    #[inline]
    pub fn is_disposable(&self) -> bool {
        self.is_disposable
    }

    /// Returns if this frame appears to set new parameters.
    ///
    /// See [`FrameEnd::has_new_parameters`].
    #[inline]
    pub fn has_new_parameters(&self) -> bool {
        self.has_new_parameters
    }

    /// Returns the parameters in effect for this frame, if known.
    ///
    /// If [`FrameStart::has_new_parameters`] is true, these are the new
    /// parameters. [`super::Depacketizer::parameters`] doesn't reflect them
    /// until the frame ends.
    #[inline]
    pub fn parameters(&self) -> Option<ParametersRef<'_>> {
        self.parameters.clone()
    }
}

/// A chunk of unframed codec unit data, passed to [`Handler::data`].
///
/// "Unframed" means that no length prefix, Annex B start code, or other
/// container framing is applied. [`Data::position`] says where this chunk falls
/// within its codec unit so the handler can apply its own framing. For example:
///
/// * For Annex B output, write `00 00 00 01` before each
///   [`UnitPosition::Complete`] or [`UnitPosition::Start`] chunk.
/// * For length-prefixed output, buffer the unit until a
///   [`UnitPosition::Complete`] or [`UnitPosition::End`] chunk, then write its
///   length and contents.
///
/// For [`UnitPosition::Complete`] and [`UnitPosition::Start`], the data begins
/// with the codec unit's header (e.g. the H.264 NAL header byte).
///
/// H.264 and H.265 parameter set NAL units (VPS, SPS, PPS) are omitted. They
/// are instead reflected in the stream's parameters; see
/// [`FrameStart::has_new_parameters`].
#[derive(Debug)]
pub struct Data<'a> {
    /// The position of this chunk within its codec unit.
    pub position: UnitPosition,

    /// The chunk's bytes, as a sequence of slices to be concatenated.
    ///
    /// The slices refer directly to the depacketizer's input buffer. Some may
    /// be empty.
    pub data: &'a [&'a [u8]],
}

impl Data<'_> {
    /// Returns the total length of [`Data::data`] in bytes.
    #[inline]
    pub fn len(&self) -> usize {
        self.data.iter().map(|d| d.len()).sum()
    }

    /// Returns true if [`Data::data`] is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.iter().all(|d| d.is_empty())
    }
}

/// The position of a [`Data`] chunk within its codec unit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnitPosition {
    /// The entire unit, in one chunk.
    Complete,

    /// The first chunk of a unit that continues in later chunks.
    Start,

    /// An interior chunk of a unit.
    Middle,

    /// The final chunk of a unit. May be empty.
    End,
}

impl UnitPosition {
    /// Returns the position of a chunk given whether it's the first and/or last chunk.
    #[inline]
    pub(crate) fn new(first: bool, last: bool) -> Self {
        match (first, last) {
            (true, true) => UnitPosition::Complete,
            (true, false) => UnitPosition::Start,
            (false, false) => UnitPosition::Middle,
            (false, true) => UnitPosition::End,
        }
    }

    /// Returns true if this chunk begins its unit.
    #[inline]
    pub fn is_first(self) -> bool {
        matches!(self, UnitPosition::Complete | UnitPosition::Start)
    }

    /// Returns true if this chunk ends its unit.
    #[inline]
    pub fn is_last(self) -> bool {
        matches!(self, UnitPosition::Complete | UnitPosition::End)
    }
}

/// Information about a video frame that has just ended.
///
/// Passed to [`Handler::frame_end`].
pub struct FrameEnd<'a, Ctx> {
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) start_ctx: &'a Ctx,
    pub(crate) end_ctx: &'a Ctx,
    pub(crate) loss: u16,
    pub(crate) is_random_access_point: bool,
    pub(crate) is_disposable: bool,
    pub(crate) has_new_parameters: bool,
    pub(crate) body: FrameBody<'a>,
}

/// Codec-specific access to a frame's accumulated data and parameters.
pub(crate) enum FrameBody<'a> {
    #[cfg(feature = "h264")]
    H264(super::h264::FrameEndBody<'a>),
    #[cfg(feature = "h265")]
    H265(super::h265::FrameEndBody<'a>),

    /// Uninhabited; keeps `'a` in use when no codec is enabled.
    #[cfg(not(any(feature = "h264", feature = "h265")))]
    Never(std::convert::Infallible, std::marker::PhantomData<&'a ()>),
}

// Without H.264 or H.265, there are no frame bodies.
#[cfg_attr(
    not(any(feature = "h264", feature = "h265")),
    allow(unused_variables, unreachable_code)
)]
impl<Ctx> FrameEnd<'_, Ctx> {
    /// Returns the frame's timestamp.
    #[inline]
    pub fn timestamp(&self) -> crate::Timestamp {
        self.timestamp
    }

    /// Returns the context of the first packet contributing to this frame.
    #[inline]
    pub fn start_ctx(&self) -> &Ctx {
        self.start_ctx
    }

    /// Returns the context of the packet which completed this frame.
    ///
    /// Having both start and end contexts can be useful to measure the total
    /// time elapsed while receiving the frame.
    #[inline]
    pub fn end_ctx(&self) -> &Ctx {
        self.end_ctx
    }

    /// Returns the number of lost RTP packets before this frame.
    ///
    /// Note that if loss occurs during a fragmented frame, more than this
    /// number of packets' worth of data may be skipped.
    #[inline]
    pub fn loss(&self) -> u16 {
        self.loss
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

    /// Returns true if this frame set new video parameters.
    #[inline]
    pub fn has_new_parameters(&self) -> bool {
        self.has_new_parameters
    }

    /// Returns the parameters in effect for this frame, if known.
    pub fn parameters(&self) -> Option<ParametersRef<'_>> {
        match &self.body {
            #[cfg(feature = "h264")]
            FrameBody::H264(b) => b.parameters(),
            #[cfg(feature = "h265")]
            FrameBody::H265(b) => b.parameters(),
            #[cfg(not(any(feature = "h264", feature = "h265")))]
            FrameBody::Never(n, _) => match *n {},
        }
    }

    /// Returns the length in bytes that [`FrameEnd::complete_frame`] would
    /// produce with the given format, or `None` if the frame wasn't accumulated.
    pub fn data_len(&self, format: FrameFormat) -> Option<usize> {
        match &self.body {
            #[cfg(feature = "h264")]
            FrameBody::H264(b) => b.data_len(format),
            #[cfg(feature = "h265")]
            FrameBody::H265(b) => b.data_len(format),
            #[cfg(not(any(feature = "h264", feature = "h265")))]
            FrameBody::Never(n, _) => match *n {},
        }
    }

    /// Returns the accumulated frame data in the given format.
    ///
    /// Returns `None` if [`Handler::frame_start`] didn't return
    /// [`Accumulate::Yes`] or if this has already been called for this frame.
    pub fn complete_frame(&mut self, format: FrameFormat) -> Option<CompleteFrame> {
        let data: Option<Vec<u8>> = match &mut self.body {
            #[cfg(feature = "h264")]
            FrameBody::H264(b) => b.build(format),
            #[cfg(feature = "h265")]
            FrameBody::H265(b) => b.build(format),
            #[cfg(not(any(feature = "h264", feature = "h265")))]
            FrameBody::Never(n, _) => match *n {},
        };
        data.map(|data| CompleteFrame { data })
    }

    /// Visits the accumulated frame data in the given format without
    /// allocating, calling `visitor` for each contiguous chunk in order.
    ///
    /// Returns false (without calling `visitor`) if the frame wasn't
    /// accumulated or [`FrameEnd::complete_frame`] has already been called.
    pub fn visit_frame_data(&self, format: FrameFormat, visitor: &mut impl FnMut(&[u8])) -> bool {
        match &self.body {
            #[cfg(feature = "h264")]
            FrameBody::H264(b) => b.visit(format, visitor),
            #[cfg(feature = "h265")]
            FrameBody::H265(b) => b.visit(format, visitor),
            #[cfg(not(any(feature = "h264", feature = "h265")))]
            FrameBody::Never(n, _) => match *n {},
        }
    }
}

/// A complete, framed video frame, as returned by [`FrameEnd::complete_frame`].
#[derive(Clone, PartialEq, Eq)]
pub struct CompleteFrame {
    data: Vec<u8>,
}

impl CompleteFrame {
    /// Returns the frame data.
    #[inline]
    pub fn data(&self) -> &[u8] {
        &self.data
    }

    /// Returns the frame data as an owned vector.
    #[inline]
    pub fn into_data(self) -> Vec<u8> {
        self.data
    }
}

impl std::fmt::Debug for CompleteFrame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompleteFrame")
            .field("data", &crate::hex::LimitedHex::new(&self.data, 64))
            .finish()
    }
}

/// Notice of lost or corrupt data, passed to [`Handler::loss`].
pub struct Loss<'a, Ctx> {
    pub(crate) ctx: &'a Ctx,
    pub(crate) reason: LossReason,
}

impl<Ctx> Loss<'_, Ctx> {
    /// Returns the context of the packet which revealed the loss.
    #[inline]
    pub fn ctx(&self) -> &Ctx {
        self.ctx
    }

    /// Returns the reason for the loss.
    #[inline]
    pub fn reason(&self) -> &LossReason {
        &self.reason
    }
}

/// The reason for a [`Loss`].
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum LossReason {
    /// RTP packets were lost, as indicated by a gap in sequence numbers.
    PacketLoss {
        /// The number of lost packets.
        packets: u16,
    },

    /// The depacketizer detected corrupt data or a protocol violation.
    ///
    /// It discards any in-progress frame and resynchronizes at the next frame
    /// boundary.
    Corrupt {
        /// A human-readable description of the problem.
        description: String,
    },
}

/// A complete audio frame, passed to [`Handler::audio_frame`].
pub struct AudioFrameRef<'a, Ctx> {
    pub(crate) ctx: &'a Ctx,
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) frame_length: NonZeroU32,
    pub(crate) loss: u16,
    pub(crate) data: &'a [u8],
}

impl<Ctx> AudioFrameRef<'_, Ctx> {
    /// Returns the context of the packet containing this frame.
    #[inline]
    pub fn ctx(&self) -> &Ctx {
        self.ctx
    }

    /// Returns the frame's timestamp.
    #[inline]
    pub fn timestamp(&self) -> crate::Timestamp {
        self.timestamp
    }

    /// Returns the frame's length in clock rate units.
    #[inline]
    pub fn frame_length(&self) -> NonZeroU32 {
        self.frame_length
    }

    /// Returns the number of lost RTP packets before this frame.
    #[inline]
    pub fn loss(&self) -> u16 {
        self.loss
    }

    /// Returns the frame data, in a format that depends on the depacketizer's
    /// [`FrameFormat`].
    #[inline]
    pub fn data(&self) -> &[u8] {
        self.data
    }
}

/// A complete message, passed to [`Handler::message_frame`].
pub struct MessageFrameRef<'a, Ctx> {
    pub(crate) ctx: &'a Ctx,
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) loss: u16,
    pub(crate) data: &'a [u8],
}

impl<Ctx> MessageFrameRef<'_, Ctx> {
    /// Returns the context of the packet which started this message.
    #[inline]
    pub fn ctx(&self) -> &Ctx {
        self.ctx
    }

    /// Returns the message's timestamp.
    #[inline]
    pub fn timestamp(&self) -> crate::Timestamp {
        self.timestamp
    }

    /// Returns the number of lost RTP packets before this message.
    #[inline]
    pub fn loss(&self) -> u16 {
        self.loss
    }

    /// Returns the message data.
    #[inline]
    pub fn data(&self) -> &[u8] {
        self.data
    }
}

/// A [`Handler`] which records events, for tests.
#[cfg(test)]
pub(crate) mod testutil {
    use super::*;

    /// A recorded event, with data flattened for easy comparison.
    #[derive(Debug, PartialEq, Eq)]
    pub(crate) enum Event {
        FrameStart {
            loss: u16,
            is_random_access_point: bool,
            is_disposable: bool,
            has_new_parameters: bool,
        },
        Data(UnitPosition, crate::testutil::HexDebug),
        FrameEnd {
            loss: u16,
            is_random_access_point: bool,
            is_disposable: bool,
            has_new_parameters: bool,

            /// The accumulated frame, if any, in the recorder's format.
            data: Option<crate::testutil::HexDebug>,
        },
        Loss(LossReason),
        AudioFrame(crate::testutil::HexDebug),
        MessageFrame(crate::testutil::HexDebug),
    }

    pub(crate) struct Recorder {
        pub(crate) events: Vec<Event>,
        pub(crate) accumulate: Accumulate,
        pub(crate) format: FrameFormat,

        /// The current frame as reassembled from `data` events, with 4-byte
        /// length prefixes, for comparison with the accumulated frame.
        streamed: Vec<u8>,

        /// The start of the current unit within `streamed`, if one is in progress.
        unit_start: Option<usize>,
    }

    impl Recorder {
        pub(crate) fn new(accumulate: Accumulate) -> Self {
            Self {
                events: Vec::new(),
                accumulate,
                format: FrameFormat::MP4,
                streamed: Vec::new(),
                unit_start: None,
            }
        }

        pub(crate) fn take(&mut self) -> Vec<Event> {
            std::mem::take(&mut self.events)
        }
    }

    pub(crate) fn hex(data: &[u8]) -> crate::testutil::HexDebug {
        crate::testutil::HexDebug(data.to_vec())
    }

    impl<Ctx> Handler<Ctx> for Recorder {
        fn frame_start(&mut self, frame_start: &FrameStart<'_, Ctx>) -> Accumulate {
            self.events.push(Event::FrameStart {
                loss: frame_start.loss(),
                is_random_access_point: frame_start.is_random_access_point(),
                is_disposable: frame_start.is_disposable(),
                has_new_parameters: frame_start.has_new_parameters(),
            });
            self.streamed.clear();
            self.unit_start = None;
            self.accumulate
        }

        fn data(&mut self, data: &Data<'_>) {
            let flat = data.data.concat();
            assert_eq!(flat.len(), data.len());
            assert_eq!(data.position.is_first(), self.unit_start.is_none());
            if data.position.is_first() {
                self.unit_start = Some(self.streamed.len());
                self.streamed.extend_from_slice(&[0; 4]);
            }
            self.streamed.extend_from_slice(&flat);
            if data.position.is_last() {
                let start = self.unit_start.take().unwrap();
                let len = u32::try_from(self.streamed.len() - start - 4).unwrap();
                self.streamed[start..start + 4].copy_from_slice(&len.to_be_bytes());
            }
            self.events
                .push(Event::Data(data.position, crate::testutil::HexDebug(flat)));
        }

        fn frame_end(&mut self, frame_end: &mut FrameEnd<'_, Ctx>) {
            let len = frame_end.data_len(self.format);
            let mut visited = Vec::new();
            let visited_ok =
                frame_end.visit_frame_data(self.format, &mut |c| visited.extend_from_slice(c));
            let data = frame_end.complete_frame(self.format).map(|f| f.into_data());
            assert_eq!(len.is_some(), visited_ok);
            assert_eq!(len, data.as_ref().map(Vec::len));
            if let Some(d) = data.as_ref() {
                assert_eq!(&visited, d);
            }
            assert!(frame_end.complete_frame(self.format).is_none());
            assert!(self.unit_start.is_none(), "frame ended mid-unit");
            if self.format == FrameFormat::MP4
                && let Some(d) = data.as_ref()
            {
                assert_eq!(
                    crate::testutil::HexDebug(self.streamed.clone()),
                    crate::testutil::HexDebug(d.clone()),
                    "streamed data should match accumulated frame"
                );
            }
            self.events.push(Event::FrameEnd {
                loss: frame_end.loss(),
                is_random_access_point: frame_end.is_random_access_point(),
                is_disposable: frame_end.is_disposable(),
                has_new_parameters: frame_end.has_new_parameters(),
                data: data.map(crate::testutil::HexDebug),
            });
        }

        fn loss(&mut self, loss: &Loss<'_, Ctx>) {
            self.unit_start = None;
            self.events.push(Event::Loss(loss.reason().clone()));
        }

        fn audio_frame(&mut self, frame: &AudioFrameRef<'_, Ctx>) {
            self.events.push(Event::AudioFrame(hex(frame.data())));
        }

        fn message_frame(&mut self, frame: &MessageFrameRef<'_, Ctx>) {
            self.events.push(Event::MessageFrame(hex(frame.data())));
        }
    }
}
