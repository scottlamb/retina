// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Push-through depacketization: the [`Handler`] trait and the events it receives.
//!
//! See [`Handler`].

use std::num::NonZeroU32;

use super::{FrameFormat, VideoParameters};

/// Receives video depacketization events from a [`super::VideoDepacketizer`].
///
/// A depacketizer is fed one RTP packet at a time and calls back into a
/// caller-supplied handler as frames begin, as their data arrives, and as
/// they end. Handlers are generic parameters, so methods left at their default
/// (empty) implementations compile to nothing.
///
/// Each frame produces this sequence of events:
///
/// 1. [`VideoHandler::frame_start`] exactly once. The handler decides whether
///    the depacketizer should retain the frame's data until the end
///    ([`Accumulate::Yes`]) or only stream it ([`Accumulate::No`]).
/// 2. [`VideoHandler::data`] zero or more times, with *unframed* codec units
///    (e.g. H.264 NAL units), in order.
/// 3. [`VideoHandler::frame_end`] exactly once, unless [`VideoHandler::loss`]
///    intervenes. If the handler requested accumulation,
///    [`VideoFrameEnd::complete_frame`] or [`VideoFrameEnd::visit_frame_data`]
///    provide the whole frame with the requested [`FrameFormat`].
///
/// `Ctx` is a caller-chosen packet context type, supplied with each packet and
/// handed back with the events it contributed to. Within a [`crate::client`]
/// session it's [`crate::PacketContext`]; a caller depacketizing from a capture
/// file might use a file offset or capture timestamp instead.
pub trait VideoHandler<Ctx> {
    /// A new frame (access unit) has begun.
    ///
    /// The depacketizer calls this as early as it can determine the frame's
    /// basic properties, which may be before all of its packets have arrived.
    /// The values here are therefore the best knowledge so far; the values on
    /// [`VideoFrameEnd`] are authoritative.
    ///
    /// Return [`Accumulate::Yes`] to have the depacketizer retain the frame's
    /// data for [`VideoFrameEnd::complete_frame`]. [`VideoHandler::data`]
    /// events are delivered either way.
    fn frame_start(&mut self, frame_start: &mut VideoFrameStart<'_, Ctx>) -> Accumulate;

    /// A chunk of unframed codec unit data. See [`VideoData`].
    fn data(&mut self, _data: &VideoData<'_>) {}

    /// The frame begun by the last [`VideoHandler::frame_start`] is complete.
    fn frame_end(&mut self, _frame_end: &mut VideoFrameEnd<'_, Ctx>) {}

    /// Packets were lost or data was corrupt.
    ///
    /// If a frame was in progress (`frame_start` was called without a matching
    /// `frame_end`), it has been abandoned: no `frame_end` will follow for it.
    fn loss(&mut self, _loss: &Loss<'_, Ctx>) {}
}

/// Receives audio depacketization events from a [`super::AudioDepacketizer`].
///
/// See [`VideoHandler`] for an overview. Each audio frame arrives complete, in
/// one [`AudioHandler::audio_frame`] call.
pub trait AudioHandler<Ctx> {
    /// A complete audio frame.
    fn audio_frame(&mut self, _frame: &AudioFrameRef<'_, Ctx>) {}

    /// Packets were lost or data was corrupt.
    fn loss(&mut self, _loss: &Loss<'_, Ctx>) {}
}

/// Receives message depacketization events from a [`super::MessageDepacketizer`].
///
/// See [`VideoHandler`] for an overview. Each message arrives complete, in one
/// [`MessageHandler::message_frame`] call.
pub trait MessageHandler<Ctx> {
    /// A complete message.
    fn message_frame(&mut self, _frame: &MessageFrameRef<'_, Ctx>) {}

    /// Packets were lost or data was corrupt. Any in-progress message was discarded.
    fn loss(&mut self, _loss: &Loss<'_, Ctx>) {}
}

impl<Ctx, H: VideoHandler<Ctx> + ?Sized> VideoHandler<Ctx> for &mut H {
    #[inline]
    fn frame_start(&mut self, frame_start: &mut VideoFrameStart<'_, Ctx>) -> Accumulate {
        (**self).frame_start(frame_start)
    }

    #[inline]
    fn data(&mut self, data: &VideoData<'_>) {
        (**self).data(data)
    }

    #[inline]
    fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, Ctx>) {
        (**self).frame_end(frame_end)
    }

    #[inline]
    fn loss(&mut self, loss: &Loss<'_, Ctx>) {
        VideoHandler::loss(&mut **self, loss)
    }
}

impl<Ctx, H: AudioHandler<Ctx> + ?Sized> AudioHandler<Ctx> for &mut H {
    #[inline]
    fn audio_frame(&mut self, frame: &AudioFrameRef<'_, Ctx>) {
        (**self).audio_frame(frame)
    }

    #[inline]
    fn loss(&mut self, loss: &Loss<'_, Ctx>) {
        AudioHandler::loss(&mut **self, loss)
    }
}

impl<Ctx, H: MessageHandler<Ctx> + ?Sized> MessageHandler<Ctx> for &mut H {
    #[inline]
    fn message_frame(&mut self, frame: &MessageFrameRef<'_, Ctx>) {
        (**self).message_frame(frame)
    }

    #[inline]
    fn loss(&mut self, loss: &Loss<'_, Ctx>) {
        MessageHandler::loss(&mut **self, loss)
    }
}

/// Whether the depacketizer should retain a video frame's data until its end.
///
/// Returned from [`VideoHandler::frame_start`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Accumulate {
    /// Retain the frame, so that [`VideoFrameEnd::complete_frame`] and
    /// [`VideoFrameEnd::visit_frame_data`] can supply it.
    Yes,

    /// Don't retain the frame. The handler sees its data only via
    /// [`VideoHandler::data`], and the depacketizer releases buffer space as soon as
    /// each chunk has been delivered.
    No,
}

/// Information about a video frame that has just begun.
///
/// Passed to [`VideoHandler::frame_start`]. Values are the best knowledge so far;
/// see [`VideoFrameEnd`] for authoritative values.
pub struct VideoFrameStart<'a, Ctx> {
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) ctx: &'a Ctx,
    pub(crate) is_random_access_point: bool,
    pub(crate) is_disposable: bool,
    pub(crate) has_new_parameters: bool,
    pub(crate) is_decodable: bool,

    /// True if packets were lost immediately before this frame, and it may be
    /// missing its beginning. Used to compute `is_decodable`.
    pub(crate) missing_prefix: bool,
    pub(crate) parameters: Option<&'a VideoParameters>,

    /// For H.264 and H.265, where [`VideoFrameStart::set_h264_parameters`] or
    /// [`VideoFrameStart::set_h265_parameters`] stores its override for the
    /// depacketizer to commit when the frame ends.
    pub(crate) param_override: Option<&'a mut dyn ParametersOverrideSlot>,
}

/// Storage for a parameter override set via [`VideoFrameStart`], not yet
/// committed. Each codec that supports overrides implements this for its own
/// override type; the defaults reject other codecs' parameters.
pub(crate) trait ParametersOverrideSlot {
    /// Returns the override's parameters, if set.
    fn parameters(&self) -> Option<&VideoParameters>;

    #[cfg(feature = "h264")]
    fn set_h264(&mut self, _sps: &[u8], _pps: &[u8]) -> Result<(), String> {
        Err("not an H.264 stream".to_owned())
    }

    #[cfg(feature = "h265")]
    fn set_h265(&mut self, _vps: &[u8], _sps: &[u8], _pps: &[u8]) -> Result<(), String> {
        Err("not an H.265 stream".to_owned())
    }
}

impl<Ctx> VideoFrameStart<'_, Ctx> {
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

    /// Returns if this frame appears to be a random access point.
    ///
    /// See [`VideoFrameEnd::is_random_access_point`].
    #[inline]
    pub fn is_random_access_point(&self) -> bool {
        self.is_random_access_point
    }

    /// Returns if this frame appears to be disposable.
    ///
    /// See [`VideoFrameEnd::is_disposable`].
    #[inline]
    pub fn is_disposable(&self) -> bool {
        self.is_disposable
    }

    /// Returns if this frame appears to be decodable.
    ///
    ///
    /// See [`VideoFrameEnd::is_decodable`].
    #[inline]
    pub fn is_decodable(&self) -> bool {
        self.is_decodable
    }

    /// Returns if this frame appears to set new parameters.
    ///
    /// See [`VideoFrameEnd::has_new_parameters`].
    #[inline]
    pub fn has_new_parameters(&self) -> bool {
        self.has_new_parameters || self.overridden_parameters().is_some()
    }

    /// Returns the parameters in effect for this frame, if known.
    ///
    /// If [`VideoFrameStart::has_new_parameters`] is true, these are the new
    /// parameters. [`super::VideoDepacketizer::parameters`] doesn't reflect them
    /// until the frame ends.
    #[inline]
    pub fn parameters(&self) -> Option<&VideoParameters> {
        self.overridden_parameters().or(self.parameters)
    }

    fn overridden_parameters(&self) -> Option<&VideoParameters> {
        self.param_override.as_deref().and_then(|o| o.parameters())
    }

    /// Overrides the H.264 SPS and PPS for this frame and later ones.
    ///
    /// This is useful to "fix" a camera's parameters, such as adding missing
    /// pixel aspect ratio information to the SPS VUI, or bitstream
    /// restrictions which reduce decode latency. See
    /// [`super::h264::parameters_from_sps_and_pps`].
    ///
    /// Afterward, [`VideoFrameStart::parameters`] returns the new parameters
    /// and [`VideoFrameStart::has_new_parameters`] returns true, as do their
    /// [`VideoFrameEnd`] counterparts. The frame's data doesn't include
    /// parameter sets either way; [`VideoFrameEnd::complete_frame`] and
    /// [`VideoFrameEnd::visit_frame_data`] prepend these if the
    /// [`FrameFormat`] requests it.
    ///
    /// The override stays in effect until the stream's in-band parameters
    /// change; repeats of the parameters it replaced don't undo it. Parameter
    /// sets which arrive after the frame's first slice (an ordering violation)
    /// are overridden too.
    ///
    /// Returns an error if this isn't an H.264 stream or the parameters are invalid.
    #[cfg(feature = "h264")]
    pub fn set_h264_parameters(&mut self, sps: &[u8], pps: &[u8]) -> Result<(), crate::Error> {
        match self.param_override.as_deref_mut() {
            Some(slot) => slot.set_h264(sps, pps),
            None => Err("not an H.264 stream".to_owned()),
        }
        .map_err(|e| wrap!(crate::error::ErrorInt::InvalidArgument(e)))
    }

    /// Overrides the H.265 VPS, SPS, and PPS for this frame and later ones.
    ///
    /// As in [`VideoFrameStart::set_h264_parameters`].
    ///
    /// Returns an error if this isn't an H.265 stream or the parameters are invalid.
    #[cfg(feature = "h265")]
    pub fn set_h265_parameters(
        &mut self,
        vps: &[u8],
        sps: &[u8],
        pps: &[u8],
    ) -> Result<(), crate::Error> {
        match self.param_override.as_deref_mut() {
            Some(slot) => slot.set_h265(vps, sps, pps),
            None => Err("not an H.265 stream".to_owned()),
        }
        .map_err(|e| wrap!(crate::error::ErrorInt::InvalidArgument(e)))
    }
}

/// A chunk of unframed codec unit data, passed to [`VideoHandler::data`].
///
/// "Unframed" means that no length prefix, Annex B start code, or other
/// container framing is applied. [`VideoData::position`] says where this chunk falls
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
/// [`VideoFrameStart::has_new_parameters`].
#[derive(Debug)]
pub struct VideoData<'a> {
    /// The position of this chunk within its codec unit.
    pub position: UnitPosition,

    /// The chunk's bytes, as a sequence of slices to be concatenated.
    ///
    /// The slices refer directly to the depacketizer's input buffer. Some may
    /// be empty.
    pub data: &'a [&'a [u8]],
}

impl VideoData<'_> {
    /// Returns the total length of [`VideoData::data`] in bytes.
    #[inline]
    pub fn len(&self) -> usize {
        self.data.iter().map(|d| d.len()).sum()
    }

    /// Returns true if [`VideoData::data`] is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.iter().all(|d| d.is_empty())
    }
}

/// The position of a [`VideoData`] chunk within its codec unit.
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
/// Passed to [`VideoHandler::frame_end`].
pub struct VideoFrameEnd<'a, Ctx> {
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) start_ctx: &'a Ctx,
    pub(crate) end_ctx: &'a Ctx,
    pub(crate) is_random_access_point: bool,
    pub(crate) is_disposable: bool,
    pub(crate) has_new_parameters: bool,
    pub(crate) is_decodable: bool,

    /// True if packets were lost immediately before this frame, and it may be
    /// missing its beginning. Used to compute `is_decodable`.
    pub(crate) missing_prefix: bool,
    pub(crate) body: FrameBody<'a>,
}

/// Codec-specific access to a frame's accumulated data and parameters.
pub(crate) enum FrameBody<'a> {
    #[cfg(feature = "h264")]
    H264(super::h264::FrameEndBody<'a>),

    #[cfg(feature = "h265")]
    H265(super::h265::FrameEndBody<'a>),

    /// A frame which the depacketizer assembled itself, in a fixed format.
    Owned {
        /// The data, if accumulated and not yet taken.
        data: Option<Vec<u8>>,
        parameters: Option<&'a VideoParameters>,
    },
}

// Only the H.26x codecs use `format`.
#[cfg_attr(not(any(feature = "h264", feature = "h265")), allow(unused_variables))]
impl<Ctx> VideoFrameEnd<'_, Ctx> {
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

    /// Returns if this frame is likely decodable.
    ///
    /// A frame is decodable if it's complete, and either it's a random access
    /// point or no packets have been lost and no corrupt data has been found
    /// since the last complete random access point. Frames before the first
    /// random access point are not decodable.
    ///
    /// A frame is complete unless packets were lost immediately before it and
    /// its first slice isn't the first slice of its picture. (Loss within a
    /// frame abandons it; see [`VideoHandler::loss`].)
    ///
    /// This is conservative: loss taints every frame until the next random
    /// access point, even though the lost data may have been disposable. One
    /// case isn't detected: if packets carrying new parameter sets are lost
    /// immediately before a random access point whose slices all arrive, the
    /// frame is reported decodable, but a decoder will use stale parameters.
    #[inline]
    pub fn is_decodable(&self) -> bool {
        self.is_decodable
    }

    /// Returns true if this frame set new video parameters.
    #[inline]
    pub fn has_new_parameters(&self) -> bool {
        self.has_new_parameters
    }

    /// Returns the parameters in effect for this frame, if known.
    pub fn parameters(&self) -> Option<&VideoParameters> {
        match &self.body {
            #[cfg(feature = "h264")]
            FrameBody::H264(b) => b.parameters(),
            #[cfg(feature = "h265")]
            FrameBody::H265(b) => b.parameters(),
            FrameBody::Owned { parameters, .. } => *parameters,
        }
    }

    /// Returns the accumulated frame data in the given format.
    ///
    /// Returns `None` if [`VideoHandler::frame_start`] didn't return
    /// [`Accumulate::Yes`] or if this has already been called for this frame.
    pub fn complete_frame(&mut self, format: FrameFormat) -> Option<Vec<u8>> {
        match &mut self.body {
            #[cfg(feature = "h264")]
            FrameBody::H264(b) => b.build(format),
            #[cfg(feature = "h265")]
            FrameBody::H265(b) => b.build(format),
            FrameBody::Owned { data, .. } => data.take(),
        }
    }

    /// Visits the accumulated frame data in the given format without
    /// allocating, calling `visitor` for each contiguous chunk in order.
    ///
    /// Returns false (without calling `visitor`) if the frame wasn't
    /// accumulated or [`VideoFrameEnd::complete_frame`] has already been called.
    pub fn visit_frame_data(&self, format: FrameFormat, visitor: &mut impl FnMut(&[u8])) -> bool {
        match &self.body {
            #[cfg(feature = "h264")]
            FrameBody::H264(b) => b.visit(format, visitor),
            #[cfg(feature = "h265")]
            FrameBody::H265(b) => b.visit(format, visitor),
            FrameBody::Owned { data, .. } => match data {
                Some(d) => {
                    visitor(d);
                    true
                }
                None => false,
            },
        }
    }
}

/// Notice of lost or corrupt data, passed to [`VideoHandler::loss`].
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
    #[non_exhaustive]
    PacketLoss {
        /// The number of lost packets.
        packets: u16,
    },

    /// The depacketizer detected corrupt data or a protocol violation.
    ///
    /// It discards any in-progress frame and resynchronizes at the next frame
    /// boundary.
    Corrupt(Corruption),
}

/// Details of corrupt data, as reported by [`LossReason::Corrupt`].
///
/// Currently this offers only a human-readable description, via its
/// [`std::fmt::Display`] impl.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Corruption(std::borrow::Cow<'static, str>);

impl Corruption {
    pub(crate) fn new(description: impl Into<std::borrow::Cow<'static, str>>) -> Self {
        Self(description.into())
    }
}

impl std::fmt::Display for Corruption {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Corruption {}

/// A complete audio frame, passed to [`AudioHandler::audio_frame`].
pub struct AudioFrameRef<'a, Ctx> {
    pub(crate) ctx: &'a Ctx,
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) frame_length: NonZeroU32,

    /// The raw frame data.
    pub(crate) data: &'a [u8],

    /// For AAC, the parameters for [`super::aac::Framing::Adts`].
    pub(crate) adts: Option<super::aac::AdtsParams>,
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

    /// Returns the frame data in the given format.
    ///
    /// This borrows the depacketizer's data unless the format requires adding
    /// framing, as with [`super::aac::Framing::Adts`].
    pub fn data(&self, format: FrameFormat) -> std::borrow::Cow<'_, [u8]> {
        match self.header(format) {
            None => std::borrow::Cow::Borrowed(self.data),
            Some(h) => std::borrow::Cow::Owned([&h[..], self.data].concat()),
        }
    }

    /// Returns the header to prepend in the given format, if any.
    fn header(&self, format: FrameFormat) -> Option<[u8; 7]> {
        match (self.adts, format.aac_framing) {
            (Some(adts), super::aac::Framing::Adts) => Some(adts.header(self.data.len())),
            _ => None,
        }
    }
}

/// A complete message, passed to [`MessageHandler::message_frame`].
pub struct MessageFrameRef<'a, Ctx> {
    pub(crate) ctx: &'a Ctx,
    pub(crate) timestamp: crate::Timestamp,
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
            is_random_access_point: bool,
            is_disposable: bool,
            has_new_parameters: bool,
        },
        Data(UnitPosition, crate::testutil::HexDebug),
        FrameEnd {
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

    impl<Ctx> VideoHandler<Ctx> for Recorder {
        fn frame_start(&mut self, frame_start: &mut VideoFrameStart<'_, Ctx>) -> Accumulate {
            self.events.push(Event::FrameStart {
                is_random_access_point: frame_start.is_random_access_point(),
                is_disposable: frame_start.is_disposable(),
                has_new_parameters: frame_start.has_new_parameters(),
            });
            self.streamed.clear();
            self.unit_start = None;
            self.accumulate
        }

        fn data(&mut self, data: &VideoData<'_>) {
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

        fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, Ctx>) {
            let mut visited = Vec::new();
            let visited_ok =
                frame_end.visit_frame_data(self.format, &mut |c| visited.extend_from_slice(c));
            let data = frame_end.complete_frame(self.format);
            assert_eq!(data.is_some(), visited_ok);
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
    }

    impl<Ctx> AudioHandler<Ctx> for Recorder {
        fn loss(&mut self, loss: &Loss<'_, Ctx>) {
            self.unit_start = None;
            self.events.push(Event::Loss(loss.reason().clone()));
        }

        fn audio_frame(&mut self, frame: &AudioFrameRef<'_, Ctx>) {
            let data = frame.data(self.format);
            self.events.push(Event::AudioFrame(hex(&data)));
        }
    }

    impl<Ctx> MessageHandler<Ctx> for Recorder {
        fn loss(&mut self, loss: &Loss<'_, Ctx>) {
            self.unit_start = None;
            self.events.push(Event::Loss(loss.reason().clone()));
        }

        fn message_frame(&mut self, frame: &MessageFrameRef<'_, Ctx>) {
            self.events.push(Event::MessageFrame(hex(frame.data())));
        }
    }
}
