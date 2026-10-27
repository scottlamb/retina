// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Packetization of frames into RTP payloads.
//!
//! This is the counterpart of depacketization, for anything which sends RTP:
//! a server responding to `PLAY`, or a client using `RECORD`. A packetizer is
//! fed frames made of *unframed* codec units (e.g. H.264 NAL units) with
//! parameters out of band—the same normal form a depacketizer produces—and
//! pushes RTP payloads to a caller-supplied [`PayloadSink`].

use super::Error;
#[cfg(any(feature = "h264", feature = "h265"))]
use super::VideoParametersCodec;
use super::{
    AudioParameters, AudioParametersCodec, FrameFormat, ParameterSetInsertion, PayloadFormat,
    Position, VideoFrameStart, VideoParameters,
};

/// Options for a [`VideoPacketizer`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VideoPacketizerOptions {
    pub(crate) parameter_set_insertion: ParameterSetInsertion,
    pub(crate) aggregate: bool,
}

impl Default for VideoPacketizerOptions {
    fn default() -> Self {
        Self {
            parameter_set_insertion: ParameterSetInsertion::EachKeyFrame,
            aggregate: true,
        }
    }
}

impl VideoPacketizerOptions {
    /// Sets when to insert parameter sets into the stream. Defaults to
    /// [`ParameterSetInsertion::EachKeyFrame`].
    #[inline]
    pub fn parameter_set_insertion(self, parameter_set_insertion: ParameterSetInsertion) -> Self {
        Self {
            parameter_set_insertion,
            ..self
        }
    }

    /// Sets whether to aggregate small codec units into one payload (e.g.
    /// H.264 STAP-A or H.265 aggregation packets). Defaults to true.
    #[inline]
    pub fn aggregate(self, aggregate: bool) -> Self {
        Self { aggregate, ..self }
    }
}

/// Information about a frame to packetize, passed to
/// [`VideoPacketizer::start_frame`] or [`VideoPacketizer::push_frame`].
///
/// The counterpart of [`VideoFrameStart`], from which it can be converted
/// when repacketizing a depacketizer's output.
#[derive(Clone, Copy, Debug)]
pub struct VideoFrameInfo {
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) is_random_access_point: bool,
    pub(crate) is_disposable: bool,
    pub(crate) extensions: crate::rtp::Extensions,
}

impl VideoFrameInfo {
    /// Creates information about a frame with the given timestamp, which is
    /// neither a random access point nor disposable.
    #[inline]
    pub fn new(timestamp: crate::Timestamp) -> Self {
        Self {
            timestamp,
            is_random_access_point: false,
            is_disposable: false,
            extensions: crate::rtp::Extensions::default(),
        }
    }

    pub_if_unstable_extensions! {
        /// Sets the frame's RTP header extension values, which the packetizer
        /// attaches to the frame's first payload; see [`Payload::encoded_extensions`].
        #[inline]
        pub fn with_extensions(self, extensions: crate::rtp::Extensions) -> Self {
            Self { extensions, ..self }
        }
    }

    pub_if_unstable_extensions! {
        /// Returns the frame's RTP header extension values.
        #[inline]
        pub fn extensions(&self) -> &crate::rtp::Extensions {
            &self.extensions
        }
    }

    /// Sets whether the frame is a random access point.
    #[inline]
    pub fn with_random_access_point(self, is_random_access_point: bool) -> Self {
        Self {
            is_random_access_point,
            ..self
        }
    }

    /// Sets whether the frame is disposable: no other frames depend on it.
    #[inline]
    pub fn with_disposable(self, is_disposable: bool) -> Self {
        Self {
            is_disposable,
            ..self
        }
    }

    /// Returns the frame's timestamp.
    #[inline]
    pub fn timestamp(&self) -> crate::Timestamp {
        self.timestamp
    }

    /// Returns true if the frame is a random access point.
    #[inline]
    pub fn is_random_access_point(&self) -> bool {
        self.is_random_access_point
    }

    /// Returns true if no other frames depend on this one.
    #[inline]
    pub fn is_disposable(&self) -> bool {
        self.is_disposable
    }
}

impl<Ctx> From<&VideoFrameStart<'_, Ctx>> for VideoFrameInfo {
    fn from(frame_start: &VideoFrameStart<'_, Ctx>) -> Self {
        Self {
            timestamp: frame_start.timestamp(),
            is_random_access_point: frame_start.is_random_access_point(),
            is_disposable: frame_start.is_disposable(),
            extensions: *frame_start.extensions(),
        }
    }
}

/// Receives RTP payloads from a packetizer.
///
/// See e.g. [`crate::rtp::Sender::sink`], which turns payloads into complete
/// RTP packets.
pub trait PayloadSink {
    /// A complete RTP payload.
    fn payload(&mut self, payload: &Payload<'_>);

    /// The packetizer's input lost data, so its output is missing data too.
    ///
    /// The sink should make this visible to receivers, e.g. by skipping an RTP
    /// sequence number.
    fn discontinuity(&mut self) {}

    /// Returns true if the sink is short of space, so the packetizer should
    /// shed load.
    ///
    /// This is a soft limit: the packetizer may deliver a couple more payloads
    /// to end the current frame cleanly. See "Throttling" on
    /// [`VideoPacketizer`].
    fn congested(&self) -> bool {
        false
    }

    /// Returns the largest payload to deliver, in bytes, before any header
    /// extension block. Defaults to 1400.
    ///
    /// This excludes the RTP fixed header (and CSRCs) and lower-layer
    /// headers. E.g., 1400 leaves ample room for IP, UDP, and RTP headers on
    /// a path with a 1500-byte MTU.
    ///
    /// The packetizer subtracts the length of the frame's encoded header
    /// extensions (see [`PayloadSink::serialize_extensions`]) from this for
    /// the frame's first payload.
    ///
    /// The packetizer asks once per frame, so a change takes effect at the
    /// next frame. If the value is too small for the codec to make progress
    /// (a few bytes), the packetizer exceeds it.
    fn max_payload_size(&self) -> u16 {
        1400
    }

    /// Encodes `extensions` as an RTP header extension block, replacing the
    /// contents of `out`, for [`Payload::encoded_extensions`].
    ///
    /// The block includes its 4-byte profile and length header, and its
    /// length is a multiple of 4. It's empty if there's nothing to send,
    /// which is the default.
    ///
    /// The packetizer calls this once per frame with a non-empty
    /// `extensions`, before delivering any of the frame's payloads.
    #[cfg(feature = "unstable-extensions")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-extensions")))]
    fn serialize_extensions(&self, extensions: &crate::rtp::Extensions, out: &mut Vec<u8>) {
        let _ = extensions;
        out.clear();
    }
}

/// Calls [`PayloadSink::serialize_extensions`] if there's anything to
/// serialize, clearing `out` otherwise.
pub(crate) fn serialize_extensions(
    sink: &impl PayloadSink,
    extensions: &crate::rtp::Extensions,
    out: &mut Vec<u8>,
) {
    out.clear();
    #[cfg(feature = "unstable-extensions")]
    if !extensions.is_empty() {
        sink.serialize_extensions(extensions, out);
        debug_assert!(
            out.len().is_multiple_of(4),
            "extension block must be 4-byte aligned"
        );
    }
    #[cfg(not(feature = "unstable-extensions"))]
    let _ = (sink, extensions);
}

/// A frame's payload size limits, from [`PayloadSink::max_payload_size`].
#[derive(Copy, Clone, Debug)]
pub(crate) struct PayloadLimits {
    first: usize,
    rest: usize,
}

impl Default for PayloadLimits {
    /// Returns [`PayloadSink::max_payload_size`]'s default, for before the
    /// first frame.
    fn default() -> Self {
        Self {
            first: 1400,
            rest: 1400,
        }
    }
}

impl PayloadLimits {
    /// Gets limits from `sink` for a frame with the given encoded extension
    /// block, raising them to at least `min`, the least that lets the codec
    /// make progress.
    pub(crate) fn new(sink: &impl PayloadSink, encoded_extensions: &[u8], min: usize) -> Self {
        let rest = usize::from(sink.max_payload_size());
        Self {
            first: rest.saturating_sub(encoded_extensions.len()).max(min),
            rest: rest.max(min),
        }
    }

    /// Returns the limit for the frame's first payload, or for the rest.
    #[inline]
    pub(crate) fn get(&self, first: bool) -> usize {
        if first { self.first } else { self.rest }
    }
}

impl<S: PayloadSink + ?Sized> PayloadSink for &mut S {
    #[inline]
    fn payload(&mut self, payload: &Payload<'_>) {
        (**self).payload(payload)
    }

    #[inline]
    fn discontinuity(&mut self) {
        (**self).discontinuity()
    }

    #[inline]
    fn congested(&self) -> bool {
        (**self).congested()
    }

    #[inline]
    fn max_payload_size(&self) -> u16 {
        (**self).max_payload_size()
    }

    #[cfg(feature = "unstable-extensions")]
    #[inline]
    fn serialize_extensions(&self, extensions: &crate::rtp::Extensions, out: &mut Vec<u8>) {
        (**self).serialize_extensions(extensions, out)
    }
}

/// An RTP payload, passed to [`PayloadSink::payload`].
#[derive(Debug)]
pub struct Payload<'a> {
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) position: Position,
    pub(crate) data: &'a [&'a [u8]],
    pub(crate) is_random_access_point: bool,
    pub(crate) is_disposable: bool,
    pub(crate) encoded_extensions: &'a [u8],
}

impl<'a> Payload<'a> {
    /// Returns the timestamp of the frame this payload belongs to.
    #[inline]
    pub fn timestamp(&self) -> crate::Timestamp {
        self.timestamp
    }

    /// Returns the RTP marker bit: for video, true on the last payload of a
    /// frame.
    #[inline]
    pub fn mark(&self) -> bool {
        self.position.is_last()
    }

    /// Returns the position of this payload within its frame.
    ///
    /// Together with [`Payload::is_random_access_point`], this identifies
    /// where a new receiver can join the stream.
    #[inline]
    pub fn position(&self) -> Position {
        self.position
    }

    /// Returns the payload's bytes, as a sequence of slices to be
    /// concatenated.
    ///
    /// These may refer directly to the packetizer's input.
    #[inline]
    pub fn data(&self) -> &'a [&'a [u8]] {
        self.data
    }

    /// Returns true if this payload's frame is a random access point.
    #[inline]
    pub fn is_random_access_point(&self) -> bool {
        self.is_random_access_point
    }

    /// Returns true if no other frames depend on this payload's frame.
    #[inline]
    pub fn is_disposable(&self) -> bool {
        self.is_disposable
    }

    pub_if_unstable_extensions! {
        /// Returns the RTP header extension block to send with this payload,
        /// as encoded by [`PayloadSink::serialize_extensions`], or empty.
        ///
        /// This is the frame's values (see [`VideoFrameInfo::with_extensions`]
        /// and [`AudioPacketizer::push_frame_with_extensions`]) on its first
        /// payload, and empty on the rest. Values such as
        /// [`crate::rtp::AbsCaptureTime`] describe the whole frame, so sending
        /// them once per frame suffices, as libwebrtc and the ONVIF replay
        /// extension do.
        #[inline]
        pub fn encoded_extensions(&self) -> &'a [u8] {
            self.encoded_extensions
        }
    }

    /// Returns the total length of [`Payload::data`] in bytes.
    #[inline]
    pub fn len(&self) -> usize {
        self.data.iter().map(|d| d.len()).sum()
    }

    /// Returns true if [`Payload::data`] is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.iter().all(|d| d.is_empty())
    }
}

/// Turns video frames into RTP payloads.
///
/// Frames are supplied incrementally: [`VideoPacketizer::start_frame`], then
/// [`VideoPacketizer::push_unit`] for each chunk of each codec unit, then
/// [`VideoPacketizer::end_frame`]. Payloads are delivered to the sink as soon
/// as they're known not to be the frame's last (which needs the RTP marker
/// bit), so a frame streams out at the pace its data arrives. Alternatively,
/// [`VideoPacketizer::push_frame`] packetizes a whole frame in one call. It's
/// just a convenience: it splits the frame's framed data into units and
/// supplies them as above, so the two produce the same payloads.
///
/// The frame's last payload is thus held until `end_frame`. When the end isn't
/// known promptly, [`VideoPacketizer::flush`] releases it early; see there.
///
/// Currently supports H.264 and H.265.
///
/// # Repacketizing
///
/// The incremental methods match the events of a [`super::VideoHandler`], so
/// a proxy can feed a depacketizer's output straight into a packetizer:
///
/// ```
/// use retina::codec::{
///     Accumulate, VideoFrameInfo, Loss, PayloadSink, VideoData, VideoFrameEnd, VideoFrameStart,
///     VideoHandler, VideoPacketizer,
/// };
///
/// struct Repacketize<'a, S> {
///     packetizer: &'a mut VideoPacketizer,
///     sink: S,
/// }
///
/// impl<Ctx, S: PayloadSink> VideoHandler<Ctx> for Repacketize<'_, S> {
///     fn frame_start(&mut self, fs: &mut VideoFrameStart<'_, Ctx>) -> Accumulate {
///         if let Some(p) = fs.parameters() {
///             if let Err(e) = self.packetizer.set_parameters(p) {
///                 // A different codec; the packetizer keeps its old parameters.
///                 eprintln!("can't repacketize with new parameters: {e}");
///             }
///         }
///         self.packetizer.start_frame(VideoFrameInfo::from(&*fs), &mut self.sink);
///         Accumulate::No // release each packet as soon as it's repacketized.
///     }
///
///     fn data(&mut self, data: &VideoData<'_>) {
///         self.packetizer.push_unit(data.position, data.data, &mut self.sink);
///     }
///
///     fn frame_end(&mut self, _: &mut VideoFrameEnd<'_, Ctx>) {
///         self.packetizer.end_frame(&mut self.sink);
///     }
///
///     fn loss(&mut self, _: &Loss<'_, Ctx>) {
///         self.packetizer.discontinuity(&mut self.sink);
///     }
/// }
/// ```
///
/// To fix up parameters (see [`VideoFrameStart::set_parameters`]), do so
/// before calling [`VideoFrameStart::parameters`].
///
/// # Parameter sets
///
/// For H.264 and H.265, the packetizer manages parameter sets (VPS, SPS, and
/// PPS NAL units). It inserts them in-band as the
/// [`ParameterSetInsertion`] option specifies, at each frame's *insertion
/// point*: before its first codec unit which is neither a parameter set nor
/// an access unit delimiter, or at its end if there's no such unit.
///
/// The parameters come from [`VideoPacketizer::new`] or
/// [`VideoPacketizer::set_parameters`], or from parameter sets supplied
/// in-band via [`VideoPacketizer::push_unit`] or
/// [`VideoPacketizer::push_frame`]. An in-band parameter set isn't delivered
/// where it was supplied:
///
/// *   Before the insertion point, it's applied there, so it takes effect for
///     its own frame, and is inserted as the option specifies.
/// *   After the insertion point (e.g. following an SEI NAL unit), it can't be
///     moved earlier, so it's delivered where it was supplied if it changes
///     the parameters, and applied when the frame ends. With
///     [`ParameterSetInsertion::OnChange`] and
///     [`ParameterSetInsertion::EachKeyFrame`], the next frame inserts it
///     again.
///
/// Either way, [`VideoPacketizer::parameters`] and
/// [`VideoPacketizer::payload_format`] reflect it once applied. In-band
/// parameter sets which can't be parsed (logged once per packetizer) leave the
/// parameters unchanged and are passed through as-is at the insertion point.
///
/// # Throttling
///
/// When [`PayloadSink::congested`] returns true, the packetizer drops data
/// in a way receivers can interpret precisely, rather than leaving the sink
/// to drop arbitrary packets:
///
/// *   At the start of a frame, it drops the whole frame. This leaves no gap
///     in sequence numbers; receivers see a gap in timestamps.
/// *   At the start of a codec unit within a frame, or before delivering a
///     fragment of one, it truncates the unit: the next payload is the
///     unit's last, with the NAL header's F bit set to mark it damaged, as
///     RFC 6184 section 5.8 and RFC 7798 section 1.1.4 allow. That payload
///     ends the frame, and the rest of the frame is dropped. (A unit whose data
///     has all been supplied is completed rather than truncated.)
/// *   After dropping all or part of a frame which isn't disposable, it drops
///     every frame until the next random access point, since they'd be
///     undecodable anyway.
///
/// Receivers thus see at most one damaged frame per congestion episode, and
/// no sequence number gaps. Retina's own depacketizer reports the damaged
/// frame as [`crate::codec::LossReason::Corrupt`].
#[derive(Debug)]
pub struct VideoPacketizer(VideoPacketizerInner);

#[derive(Debug)]
enum VideoPacketizerInner {
    #[cfg(feature = "h264")]
    H264(Box<super::h264::Packetizer>),
    #[cfg(feature = "h265")]
    H265(Box<super::h265::Packetizer>),
}

// Without H.264 or H.265, there are no packetizers.
#[cfg_attr(not(any(feature = "h264", feature = "h265")), allow(unused_variables))]
impl VideoPacketizer {
    /// Creates a packetizer for a stream with the given parameters.
    ///
    /// Returns an [`ErrorKind::Unsupported`](super::ErrorKind::Unsupported)
    /// error if Retina can't packetize this codec.
    ///
    /// The payload size limit comes from the sink; see
    /// [`PayloadSink::max_payload_size`].
    pub fn new(
        parameters: &VideoParameters,
        options: VideoPacketizerOptions,
    ) -> Result<Self, Error> {
        match &parameters.codec {
            #[cfg(feature = "h264")]
            VideoParametersCodec::H264 { .. } => super::h264::Packetizer::new(parameters, options)
                .map(|p| Self(VideoPacketizerInner::H264(Box::new(p)))),
            #[cfg(feature = "h265")]
            VideoParametersCodec::H265 { .. } => super::h265::Packetizer::new(parameters, options)
                .map(|p| Self(VideoPacketizerInner::H265(Box::new(p)))),
            _ => Err(Error::unsupported(format!(
                "packetizing {} is unsupported",
                parameters.rfc6381_codec()
            ))),
        }
    }

    /// Returns the payload format, suitable for describing the stream in SDP.
    ///
    /// This reflects the current parameters; it's equivalent to
    /// [`VideoParameters::payload_format`] on [`VideoPacketizer::parameters`].
    pub fn payload_format(&self) -> PayloadFormat {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref p) => p.payload_format(),
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref p) => p.payload_format(),
        }
    }

    /// Returns the current parameters.
    pub fn parameters(&self) -> &VideoParameters {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref p) => p.parameters(),
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref p) => p.parameters(),
        }
    }

    /// Sets new parameters, taking effect at the next insertion point; see
    /// "Parameter sets" above.
    ///
    /// If they differ from the current parameters, they're inserted into the
    /// stream there (unless the parameter set insertion option is
    /// [`ParameterSetInsertion::Never`]). If they're the same, this does
    /// nothing, so it's fine to call before every frame.
    ///
    /// Returns an [`ErrorKind::Invalid`](super::ErrorKind::Invalid) error if
    /// the parameters are for a different codec. The packetizer keeps its
    /// current parameters in that case.
    pub fn set_parameters(&mut self, parameters: &VideoParameters) -> Result<(), Error> {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref mut p) => p.set_parameters(parameters),
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref mut p) => p.set_parameters(parameters),
        }
    }

    /// Starts a new frame, ending any frame in progress.
    pub fn start_frame(&mut self, frame: VideoFrameInfo, sink: &mut impl PayloadSink) {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref mut p) => p.start_frame(frame, sink),
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref mut p) => p.start_frame(frame, sink),
        }
    }

    /// Supplies a chunk of an unframed codec unit, as in [`super::VideoData`].
    ///
    /// `position` is the chunk's position within its codec unit, not within
    /// the frame; the frame is delimited by [`VideoPacketizer::start_frame`]
    /// and [`VideoPacketizer::end_frame`]. A unit may be supplied in one
    /// [`Position::Complete`] chunk, or split into a [`Position::Start`]
    /// chunk, any number of [`Position::Middle`] chunks, and a
    /// [`Position::End`] chunk.
    ///
    /// For H.264 and H.265, units are NAL units, with the NAL header at the
    /// start of the first chunk. Parameter set NAL units are taken over by the
    /// packetizer, as described in "Parameter sets" above. A NAL unit which
    /// can't be packetized is discarded (logged once per packetizer): one with
    /// its F bit (`forbidden_zero_bit`) set, or with a type the RTP payload
    /// format reserves for its own packets. To mark lost or damaged data, use
    /// [`VideoPacketizer::discontinuity`] instead.
    ///
    /// Misuse is logged (once per packetizer) and tolerated: a chunk supplied
    /// outside a frame, or continuing a unit which wasn't started, is
    /// discarded, and a unit started while another is in progress ends the
    /// other.
    pub fn push_unit(&mut self, position: Position, data: &[&[u8]], sink: &mut impl PayloadSink) {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref mut p) => p.push_unit(position, data, sink),
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref mut p) => p.push_unit(position, data, sink),
        }
    }

    /// Delivers payloads held back in case they're the frame's last.
    ///
    /// Normally the packetizer holds the most recent payload until it learns
    /// whether that payload ends the frame and so needs the RTP marker bit.
    /// When repacketizing from a source that doesn't promptly say where frames
    /// end (e.g. a camera which doesn't set the marker bit, so the
    /// depacketizer only learns of a frame's end from the next frame's
    /// timestamp), that payload would wait for the next frame. Calling this
    /// after supplying each input packet's data releases it immediately, at
    /// the cost of not aggregating codec units across calls.
    ///
    /// For H.264 and H.265, payloads are made of complete NAL units (or a NAL
    /// unit's final fragment); data of a NAL unit still in progress waits for
    /// the rest of that NAL unit. Nothing is released until the frame's first
    /// VCL (slice) NAL unit has ended: NAL units before it (e.g. SEI) can't end
    /// the frame, so they're held to be aggregated with what follows. An end of
    /// sequence or end of stream NAL unit is also held, since nothing may
    /// follow it in the frame.
    ///
    /// If the frame's last payload was released this way, then
    /// [`VideoPacketizer::end_frame`] delivers an extra filler data NAL unit
    /// (H.264 type 12; H.265 `FD_NUT`) to carry the marker bit, so the output
    /// stays compliant. If the frame ends before `flush`, as when the
    /// depacketizer sees the input's marker bit, nothing extra is delivered.
    pub fn flush(&mut self, sink: &mut impl PayloadSink) {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref mut p) => p.flush(sink),
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref mut p) => p.flush(sink),
        }
    }

    /// Ends the current frame, if any.
    pub fn end_frame(&mut self, sink: &mut impl PayloadSink) {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref mut p) => p.end_frame(sink),
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref mut p) => p.end_frame(sink),
        }
    }

    /// Packetizes a whole frame of framed data.
    ///
    /// This is equivalent to [`VideoPacketizer::start_frame`], then
    /// [`VideoPacketizer::push_unit`] with each codec unit in turn as one
    /// [`Position::Complete`] chunk, then [`VideoPacketizer::end_frame`].
    /// For H.264 and H.265, in-band parameter sets are thus handled as
    /// described in "Parameter sets" above.
    ///
    /// `format` describes how `data` is framed, as when a depacketizer
    /// produced it (see [`super::VideoFrameEnd::complete_frame`]). Only the
    /// framing knobs matter: for H.264 and H.265,
    /// [`FrameFormat::h26x_framing`]. Insertion of parameter sets in the
    /// output is controlled by [`VideoPacketizerOptions::parameter_set_insertion`]
    /// instead.
    ///
    /// Returns an [`ErrorKind::Invalid`](super::ErrorKind::Invalid) error if
    /// the data isn't validly framed, or (for H.264 and H.265) contains a NAL
    /// unit which `push_unit` would discard. Such an error is about this frame
    /// only: nothing has been delivered to `sink`, and the packetizer is
    /// unchanged, so the caller can drop the frame and continue with the
    /// next. Later frames may reference the dropped one, though, so unless
    /// it's known to be unreferenced, call [`VideoPacketizer::discontinuity`]
    /// to drop frames until the next random access point, as for lost input.
    pub fn push_frame(
        &mut self,
        frame: VideoFrameInfo,
        format: FrameFormat,
        data: &[u8],
        sink: &mut impl PayloadSink,
    ) -> Result<(), Error> {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref mut p) => {
                p.push_frame(frame, format.h26x_framing, data, sink)
            }
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref mut p) => {
                p.push_frame(frame, format.h26x_framing, data, sink)
            }
        }
    }

    /// Notes that the input lost data.
    ///
    /// Abandons any frame in progress (payloads already delivered stay
    /// delivered) and calls [`PayloadSink::discontinuity`]. As the lost data
    /// may have been depended on, drops frames until the next random access
    /// point.
    pub fn discontinuity(&mut self, sink: &mut impl PayloadSink) {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref mut p) => p.discontinuity(sink),
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref mut p) => p.discontinuity(sink),
        }
    }
}

/// Options for an [`AudioPacketizer`].
///
/// There are currently none; this exists so that future options (such as
/// aggregating several frames into one payload) can be added without
/// changing [`AudioPacketizer::new`]'s signature. The maximum payload size
/// comes from [`PayloadSink::max_payload_size`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct AudioPacketizerOptions {}

/// Turns audio frames into RTP payloads.
///
/// Unlike [`VideoPacketizer`], frames are supplied whole, via
/// [`AudioPacketizer::push_frame`]: audio frames are small, and a codec's
/// payload format may need a frame's size before its data.
///
/// Currently supports AAC, as RFC 3640's `AAC-hbr` mode, with one access unit
/// per payload, or fragmented across payloads if it doesn't fit in one. As
/// AAC's `AudioSpecificConfig` can only be sent out of band (in the SDP),
/// parameters can't change mid-stream; create a new packetizer instead.
///
/// # Throttling
///
/// When [`PayloadSink::congested`] returns true at the start of a frame, the
/// packetizer drops the whole frame. This leaves no gap in sequence numbers;
/// receivers see a gap in timestamps. As every audio frame is independently
/// decodable, the next frame is sent as usual.
#[derive(Debug)]
pub struct AudioPacketizer(AudioPacketizerInner);

#[derive(Debug)]
enum AudioPacketizerInner {
    Aac(super::aac::Packetizer),
}

impl AudioPacketizer {
    /// Creates a packetizer for a stream with the given parameters.
    ///
    /// Returns an [`ErrorKind::Unsupported`](super::ErrorKind::Unsupported)
    /// error if Retina can't packetize this codec.
    pub fn new(
        parameters: &AudioParameters,
        _options: AudioPacketizerOptions,
    ) -> Result<Self, Error> {
        match parameters.codec {
            AudioParametersCodec::Aac { .. } => Ok(Self(AudioPacketizerInner::Aac(
                super::aac::Packetizer::new(parameters),
            ))),
            AudioParametersCodec::Other => Err(Error::unsupported(format!(
                "packetizing {} is unsupported",
                parameters.rfc6381_codec().unwrap_or("this audio codec")
            ))),
        }
    }

    /// Returns the payload format, suitable for describing the stream in SDP.
    ///
    /// This is equivalent to [`AudioParameters::payload_format`] on
    /// [`AudioPacketizer::parameters`].
    pub fn payload_format(&self) -> PayloadFormat {
        match self.0 {
            AudioPacketizerInner::Aac(ref p) => p.payload_format(),
        }
    }

    /// Returns the parameters.
    pub fn parameters(&self) -> &AudioParameters {
        match self.0 {
            AudioPacketizerInner::Aac(ref p) => p.parameters(),
        }
    }

    /// Packetizes a frame.
    ///
    /// `timestamp` must be in units of the parameters' clock rate
    /// ([`AudioParameters::clock_rate`]). For AAC, `data` is a raw access
    /// unit, as when depacketized with [`super::aac::Framing::Raw`].
    ///
    /// Returns an [`ErrorKind::Invalid`](super::ErrorKind::Invalid) error if
    /// the timestamp's clock rate is wrong, or the frame can't be
    /// packetized (for AAC, if it's empty or exceeds 8,191 bytes). Nothing
    /// has been delivered to `sink` in that case.
    #[inline]
    pub fn push_frame(
        &mut self,
        timestamp: crate::Timestamp,
        data: &[u8],
        sink: &mut impl PayloadSink,
    ) -> Result<(), Error> {
        self.push_frame_with_extensions(timestamp, &crate::rtp::Extensions::default(), data, sink)
    }

    pub_if_unstable_extensions! {
        /// As [`AudioPacketizer::push_frame`], attaching RTP header extension
        /// values to the frame's first payload; see [`Payload::encoded_extensions`].
        pub fn push_frame_with_extensions(
            &mut self,
            timestamp: crate::Timestamp,
            extensions: &crate::rtp::Extensions,
            data: &[u8],
            sink: &mut impl PayloadSink,
        ) -> Result<(), Error> {
            match self.0 {
                AudioPacketizerInner::Aac(ref mut p) => p.push_frame(timestamp, extensions, data, sink),
            }
        }
    }
}

/// Returns the payload format for `parameters`, if they can be packetized.
pub(super) fn audio_payload_format(parameters: &AudioParameters) -> Option<PayloadFormat> {
    match parameters.codec {
        AudioParametersCodec::Aac { .. } => {
            Some(super::aac::Packetizer::payload_format_for(parameters))
        }
        AudioParametersCodec::Other => None,
    }
}

/// Returns the payload format for `parameters`, if they can be packetized.
pub(super) fn payload_format(parameters: &VideoParameters) -> Option<PayloadFormat> {
    match &parameters.codec {
        #[cfg(feature = "h264")]
        VideoParametersCodec::H264 { .. } => {
            super::h264::Packetizer::payload_format_for(parameters)
        }
        #[cfg(feature = "h265")]
        VideoParametersCodec::H265 { .. } => {
            super::h265::Packetizer::payload_format_for(parameters)
        }
        _ => None,
    }
}
