// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Packetization of frames into RTP payloads.
//!
//! This is the counterpart of depacketization, for anything which sends RTP:
//! a server responding to `PLAY`, or a client using `RECORD`. A packetizer is
//! fed frames made of *unframed* codec units (e.g. H.264 NAL units) with
//! parameters out of band—the same normal form a depacketizer produces—and
//! pushes RTP payloads to a caller-supplied [`PayloadSink`].

#[cfg(any(feature = "h264", feature = "h265"))]
use super::VideoParametersCodec;
use super::{ParameterSetInsertion, PayloadFormat, Position, VideoFrameStart, VideoParameters};
use crate::Error;
use crate::error::ErrorInt;

/// Options for a [`VideoPacketizer`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PacketizeOptions {
    pub(crate) max_payload_size: u16,
    pub(crate) parameter_set_insertion: ParameterSetInsertion,
    pub(crate) aggregate: bool,
}

impl Default for PacketizeOptions {
    fn default() -> Self {
        Self {
            max_payload_size: 1400,
            parameter_set_insertion: ParameterSetInsertion::EachKeyFrame,
            aggregate: true,
        }
    }
}

impl PacketizeOptions {
    /// Sets the maximum RTP payload size in bytes. Defaults to 1400.
    ///
    /// This excludes the RTP header added by [`crate::rtp::Sender`], and on
    /// TCP the 4-byte interleaved data header. E.g., 1400 leaves ample room
    /// for IP, UDP, and RTP headers on a path with a 1500-byte MTU.
    #[inline]
    pub fn max_payload_size(self, max_payload_size: u16) -> Self {
        Self {
            max_payload_size,
            ..self
        }
    }

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
pub struct FrameInfo {
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) is_random_access_point: bool,
    pub(crate) is_disposable: bool,
}

impl FrameInfo {
    /// Creates information about a frame with the given timestamp, which is
    /// neither a random access point nor disposable.
    #[inline]
    pub fn new(timestamp: crate::Timestamp) -> Self {
        Self {
            timestamp,
            is_random_access_point: false,
            is_disposable: false,
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

impl<Ctx> From<&VideoFrameStart<'_, Ctx>> for FrameInfo {
    fn from(frame_start: &VideoFrameStart<'_, Ctx>) -> Self {
        Self {
            timestamp: frame_start.timestamp(),
            is_random_access_point: frame_start.is_random_access_point(),
            is_disposable: frame_start.is_disposable(),
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
}

/// An RTP payload, passed to [`PayloadSink::payload`].
#[derive(Debug)]
pub struct Payload<'a> {
    pub(crate) timestamp: crate::Timestamp,
    pub(crate) position: Position,
    pub(crate) data: &'a [&'a [u8]],
    pub(crate) is_random_access_point: bool,
    pub(crate) is_disposable: bool,
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
/// [`VideoPacketizer::push_frame`] packetizes a whole frame in one call.
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
///     Accumulate, FrameInfo, Loss, PayloadSink, VideoData, VideoFrameEnd, VideoFrameStart,
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
///         self.packetizer.start_frame(FrameInfo::from(&*fs), &mut self.sink);
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
/// To fix up parameters (see [`VideoFrameStart::set_h264_parameters`] and
/// [`VideoFrameStart::set_h265_parameters`]), do so before calling
/// [`VideoFrameStart::parameters`].
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
    pub fn new(parameters: &VideoParameters, options: PacketizeOptions) -> Result<Self, Error> {
        match parameters.codec_params() {
            #[cfg(feature = "h264")]
            VideoParametersCodec::H264 { .. } => super::h264::Packetizer::new(parameters, options)
                .map(|p| Self(VideoPacketizerInner::H264(Box::new(p)))),
            #[cfg(feature = "h265")]
            VideoParametersCodec::H265 { .. } => super::h265::Packetizer::new(parameters, options)
                .map(|p| Self(VideoPacketizerInner::H265(Box::new(p)))),
            _ => Err(wrap!(ErrorInt::InvalidArgument(format!(
                "packetizing {} is unsupported",
                parameters.rfc6381_codec()
            )))),
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

    /// Sets new parameters, taking effect with the next frame.
    ///
    /// If they differ from the current parameters, they're inserted into the
    /// stream before that frame (unless the parameter set insertion option is
    /// [`ParameterSetInsertion::Never`]). If they're the same, this does
    /// nothing, so it's fine to call before every frame.
    ///
    /// Returns an error if the parameters are for a different codec.
    pub fn set_parameters(&mut self, parameters: &VideoParameters) -> Result<(), Error> {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref mut p) => p.set_parameters(parameters),
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref mut p) => p.set_parameters(parameters),
        }
    }

    /// Starts a new frame, ending any frame in progress.
    pub fn start_frame(&mut self, frame: FrameInfo, sink: &mut impl PayloadSink) {
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
    /// start of the first chunk. Parameter set NAL units are passed through
    /// as-is; to have the packetizer manage them, use
    /// [`VideoPacketizer::set_parameters`] instead.
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
    /// For H.264 and H.265, in-band parameter sets are removed from the data
    /// and applied via [`VideoPacketizer::set_parameters`], then reinserted as
    /// the [`PacketizeOptions`] specify.
    ///
    /// Returns an error (without emitting any payloads) if the data isn't
    /// validly framed or its parameter sets are invalid.
    pub fn push_frame(
        &mut self,
        frame: FrameInfo,
        framing: super::h26x::Framing,
        data: &[u8],
        sink: &mut impl PayloadSink,
    ) -> Result<(), Error> {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref mut p) => p.push_frame(frame, framing, data, sink),
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref mut p) => p.push_frame(frame, framing, data, sink),
        }
    }

    /// Notes that the input lost data.
    ///
    /// Abandons any frame in progress (payloads already delivered stay
    /// delivered) and calls [`PayloadSink::discontinuity`].
    pub fn discontinuity(&mut self, sink: &mut impl PayloadSink) {
        match self.0 {
            #[cfg(feature = "h264")]
            VideoPacketizerInner::H264(ref mut p) => p.discontinuity(sink),
            #[cfg(feature = "h265")]
            VideoPacketizerInner::H265(ref mut p) => p.discontinuity(sink),
        }
    }
}

/// Returns the payload format for `parameters`, if they can be packetized.
pub(super) fn payload_format(parameters: &VideoParameters) -> Option<PayloadFormat> {
    match parameters.codec_params() {
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

/// Splits framed H.26x data into NAL units.
#[cfg_attr(not(any(feature = "h264", feature = "h265")), allow(dead_code))]
pub(super) fn split_nals(
    framing: super::h26x::Framing,
    mut data: &[u8],
) -> Result<Vec<&[u8]>, String> {
    let mut nals = Vec::new();
    match framing {
        super::h26x::Framing::FourByteLength => {
            while !data.is_empty() {
                let Some((len, rest)) = data.split_first_chunk::<4>() else {
                    return Err("truncated NAL length".into());
                };
                let len = crate::to_usize(u32::from_be_bytes(*len));
                let Some((nal, rest)) = rest.split_at_checked(len) else {
                    return Err(format!(
                        "NAL length {len} exceeds remaining {} bytes",
                        rest.len()
                    ));
                };
                if nal.is_empty() {
                    return Err("empty NAL".into());
                }
                nals.push(nal);
                data = rest;
            }
        }
        super::h26x::Framing::AnnexB => {
            if data.is_empty() {
                return Ok(nals);
            }
            let finder = memchr::memmem::Finder::new(&[0, 0, 1][..]);
            let mut starts = finder.find_iter(data).map(|p| (p, p + 3)).peekable();
            if !starts
                .peek()
                .is_some_and(|&(p, _)| data[..p].iter().all(|&b| b == 0))
            {
                return Err("Annex B data doesn't begin with a start code".into());
            }
            while let Some((_, body_start)) = starts.next() {
                let mut end = starts.peek().map_or(data.len(), |&(p, _)| p);
                while end > body_start && data[end - 1] == 0 {
                    end -= 1; // trailing_zero_8bits or the next start code's zero_byte.
                }
                if end > body_start {
                    nals.push(&data[body_start..end]);
                }
            }
        }
    }
    Ok(nals)
}
