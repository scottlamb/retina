// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Codec-specific logic (for audio, video, and application media types).
//!
//! This has a receive side and a send side, each usable by either a client or
//! a server:
//!
//! | | receive side | send side |
//! |---|---|---|
//! | used by | client `PLAY`; server `RECORD` | server `PLAY`; client `RECORD` |
//! | converts | RTP packets → frames | frames → RTP payloads |
//! | entry point | [`Depacketizer`] | [`VideoPacketizer`] |
//! | delivers to | [`VideoHandler`], [`AudioHandler`], [`MessageHandler`] | [`PayloadSink`] |
//!
//! Parameter types such as [`VideoParameters`], and [`PayloadFormat`], are
//! shared by both. A proxy can connect the receive side to the send side; see
//! "Repacketizing" on [`VideoPacketizer`].
//!
//! The send side requires the `unstable-send` feature and is exempt from
//! semver: it may change in any release.

#![cfg_attr(docsrs, feature(doc_cfg))]

use std::borrow::Cow;
use std::num::NonZeroU8;
use std::num::{NonZeroU16, NonZeroU32};

use bytes::Bytes;

use crate::Error;
use crate::error::ErrorInt;
use crate::rtp::ReceivedPacketRef;

/// Writes an `.mp4` (more properly, ISO/IEC 14496-12 BMFF) box.
///
/// See ISO/IEC 14496-12 section 4.2. This macro reserves space for the
/// compact/32-bit size, writes the compact/32-bit type (specified in `fourcc`),
/// runs the supplied block `b` which is expected to fill the contents, and then
/// sets the length accordingly.
macro_rules! write_mp4_box {
    ($buf:expr, $fourcc:expr, $b:block) => {{
        let _: &mut Vec<u8> = $buf; // type-check.
        let pos_start = $buf.len();
        let fourcc: [u8; 4] = $fourcc;
        $buf.extend_from_slice(&[0, 0, 0, 0, fourcc[0], fourcc[1], fourcc[2], fourcc[3]]);
        let r = {
            $b;
        };
        let pos_end = $buf.len();
        let len = pos_end
            .checked_sub(pos_start)
            .expect("buf should not shrink during `write_mp4_box` block");
        let len = u32::try_from(len).expect("box size should not exceed u32::MAX");
        $buf[pos_start..pos_start + 4].copy_from_slice(&len.to_be_bytes()[..]);
        r
    }};
}

/// Overwrites a buffer with a varint length, returning the length of the length.
/// See ISO/IEC 14496-1 section 8.3.3.
fn set_iso14496_length(len: usize, data: &mut [u8]) -> usize {
    if len < 1 << 7 {
        data[0] = len as u8;
        1
    } else if len < 1 << 14 {
        data[0] = ((len & 0x7F) | 0x80) as u8;
        data[1] = (len >> 7) as u8;
        2
    } else if len < 1 << 21 {
        data[0] = ((len & 0x7F) | 0x80) as u8;
        data[1] = (((len >> 7) & 0x7F) | 0x80) as u8;
        data[2] = (len >> 14) as u8;
        3
    } else if len < 1 << 28 {
        data[0] = ((len & 0x7F) | 0x80) as u8;
        data[1] = (((len >> 7) & 0x7F) | 0x80) as u8;
        data[2] = (((len >> 14) & 0x7F) | 0x80) as u8;
        data[3] = (len >> 21) as u8;
        4
    } else {
        // BaseDescriptor sets a maximum length of 2**28 - 1.
        panic!("ISO 14496 descriptor should not exceed maximum length of 2**28 - 1")
    }
}

/// Writes a descriptor tag and length for everything appended in the supplied
/// scope. See ISO/IEC 14496-1 Table 1 for the `tag`.
macro_rules! write_mpeg4_descriptor {
    ($buf:expr, $tag:expr, $b:block) => {{
        let _: &mut Vec<u8> = $buf; // type-check.
        let _: u8 = $tag;
        let pos_start = $buf.len();

        // Overallocate room for the varint length and append the body.
        $buf.extend_from_slice(&[$tag, 0, 0, 0, 0]);
        let r = {
            $b;
        };
        let pos_end = $buf.len();

        // Then fix it afterward: write the correct varint length and move
        // the body backward. This approach seems better than requiring the
        // caller to first prepare the body in a separate allocation (and
        // awkward code ordering), or (as ffmpeg does) writing a "varint"
        // which is padded with leading 0x80 bytes.
        let len = pos_end
            .checked_sub(pos_start + 5)
            .expect("`buf` should not shrink during `write_iso14496_descriptor` block");
        let len_len =
            crate::codec::set_iso14496_length(len, &mut $buf[pos_start + 1..pos_start + 4]);
        $buf.copy_within(pos_start + 5..pos_end, pos_start + 1 + len_len);
        $buf.truncate(pos_end + len_len - 4);
        r
    }};
}

pub mod aac;
pub(crate) mod events;
pub(crate) mod g723;
#[cfg(any(feature = "h264", feature = "h265"))]
pub mod h26x;
pub(crate) mod jpeg;

#[cfg(feature = "h264")]
pub mod h264;

#[cfg(feature = "h265")]
#[doc(hidden)]
pub mod h265;

pub(crate) mod onvif;
#[cfg(feature = "unstable-send")]
pub(crate) mod packetize;
pub(crate) mod simple_audio;

#[cfg(test)]
mod testutil;

pub(crate) use events::FrameBody;
pub use events::{
    Accumulate, AudioFrameRef, AudioHandler, Corruption, Loss, LossReason, MessageFrameRef,
    MessageHandler, Position, VideoData, VideoFrameEnd, VideoFrameStart, VideoHandler,
};
#[cfg(feature = "unstable-send")]
pub use packetize::{
    Payload, PayloadSink, VideoFrameInfo, VideoPacketizer, VideoPacketizerOptions,
};

/// Options controlling how frames are formatted.
///
/// This controls codec-specific framing (e.g. H.26x NAL unit framing, AAC
/// framing) and parameter set insertion. Each codec picks out the knobs
/// relevant to it and ignores the rest.
///
/// It's supplied wherever frame data or matching "extra data" is produced:
/// [`VideoFrameEnd::complete_frame`], [`VideoFrameEnd::visit_frame_data`],
/// [`AudioFrameRef::data`], [`VideoParameters::extra_data`], and
/// [`AudioParameters::extra_data`]. On the send side, it describes
/// the frame data supplied to [`VideoPacketizer::push_frame`], which uses
/// only the framing knobs.
///
/// Preset constants are provided for common use cases:
///
/// * [`FrameFormat::MP4`] — suitable for writing ISO BMFF / `.mp4` files.
/// * [`FrameFormat::SIMPLE`] — self-describing output (Annex B + inline
///   parameter sets for H.26x, ADTS for AAC), suitable for piping to a decoder
///   without needing to handle extra data separately.
///
/// This is `#[non_exhaustive]` so that knobs for more codecs can be added
/// later. Start from a preset (or `Default::default()`) and adjust it with
/// the `with_*` methods or by assigning fields:
///
/// ```
/// use retina::codec::{FrameFormat, ParameterSetInsertion};
/// const FORMAT: FrameFormat =
///     FrameFormat::SIMPLE.with_parameter_set_insertion(ParameterSetInsertion::OnChange);
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct FrameFormat {
    /// How to frame H.26x NAL units.
    #[cfg(any(feature = "h264", feature = "h265"))]
    pub h26x_framing: h26x::Framing,

    /// When to insert parameter sets (SPS/PPS/VPS) into frame data.
    pub parameter_set_insertion: ParameterSetInsertion,

    /// How to frame AAC audio.
    pub aac_framing: aac::Framing,
}

impl FrameFormat {
    /// Suitable for ISO BMFF / `.mp4` files: 4-byte length-prefixed NALs,
    /// no inline parameter sets (they go in the sample entry), raw AAC.
    pub const MP4: Self = Self {
        #[cfg(any(feature = "h264", feature = "h265"))]
        h26x_framing: h26x::Framing::FourByteLength,
        parameter_set_insertion: ParameterSetInsertion::Never,
        aac_framing: aac::Framing::Raw,
    };

    /// Suitable for piping to a decoder without handling extra data separately:
    /// Annex B start codes, parameter sets prepended to every key frame,
    /// ADTS-wrapped AAC.
    pub const SIMPLE: Self = Self {
        #[cfg(any(feature = "h264", feature = "h265"))]
        h26x_framing: h26x::Framing::AnnexB,
        parameter_set_insertion: ParameterSetInsertion::EachKeyFrame,
        aac_framing: aac::Framing::Adts,
    };

    /// Returns a copy with [`FrameFormat::h26x_framing`] replaced.
    #[cfg(any(feature = "h264", feature = "h265"))]
    pub const fn with_h26x_framing(mut self, h26x_framing: h26x::Framing) -> Self {
        self.h26x_framing = h26x_framing;
        self
    }

    /// Returns a copy with [`FrameFormat::parameter_set_insertion`] replaced.
    pub const fn with_parameter_set_insertion(
        mut self,
        parameter_set_insertion: ParameterSetInsertion,
    ) -> Self {
        self.parameter_set_insertion = parameter_set_insertion;
        self
    }

    /// Returns a copy with [`FrameFormat::aac_framing`] replaced.
    pub const fn with_aac_framing(mut self, aac_framing: aac::Framing) -> Self {
        self.aac_framing = aac_framing;
        self
    }
}

/// When to insert parameter sets (SPS/PPS for H.264; VPS/SPS/PPS for H.265)
/// in-band.
///
/// This is used in two places:
///
/// *   [`FrameFormat::parameter_set_insertion`]: when a depacketizer prepends
///     parameter sets to the frame data it produces, as with
///     [`VideoFrameEnd::complete_frame`]. A depacketizer only prepends them
///     to random access points.
/// *   [`VideoPacketizerOptions::parameter_set_insertion`]: when a packetizer sends
///     parameter sets in the RTP stream, before a frame's own codec units.
///
/// Either way, they're also available out of band via [`VideoParameters`]
/// (and, for an RTP stream, the SDP; see [`VideoPacketizer::payload_format`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum ParameterSetInsertion {
    /// Insert at each key frame (random access point), and whenever the
    /// parameters change. Default.
    #[default]
    EachKeyFrame,

    /// Insert only when the parameters change.
    OnChange,

    /// Never insert in-band.
    Never,
}

/// Reference to parameters which describe a stream.
///
/// Parameters are often, but not always, available immediately
/// after `DESCRIBE` via [`crate::client::Stream::parameters`]. They should
/// always be available after the first frame.
///
/// Video streams' parameters may change mid-stream; if so, the frame which
/// changed them will have [`VideoFrameEnd::has_new_parameters`] set, and
/// [`VideoFrameEnd::parameters`] and [`Depacketizer::parameters`] will
/// return the new value.
///
/// Currently audio and message streams' parameters never change mid-stream.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ParametersRef<'a> {
    Video(&'a VideoParameters),
    Audio(&'a AudioParameters),
    Message(&'a MessageParameters),
}

/// Owned parameters which describe a stream; see [`ParametersRef`].
#[derive(Clone, Debug)]
pub(crate) enum Parameters {
    Video(VideoParameters),
    Audio(AudioParameters),
    Message(MessageParameters),
}

impl Parameters {
    pub(crate) fn as_ref(&self) -> ParametersRef<'_> {
        match self {
            Self::Video(p) => ParametersRef::Video(p),
            Self::Audio(p) => ParametersRef::Audio(p),
            Self::Message(p) => ParametersRef::Message(p),
        }
    }
}

impl From<ParametersRef<'_>> for Parameters {
    fn from(p: ParametersRef<'_>) -> Self {
        match p {
            ParametersRef::Video(p) => Self::Video(p.clone()),
            ParametersRef::Audio(p) => Self::Audio(p.clone()),
            ParametersRef::Message(p) => Self::Message(p.clone()),
        }
    }
}

/// Parameters which describe a video stream.
///
/// A video stream's parameters are often, but not always, available immediately
/// after `DESCRIBE` via [`crate::client::Stream::parameters`]. They should
/// always be available after the first frame.
///
/// Video streams' parameters may change mid-stream; if so, the frame which
/// changed them will have [`VideoFrameEnd::has_new_parameters`] set, and
/// [`VideoFrameEnd::parameters`] and [`VideoDepacketizer::parameters`] will
/// return the new value.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct VideoParameters {
    all_pixel_dimensions: AllPixelDimensions,
    rfc6381_codec: String,
    pixel_aspect_ratio: Option<(u32, u32)>,
    frame_rate: Option<(u32, u32)>,

    /// For H.264/H.265, the `AVCDecoderConfigurationRecord` or
    /// `HEVCDecoderConfigurationRecord`. Empty for other codecs.
    decoder_config_record: Bytes,

    /// For H.264/H.265, the parameter sets with Annex B start codes. Empty for other codecs.
    #[cfg(any(feature = "h264", feature = "h265"))]
    annex_b_parameter_sets: Bytes,

    /// The codec, for internal use in sample entry construction.
    ///
    /// This is more straightforward than reparsing the RFC 6381 codec string.
    codec: VideoParametersCodec,
}

/// Public for fuzz testing.
#[doc(hidden)]
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct AllPixelDimensions {
    pub display: (u16, u16),
    pub coded: (u16, u16),
}

impl VideoParameters {
    /// Returns parameters for the given H.264 parameter sets.
    ///
    /// It's sometimes useful to "fix" a server's parameters, e.g.:
    ///
    /// * adding missing pixel aspect ratio information to the SPS VUI so that
    ///   anamorphic video is displayed at the correct aspect ratio.
    /// * adding missing bitstream restrictions such as `num_reorder_frames = 0`
    ///   that significantly reduce decode latency.
    /// * removing garbage after the RBSP trailing bits.
    ///
    /// Retina currently does not support directly making these changes itself, but
    /// callers can use e.g. [`h264_reader`](https://crates.io/crates/h264_reader)
    /// to rewrite the SPS, then use Retina's logic to repackage the parameters into
    /// a [`VideoParameters`]. Pass these to
    /// [`VideoFrameStart::set_parameters`] or
    /// [`VideoPacketizer::set_parameters`].
    ///
    /// Each set is a raw NAL unit, as in [`VideoParameters::parameter_sets`]:
    /// it includes its NAL header, with no start code or length prefix. They
    /// may be in any order. Currently this requires exactly one SPS and one
    /// PPS; a future version may accept several of each (with distinct ids).
    ///
    /// Returns an error if the sets are invalid.
    #[cfg(feature = "h264")]
    pub fn from_h264_parameter_sets<'a>(
        sets: impl IntoIterator<Item = &'a [u8]>,
    ) -> Result<Self, Error> {
        h26x::Codec::H264
            .parameters_from_unordered_sets(sets)
            .map_err(|e| wrap!(ErrorInt::InvalidArgument(e)))
    }

    /// Returns parameters for the given H.265 parameter sets.
    ///
    /// As in [`VideoParameters::from_h264_parameter_sets`], but this
    /// currently requires exactly one VPS, one SPS, and one PPS.
    #[cfg(feature = "h265")]
    pub fn from_h265_parameter_sets<'a>(
        sets: impl IntoIterator<Item = &'a [u8]>,
    ) -> Result<Self, Error> {
        h26x::Codec::H265
            .parameters_from_unordered_sets(sets)
            .map_err(|e| wrap!(ErrorInt::InvalidArgument(e)))
    }

    /// Returns a codec description in
    /// [RFC-6381](https://tools.ietf.org/html/rfc6381) form, eg `avc1.4D401E`.
    // TODO: use https://github.com/dholroyd/rfc6381-codec crate once published?
    pub fn rfc6381_codec(&self) -> &str {
        &self.rfc6381_codec
    }

    /// Returns a builder for an `.mp4` `VideoSampleEntry` box (as defined in
    /// ISO/IEC 14496-12).
    pub fn mp4_sample_entry(&self) -> VideoSampleEntryBuilder<'_> {
        VideoSampleEntryBuilder {
            params: self,
            aspect_ratio_override: None,
        }
    }

    /// Returns the *cropped* dimensions of the video frame in pixels, as `(width, height)`.
    /// These are sometimes called the display dimensions, although they do not take the
    /// pixel aspect ratio into account.
    ///
    /// See also [`coded_pixel_dimensions`](Self::coded_pixel_dimensions).
    pub fn pixel_dimensions(&self) -> (u32, u32) {
        let (width, height) = self.all_pixel_dimensions.display;
        (width.into(), height.into())
    }

    /// Returns the *coded* dimensions of the video frame in pixels, as `(width, height)`.
    ///
    /// See [`pixel_dimensions`](Self::pixel_dimensions) for the more commonly
    /// needed *display* dimensions. The coded dimensions are useful to put
    /// inside a [WebCodecs `VideoDecoderConfig`](https://www.w3.org/TR/webcodecs/#dom-videodecoderconfig-codedwidth);
    /// Safari appears to require them.
    ///
    /// # What are coded dimensions?
    ///
    /// Video codecs aren't designed for arbitrary pixels dimensions. H.264 dimensions
    /// for example must be specified in "macroblocks" of 16x16 pixels. So an encoder
    /// will round say a 30x30 input video up to a coded size of 32x32, perhaps with
    /// an extra 2 black pixels in each dimension. A decoder will crop the 32x32 video
    /// back to a display size of 30x30.
    pub fn coded_pixel_dimensions(&self) -> (u32, u32) {
        let (width, height) = self.all_pixel_dimensions.coded;
        (width.into(), height.into())
    }

    /// Returns the displayed size of a pixel, if known, as a dimensionless ratio `(h_spacing, v_spacing)`.
    /// This is as specified in [ISO/IEC 14496-12:2015](https://standards.iso.org/ittf/PubliclyAvailableStandards/c068960_ISO_IEC_14496-12_2015.zip])
    /// section 12.1.4.
    ///
    /// It's common for IP cameras to use [anamorphic](https://en.wikipedia.org/wiki/Anamorphic_format) sub streams.
    /// Eg a 16x9 camera may export the same video source as a 1920x1080 "main"
    /// stream and a 704x480 "sub" stream, without cropping. The former has a
    /// pixel aspect ratio of `(1, 1)` while the latter has a pixel aspect ratio
    /// of `(40, 33)`.
    pub fn pixel_aspect_ratio(&self) -> Option<(u32, u32)> {
        self.pixel_aspect_ratio
    }

    /// Returns the maximum frame rate in seconds as `(numerator, denominator)`,
    /// if known.
    ///
    /// May not be minimized, and may not be in terms of the clock rate. Eg 15
    /// frames per second might be returned as `(1, 15)` or `(6000, 90000)`. The
    /// standard NTSC framerate (roughly 29.97 fps) might be returned as
    /// `(1001, 30000)`.
    ///
    /// TODO: maybe return in clock rate units instead?
    /// TODO: expose fixed vs max distinction (see H.264 fixed_frame_rate_flag).
    pub fn frame_rate(&self) -> Option<(u32, u32)> {
        self.frame_rate
    }

    /// Returns the parameter sets, as raw NAL units.
    ///
    /// For H.264, these are the SPS and PPS; for H.265, the VPS, SPS, and
    /// PPS. Each includes its NAL header, with no start code or length prefix.
    /// They're in the order a packetizer or depacketizer inserts them in-band.
    /// Other codecs have none.
    ///
    /// Currently there's exactly one of each type, but a future version may
    /// support streams with several (with distinct ids), so look at each NAL
    /// header to find the type rather than relying on position. To insert the
    /// parameter sets in-band yourself, [`VideoParameters::extra_data`] with
    /// [`h26x::Framing::AnnexB`] returns them already framed.
    pub fn parameter_sets(&self) -> impl Iterator<Item = &[u8]> {
        let sets: [Option<&Bytes>; 3] = match &self.codec {
            #[cfg(feature = "h264")]
            VideoParametersCodec::H264 { sps, pps } => [Some(sps), Some(pps), None],
            #[cfg(feature = "h265")]
            VideoParametersCodec::H265 { vps, sps, pps } => [Some(vps), Some(sps), Some(pps)],
            VideoParametersCodec::Jpeg => [None; 3],
        };
        sets.into_iter().flatten().map(|s| &s[..])
    }

    /// Returns the codec-specific "extra data" to feed to a decoder (such as
    /// FFmpeg) alongside frames in the given format.
    ///
    /// For H.264 and H.265, this depends on [`FrameFormat::h26x_framing`]:
    ///
    /// * [`h26x::Framing::FourByteLength`]: an `AVCDecoderConfigurationRecord` or
    ///   `HEVCDecoderConfigurationRecord`, as in ISO/IEC 14496-15.
    /// * [`h26x::Framing::AnnexB`]: the parameter sets, each preceded by an
    ///   Annex B start code.
    pub fn extra_data(&self, format: FrameFormat) -> &[u8] {
        #[cfg(any(feature = "h264", feature = "h265"))]
        if format.h26x_framing == h26x::Framing::AnnexB {
            return &self.annex_b_parameter_sets;
        }
        let _ = format;
        &self.decoder_config_record
    }

    /// Returns the RTP payload format for sending a stream with these
    /// parameters, as a [`VideoPacketizer`] would, or `None` if Retina can't
    /// packetize this codec.
    ///
    /// Currently H.264 and H.265 are supported.
    ///
    /// This requires the `unstable-send` feature.
    #[cfg(feature = "unstable-send")]
    pub fn payload_format(&self) -> Option<PayloadFormat> {
        packetize::payload_format(self)
    }
}

impl std::fmt::Debug for VideoParameters {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VideoParameters")
            .field("rfc6381_codec", &self.rfc6381_codec)
            .field("pixel_dimensions", &self.all_pixel_dimensions.display)
            .field("coded_pixel_dimensions", &self.all_pixel_dimensions.coded)
            .field("pixel_aspect_ratio", &self.pixel_aspect_ratio)
            .field("frame_rate", &self.frame_rate)
            .field(
                "decoder_config_record",
                &crate::hex::LimitedHex::new(&self.decoder_config_record, 256),
            )
            .finish()
    }
}

/// The codec of a [`VideoParameters`], with its codec-specific parameters.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum VideoParametersCodec {
    #[cfg(feature = "h264")]
    H264 {
        sps: Bytes,
        pps: Bytes,
    },
    #[cfg(feature = "h265")]
    H265 {
        vps: Bytes,
        sps: Bytes,
        pps: Bytes,
    },
    Jpeg,
}

impl std::fmt::Debug for VideoParametersCodec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            #[cfg(feature = "h264")]
            Self::H264 { sps, pps } => f
                .debug_struct("H264")
                .field("sps", &crate::hex::LimitedHex::new(sps, 256))
                .field("pps", &crate::hex::LimitedHex::new(pps, 256))
                .finish(),
            #[cfg(feature = "h265")]
            Self::H265 { vps, sps, pps } => f
                .debug_struct("H265")
                .field("vps", &crate::hex::LimitedHex::new(vps, 256))
                .field("sps", &crate::hex::LimitedHex::new(sps, 256))
                .field("pps", &crate::hex::LimitedHex::new(pps, 256))
                .finish(),
            Self::Jpeg => write!(f, "Jpeg"),
        }
    }
}

impl VideoParametersCodec {
    fn visual_sample_entry_box_type(&self) -> [u8; 4] {
        match self {
            #[cfg(feature = "h264")]
            VideoParametersCodec::H264 { .. } => *b"avc1",
            #[cfg(feature = "h265")]
            VideoParametersCodec::H265 { .. } => *b"hvc1",
            VideoParametersCodec::Jpeg => *b"mp4v",
        }
    }
}

pub struct VideoSampleEntryBuilder<'p> {
    params: &'p VideoParameters,
    aspect_ratio_override: Option<(u16, u16)>,
}

impl VideoSampleEntryBuilder<'_> {
    /// Overrides the codec-level pixel aspect ratio via a `pasp` box.
    #[inline]
    pub fn with_aspect_ratio(self, aspect_ratio: (u16, u16)) -> Self {
        Self {
            aspect_ratio_override: Some(aspect_ratio),
            ..self
        }
    }

    /// Builds the `.mp4` `VisualSampleEntry` box, if possible.
    pub fn build(self) -> Result<Vec<u8>, Error> {
        let mut buf = Vec::new();
        write_mp4_box!(
            &mut buf,
            self.params.codec.visual_sample_entry_box_type(),
            {
                // SampleEntry, section 8.5.2.2.
                buf.extend_from_slice(&0u32.to_be_bytes()[..]); // pre_defined + reserved
                buf.extend_from_slice(&1u32.to_be_bytes()[..]); // data_reference_index = 1

                // VisualSampleEntry, section 12.1.3.2.
                buf.extend_from_slice(&[0; 16]);
                buf.extend_from_slice(
                    &self.params.all_pixel_dimensions.display.0.to_be_bytes()[..],
                );
                buf.extend_from_slice(
                    &self.params.all_pixel_dimensions.display.1.to_be_bytes()[..],
                );
                buf.extend_from_slice(&[
                    0x00, 0x48, 0x00, 0x00, // horizresolution
                    0x00, 0x48, 0x00, 0x00, // vertresolution
                    0x00, 0x00, 0x00, 0x00, // reserved
                    0x00, 0x01, // frame count
                    0x00, 0x00, 0x00, 0x00, // compressorname
                    0x00, 0x00, 0x00, 0x00, //
                    0x00, 0x00, 0x00, 0x00, //
                    0x00, 0x00, 0x00, 0x00, //
                    0x00, 0x00, 0x00, 0x00, //
                    0x00, 0x00, 0x00, 0x00, //
                    0x00, 0x00, 0x00, 0x00, //
                    0x00, 0x00, 0x00, 0x00, //
                    0x00, 0x18, 0xff, 0xff, // depth + pre_defined
                ]);

                // Codec-specific portion.
                match self.params.codec {
                    #[cfg(feature = "h264")]
                    VideoParametersCodec::H264 { .. } => {
                        write_mp4_box!(&mut buf, *b"avcC", {
                            buf.extend_from_slice(&self.params.decoder_config_record);
                        });
                    }
                    #[cfg(feature = "h265")]
                    VideoParametersCodec::H265 { .. } => {
                        write_mp4_box!(&mut buf, *b"hvcC", {
                            buf.extend_from_slice(&self.params.decoder_config_record);
                        });
                    }
                    VideoParametersCodec::Jpeg => {
                        jpeg::append_esds(&mut buf);
                    }
                }

                // pasp box, if requested.
                if let Some(aspect_ratio) = self.aspect_ratio_override {
                    write_mp4_box!(&mut buf, *b"pasp", {
                        buf.extend_from_slice(&u32::from(aspect_ratio.0).to_be_bytes()[..]);
                        buf.extend_from_slice(&u32::from(aspect_ratio.1).to_be_bytes()[..]);
                    });
                }
            }
        );
        Ok(buf)
    }
}

/// Parameters which describe an audio stream.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AudioParameters {
    rfc6381_codec: Option<String>,
    frame_length: Option<NonZeroU32>,
    clock_rate: u32,
    channels: NonZeroU16,
    extra_data: Vec<u8>,
    codec: AudioParametersCodec,
}

impl std::fmt::Debug for AudioParameters {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AudioParameters")
            .field("rfc6381_codec", &self.rfc6381_codec)
            .field("frame_length", &self.frame_length)
            .field(
                "extra_data",
                &crate::hex::LimitedHex::new(&self.extra_data, 256),
            )
            .finish()
    }
}

impl AudioParameters {
    pub fn rfc6381_codec(&self) -> Option<&str> {
        self.rfc6381_codec.as_deref()
    }

    /// The length of each frame (in clock_rate units), if fixed.
    pub fn frame_length(&self) -> Option<NonZeroU32> {
        self.frame_length
    }

    pub fn clock_rate(&self) -> u32 {
        self.clock_rate
    }

    /// Returns the number of audio channels.
    ///
    /// This can be passed to a [WebCodecs `AudioDecoderConfig.numberOfChannels`](https://www.w3.org/TR/webcodecs/#dom-audiodecoderconfig-numberofchannels).
    pub fn channels(&self) -> NonZeroU16 {
        self.channels
    }

    /// Returns the codec-specific "extra data" to feed to a decoder alongside
    /// frames in the given format.
    ///
    /// For AAC, this depends on [`FrameFormat::aac_framing`]:
    ///
    /// * [`aac::Framing::Raw`]: the `AudioSpecificConfig`, as in ISO/IEC 14496-3.
    /// * [`aac::Framing::Adts`]: empty. ADTS frames are self-describing, and a
    ///   decoder given an `AudioSpecificConfig` would expect raw frames.
    pub fn extra_data(&self, format: FrameFormat) -> &[u8] {
        match (&self.codec, format.aac_framing) {
            (AudioParametersCodec::Aac { .. }, aac::Framing::Adts) => &[],
            _ => &self.extra_data,
        }
    }

    /// Returns a builder for an `.mp4` `AudioSampleEntry` box (as defined in ISO/IEC 14496-12).
    pub fn mp4_sample_entry(&self) -> AudioSampleEntryBuilder<'_> {
        AudioSampleEntryBuilder { params: self }
    }
}

/// Holds codec-specific data needed from the `AudioParameters`.
#[derive(Clone, PartialEq, Eq, Hash)]
enum AudioParametersCodec {
    Aac { channels_config_id: NonZeroU8 },
    Other,
}

pub struct AudioSampleEntryBuilder<'p> {
    params: &'p AudioParameters,
}

impl AudioSampleEntryBuilder<'_> {
    /// Builds the `.mp4` `AudioSampleEntry` box, if possible.
    ///
    /// Not all codecs can be placed into a `.mp4` file, and even for supported codecs there
    /// may be unsupported edge cases.
    pub fn build(self) -> Result<Vec<u8>, Error> {
        match self.params.codec {
            AudioParametersCodec::Aac { channels_config_id } => aac::make_sample_entry(
                channels_config_id,
                self.params.clock_rate,
                &self.params.extra_data,
            ),
            AudioParametersCodec::Other => {
                bail!(ErrorInt::Unsupported(
                    "unsupported audio codec for mp4".to_owned()
                ));
            }
        }
    }
}

/// Parameters which describe a message stream, for `application` media types.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MessageParameters(onvif::CompressionType);

/// Returns the loss to report before a packet with the given continuity, if any.
fn packet_loss_reason(continuity: crate::rtp::Continuity) -> Option<LossReason> {
    match continuity {
        crate::rtp::Continuity::Contiguous => None,
        crate::rtp::Continuity::Lost(n) => Some(LossReason::PacketLoss { packets: n.get() }),
        crate::rtp::Continuity::Discontinuity => Some(LossReason::Discontinuity),
    }
}

/// Reports packet loss before a packet is pushed, as all depacketizers do.
///
/// The H.264 and H.265 depacketizers do this themselves, via their analyzers.
fn report_packet_loss<Ctx>(pkt: &ReceivedPacketRef<'_, Ctx>, loss: impl FnOnce(&Loss<'_, Ctx>)) {
    if let Some(reason) = packet_loss_reason(pkt.meta.continuity) {
        loss(&Loss {
            ctx: &pkt.meta.ctx,
            reason,
        });
    }
}

/// Reports corrupt data found in a packet.
fn report_corrupt<Ctx>(
    pkt: &ReceivedPacketRef<'_, Ctx>,
    description: String,
    loss: impl FnOnce(&Loss<'_, Ctx>),
) {
    loss(&Loss {
        ctx: &pkt.meta.ctx,
        reason: LossReason::Corrupt(Corruption::new(description)),
    });
}

/// Turns RTP packets into video frames, delivering them to a [`VideoHandler`].
///
/// This is a sans-I/O interface: it's up to the caller to receive packets
/// (e.g. from a [`crate::client`] session, a network capture, or a file)
/// into a [`crate::buf::MarkBuf`] and supply them via
/// [`VideoDepacketizer::push`].
///
/// `Ctx` is a caller-chosen packet context type; see [`VideoHandler`].
#[derive(Debug)]
pub struct VideoDepacketizer<Ctx> {
    inner: VideoInner<Ctx>,

    /// For JPEG; the H.264 and H.265 analyzers track their own.
    decodability: DecodabilityState,
}

/// State for [`DecodabilityTracker`], kept between calls.
#[derive(Copy, Clone, Debug)]
pub(crate) struct DecodabilityState {
    current: Decodability,

    /// The decodability state before the in-progress frame, if any, so that
    /// `frame_end` can redo `frame_start`'s update with authoritative values.
    before_frame: Option<Decodability>,
}

impl Default for DecodabilityState {
    fn default() -> Self {
        Self {
            current: Decodability {
                tainted: true,
                rasl_decodable: false,
            },
            before_frame: None,
        }
    }
}

/// State for computing [`VideoFrameEnd::is_decodable`].
#[derive(Copy, Clone, Debug)]
struct Decodability {
    /// True if data has been lost since the last random access point.
    tainted: bool,

    /// True if the last random access point was reached with no data lost
    /// since the one before it, so its RASL pictures' references are intact.
    rasl_decodable: bool,
}

impl Decodability {
    /// Updates the state for a frame, returning whether the frame is decodable.
    fn update(
        &mut self,
        is_random_access_point: bool,
        is_rasl: bool,
        missing_prefix: bool,
    ) -> bool {
        if missing_prefix {
            // Loss taints until the next *complete* random access point.
            self.tainted = true;
            return false;
        }
        if is_random_access_point {
            self.rasl_decodable = !self.tainted;
            self.tainted = false;
        }
        !self.tainted && (!is_rasl || self.rasl_decodable)
    }
}

/// Wraps a [`VideoHandler`] to track [`VideoFrameEnd::is_decodable`].
pub(crate) struct DecodabilityTracker<'a, H> {
    pub(crate) state: &'a mut DecodabilityState,
    pub(crate) inner: &'a mut H,
}

impl<Ctx, H: VideoHandler<Ctx>> VideoHandler<Ctx> for DecodabilityTracker<'_, H> {
    fn frame_start(&mut self, frame_start: &mut VideoFrameStart<'_, Ctx>) -> Accumulate {
        self.state.before_frame = Some(self.state.current);
        frame_start.is_decodable = self.state.current.update(
            frame_start.is_random_access_point,
            frame_start.is_rasl,
            frame_start.missing_prefix,
        );
        self.inner.frame_start(frame_start)
    }

    #[inline]
    fn data(&mut self, data: &VideoData<'_>) {
        self.inner.data(data)
    }

    fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, Ctx>) {
        if let Some(before) = self.state.before_frame.take() {
            self.state.current = before;
        }
        frame_end.is_decodable = self.state.current.update(
            frame_end.is_random_access_point,
            frame_end.is_rasl,
            frame_end.missing_prefix,
        );
        self.inner.frame_end(frame_end)
    }

    fn loss(&mut self, loss: &Loss<'_, Ctx>) {
        // Loss within a frame abandons it.
        self.state.before_frame = None;
        self.state.current.tainted = true;
        self.inner.loss(loss)
    }
}

#[derive(Debug)]
enum VideoInner<Ctx> {
    #[cfg(feature = "h264")]
    H264(Box<h264::Depacketizer<Ctx>>),
    #[cfg(feature = "h265")]
    H265(Box<h265::Depacketizer<Ctx>>),
    Jpeg(Box<jpeg::Depacketizer<Ctx>>),
}

impl<Ctx: Clone> VideoDepacketizer<Ctx> {
    /// Creates a depacketizer for the given RTP payload format.
    ///
    /// Arguments are from the SDP media description's `rtpmap` and `fmtp`
    /// attributes, for media type `video`. `encoding_name` is expected to be
    /// lowercase.
    ///
    /// Returns an error if the format is unsupported or the parameters are invalid.
    pub fn new(
        encoding_name: &str,
        clock_rate: u32,
        format_specific_params: Option<&str>,
    ) -> Result<Self, Error> {
        Self::new_inner(encoding_name, clock_rate, format_specific_params)
            .map_err(|e| wrap!(ErrorInt::InvalidArgument(e)))
    }

    #[cfg_attr(not(any(feature = "h264", feature = "h265")), allow(unused_variables))]
    fn new_inner(
        encoding_name: &str,
        clock_rate: u32,
        format_specific_params: Option<&str>,
    ) -> Result<Self, String> {
        let inner = match encoding_name {
            #[cfg(feature = "h264")]
            "h264" => VideoInner::H264(Box::new(h264::Depacketizer::new(
                clock_rate,
                format_specific_params,
            )?)),
            #[cfg(feature = "h265")]
            "h265" => VideoInner::H265(Box::new(h265::Depacketizer::new(
                clock_rate,
                format_specific_params,
            )?)),
            "jpeg" => VideoInner::Jpeg(Box::default()),
            _ => {
                return Err(format!(
                    "no video depacketizer for encoding_name {encoding_name}"
                ));
            }
        };
        Ok(Self {
            inner,
            decodability: DecodabilityState::default(),
        })
    }

    #[doc(hidden)]
    pub fn check_invariants(&self) {
        match &self.inner {
            #[cfg(feature = "h264")]
            VideoInner::H264(d) => d.check_invariants(),
            #[cfg(feature = "h265")]
            VideoInner::H265(d) => d.check_invariants(),
            VideoInner::Jpeg(_) => {}
        }
    }

    /// Limits the bytes retained for an in-progress frame.
    ///
    /// When a frame grows beyond this, the depacketizer discards it, reports
    /// [`LossReason::TooLarge`] to [`VideoHandler::loss`], and skips the rest
    /// of it, resynchronizing at the next frame boundary.
    ///
    /// For H.264 and H.265, this counts RTP payload bytes the depacketizer
    /// retains in the [`crate::buf::MarkBuf`]. That's the whole frame if the
    /// handler returns [`Accumulate::Yes`] from [`VideoHandler::frame_start`].
    /// With [`Accumulate::No`], it's the data before `frame_start` (such as
    /// parameter sets and SEI), plus at most about a packet after it, so only
    /// that part is limited.
    ///
    /// There's no limit by default. A [`crate::buf::MarkBuf`] limit set via
    /// [`crate::buf::MarkBuf::set_max_retained`] bounds memory regardless.
    pub fn set_max_frame_bytes(&mut self, max_frame_bytes: usize) {
        match &mut self.inner {
            #[cfg(feature = "h264")]
            VideoInner::H264(d) => d.set_max_frame_bytes(max_frame_bytes),
            #[cfg(feature = "h265")]
            VideoInner::H265(d) => d.set_max_frame_bytes(max_frame_bytes),
            VideoInner::Jpeg(d) => d.set_max_frame_bytes(max_frame_bytes),
        }
    }

    /// Returns the current parameters, if known.
    ///
    /// These may change as frames arrive; see
    /// [`VideoFrameEnd::has_new_parameters`].
    pub fn parameters(&self) -> Option<&VideoParameters> {
        match &self.inner {
            #[cfg(feature = "h264")]
            VideoInner::H264(d) => d.parameters(),
            #[cfg(feature = "h265")]
            VideoInner::H265(d) => d.parameters(),
            VideoInner::Jpeg(d) => d.parameters(),
        }
    }

    /// Supplies a new packet, delivering any resulting events to `handler`.
    ///
    /// This never fails: lost packets and corrupt data are reported via
    /// [`VideoHandler::loss`], and the depacketizer resynchronizes at the next
    /// frame boundary. It's up to the handler whether to treat this as fatal.
    ///
    /// # Panics
    ///
    /// Panics if a depacketizer which has retained data from one
    /// [`crate::buf::MarkBuf`] is supplied a packet from another.
    pub fn push(&mut self, pkt: &ReceivedPacketRef<'_, Ctx>, handler: &mut impl VideoHandler<Ctx>) {
        match &mut self.inner {
            // These report loss and track decodability via their analyzers.
            #[cfg(feature = "h264")]
            VideoInner::H264(d) => d.push(pkt, handler),
            #[cfg(feature = "h265")]
            VideoInner::H265(d) => d.push(pkt, handler),
            VideoInner::Jpeg(d) => {
                let handler = &mut DecodabilityTracker {
                    state: &mut self.decodability,
                    inner: handler,
                };
                report_packet_loss(pkt, |l| handler.loss(l));
                d.push(pkt, handler)
            }
        }
    }
}

/// Turns RTP packets into audio frames, delivering them to an [`AudioHandler`].
///
/// See [`VideoDepacketizer`] for an overview.
#[derive(Debug)]
pub struct AudioDepacketizer<Ctx>(AudioInner<Ctx>);

#[derive(Debug)]
enum AudioInner<Ctx> {
    Aac(Box<aac::Depacketizer<Ctx>>),
    SimpleAudio(Box<simple_audio::Depacketizer>),
    G723(Box<g723::Depacketizer>),
}

impl<Ctx: Clone> AudioDepacketizer<Ctx> {
    /// Creates a depacketizer for the given RTP payload format.
    ///
    /// Arguments are from the SDP media description's `rtpmap` and `fmtp`
    /// attributes. `encoding_name` is expected to be lowercase.
    ///
    /// Returns an error if the format is unsupported or the parameters are invalid.
    pub fn new(
        encoding_name: &str,
        clock_rate: u32,
        channels: Option<NonZeroU16>,
        format_specific_params: Option<&str>,
    ) -> Result<Self, Error> {
        Self::new_inner(encoding_name, clock_rate, channels, format_specific_params)
            .map_err(|e| wrap!(ErrorInt::InvalidArgument(e)))
    }

    fn new_inner(
        encoding_name: &str,
        clock_rate: u32,
        channels: Option<NonZeroU16>,
        format_specific_params: Option<&str>,
    ) -> Result<Self, String> {
        let simple = |bits_per_sample| {
            AudioInner::SimpleAudio(Box::new(simple_audio::Depacketizer::new(
                clock_rate,
                bits_per_sample,
                channels,
            )))
        };
        Ok(Self(match encoding_name {
            "mpeg4-generic" => AudioInner::Aac(Box::new(aac::Depacketizer::new(
                clock_rate,
                channels,
                format_specific_params,
            )?)),
            "g726-16" => simple(2),
            "g726-24" => simple(3),
            "dvi4" | "g726-32" => simple(4),
            "g726-40" => simple(5),
            "pcma" | "pcmu" | "u8" | "g722" => simple(8),
            "l16" => simple(16),
            // Dahua cameras when configured with G723 send packets with a
            // non-standard encoding-name "G723.1" and length 40, which doesn't
            // make sense. Don't try to depacketize these.
            "g723" => AudioInner::G723(Box::new(g723::Depacketizer::new(clock_rate)?)),
            _ => {
                return Err(format!(
                    "no audio depacketizer for encoding_name {encoding_name}"
                ));
            }
        }))
    }

    /// Returns the parameters.
    pub fn parameters(&self) -> &AudioParameters {
        match &self.0 {
            AudioInner::Aac(d) => d.parameters(),
            AudioInner::SimpleAudio(d) => d.parameters(),
            AudioInner::G723(d) => d.parameters(),
        }
    }

    /// Supplies a new packet, delivering any resulting events to `handler`.
    ///
    /// This never fails: lost packets and corrupt data are reported via
    /// [`AudioHandler::loss`].
    pub fn push(&mut self, pkt: &ReceivedPacketRef<'_, Ctx>, handler: &mut impl AudioHandler<Ctx>) {
        report_packet_loss(pkt, |l| handler.loss(l));
        match &mut self.0 {
            AudioInner::Aac(d) => d.push(pkt, handler),
            AudioInner::SimpleAudio(d) => d.push(pkt, handler),
            AudioInner::G723(d) => d.push(pkt, handler),
        }
    }
}

/// Turns RTP packets into messages (for `application` media types),
/// delivering them to a [`MessageHandler`].
///
/// See [`VideoDepacketizer`] for an overview.
#[derive(Debug)]
pub struct MessageDepacketizer<Ctx>(Box<onvif::Depacketizer<Ctx>>);

impl<Ctx: Clone> MessageDepacketizer<Ctx> {
    /// Creates a depacketizer for the given RTP payload format.
    ///
    /// `encoding_name` is from the SDP media description's `rtpmap` attribute,
    /// and is expected to be lowercase.
    ///
    /// Returns an error if the format is unsupported.
    pub fn new(encoding_name: &str) -> Result<Self, Error> {
        use onvif::CompressionType;
        let compression_type = match encoding_name {
            "vnd.onvif.metadata" => CompressionType::Uncompressed,
            "vnd.onvif.metadata.gzip" => CompressionType::GzipCompressed,
            "vnd.onvif.metadata.exi.onvif" => CompressionType::ExiDefault,
            "vnd.onvif.metadata.exi.ext" => CompressionType::ExiInBand,
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "no message depacketizer for encoding_name {encoding_name}"
            ))),
        };
        Ok(Self(Box::new(onvif::Depacketizer::new(compression_type))))
    }

    /// Returns the parameters.
    pub fn parameters(&self) -> &MessageParameters {
        self.0.parameters()
    }

    /// Supplies a new packet, delivering any resulting events to `handler`.
    ///
    /// This never fails: lost packets and corrupt data are reported via
    /// [`MessageHandler::loss`].
    pub fn push(
        &mut self,
        pkt: &ReceivedPacketRef<'_, Ctx>,
        handler: &mut impl MessageHandler<Ctx>,
    ) {
        report_packet_loss(pkt, |l| handler.loss(l));
        self.0.push(pkt, handler);
    }
}

/// An RTP payload format, as described by an SDP media description: its media
/// type, and its `rtpmap` and `fmtp` attributes.
///
/// A [`Depacketizer`] is created from one (see
/// [`crate::client::Stream::payload_format`]), and a [`VideoPacketizer`]
/// describes its output with one (see [`VideoPacketizer::payload_format`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PayloadFormat {
    media: Cow<'static, str>,
    encoding_name: Cow<'static, str>,
    clock_rate: u32,
    channels: Option<NonZeroU16>,
    fmtp: Option<String>,
}

impl PayloadFormat {
    /// Creates a payload format with the given media type (e.g. `video`),
    /// encoding name (e.g. `H264`), and clock rate in Hz.
    pub fn new(
        media: impl Into<Cow<'static, str>>,
        encoding_name: impl Into<Cow<'static, str>>,
        clock_rate: u32,
    ) -> Self {
        Self {
            media: media.into(),
            encoding_name: encoding_name.into(),
            clock_rate,
            channels: None,
            fmtp: None,
        }
    }

    /// Sets the number of channels from the `rtpmap` attribute, for audio.
    #[inline]
    pub fn with_channels(self, channels: NonZeroU16) -> Self {
        Self {
            channels: Some(channels),
            ..self
        }
    }

    /// Sets the format-specific parameters from the `fmtp` attribute.
    #[inline]
    pub fn with_fmtp(self, fmtp: impl Into<String>) -> Self {
        Self {
            fmtp: Some(fmtp.into()),
            ..self
        }
    }

    /// Returns the SDP media type, e.g. `video`.
    #[inline]
    pub fn media(&self) -> &str {
        &self.media
    }

    /// Returns the encoding name from the `rtpmap` attribute, e.g. `H264`.
    #[inline]
    pub fn encoding_name(&self) -> &str {
        &self.encoding_name
    }

    /// Returns the clock rate from the `rtpmap` attribute, in Hz.
    #[inline]
    pub fn clock_rate(&self) -> u32 {
        self.clock_rate
    }

    /// Returns the number of channels from the `rtpmap` attribute, if
    /// specified.
    #[inline]
    pub fn channels(&self) -> Option<NonZeroU16> {
        self.channels
    }

    /// Returns the format-specific parameters from the `fmtp` attribute, if
    /// any.
    #[inline]
    pub fn fmtp(&self) -> Option<&str> {
        self.fmtp.as_deref()
    }
}

/// A video, audio, or message depacketizer, chosen from an SDP media
/// description.
///
/// This is for callers which don't know the media type statically, such as
/// [`crate::client`] sessions; see
/// [`crate::client::Stream::new_depacketizer`]. It delivers events to a
/// handler which implements all of [`VideoHandler`], [`AudioHandler`], and
/// [`MessageHandler`]. The latter two have default implementations of all
/// methods, so a handler which only expects video can implement them with
/// empty `impl` blocks.
#[derive(Debug)]
#[non_exhaustive]
pub enum Depacketizer<Ctx> {
    Video(VideoDepacketizer<Ctx>),
    Audio(AudioDepacketizer<Ctx>),
    Message(MessageDepacketizer<Ctx>),
}

impl<Ctx: Clone> Depacketizer<Ctx> {
    /// Creates a depacketizer for the given RTP payload format.
    ///
    /// The media type and encoding name are matched case-insensitively.
    ///
    /// Returns an error if the format is unsupported or the parameters are invalid.
    pub fn new(format: &PayloadFormat) -> Result<Self, Error> {
        let media = format.media.to_ascii_lowercase();
        let encoding_name = format.encoding_name.to_ascii_lowercase();
        let clock_rate = format.clock_rate;
        let fmtp = format.fmtp.as_deref();

        // RTP Payload Format Media Types
        // https://www.iana.org/assignments/rtp-parameters/rtp-parameters.xhtml#rtp-parameters-2
        match (&*media, &*encoding_name) {
            // JPEG's registered media type is `video` (RFC 2435), but some
            // servers say `image`.
            ("video", _) | ("image", "jpeg") => {
                VideoDepacketizer::new(&encoding_name, clock_rate, fmtp).map(Self::Video)
            }
            ("audio", _) => {
                AudioDepacketizer::new(&encoding_name, clock_rate, format.channels, fmtp)
                    .map(Self::Audio)
            }
            ("application", _) => MessageDepacketizer::new(&encoding_name).map(Self::Message),
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "no depacketizer for media {media}"
            ))),
        }
    }

    #[cfg(test)]
    pub(crate) fn check_invariants(&self) {
        if let Self::Video(d) = self {
            d.check_invariants();
        }
    }

    /// Returns the current codec parameters, if known.
    ///
    /// Video parameters may change as frames arrive; see [`ParametersRef`].
    pub fn parameters(&self) -> Option<ParametersRef<'_>> {
        match self {
            Self::Video(d) => d.parameters().map(ParametersRef::Video),
            Self::Audio(d) => Some(ParametersRef::Audio(d.parameters())),
            Self::Message(d) => Some(ParametersRef::Message(d.parameters())),
        }
    }

    /// Supplies a new packet, delivering any resulting events to `handler`.
    ///
    /// This is test-only: a public equivalent would need a handler bound
    /// naming every media type, which a new variant would break. Callers
    /// match on the variant and use its `push` instead.
    #[cfg(test)]
    pub(crate) fn push(
        &mut self,
        pkt: &ReceivedPacketRef<'_, Ctx>,
        handler: &mut (impl VideoHandler<Ctx> + AudioHandler<Ctx> + MessageHandler<Ctx>),
    ) {
        match self {
            Self::Video(d) => d.push(pkt, handler),
            Self::Audio(d) => d.push(pkt, handler),
            Self::Message(d) => d.push(pkt, handler),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::buf::MarkBuf;
    #[cfg(feature = "h264")]
    use crate::rtp::ReceivedPacketMeta;
    use events::testutil::{Event, Recorder, hex};

    /// Pushes a packet via the infallible `push`.
    fn push(
        d: &mut Depacketizer<crate::PacketContext>,
        buf: &mut MarkBuf,
        (sequence_number, timestamp, mark, loss): (u16, i64, bool, u16),
        payload: &[u8],
        h: &mut Recorder,
    ) {
        let meta = crate::rtp::ReceivedPacketMeta {
            ctx: crate::PacketContext::dummy(),
            timestamp: crate::Timestamp::new(timestamp, NonZeroU32::new(90_000).unwrap(), 0)
                .unwrap(),
            ssrc: 0,
            sequence_number,
            mark,
            continuity: crate::rtp::Continuity::from_loss(loss),
        };
        let pos = buf.end();
        buf.extend(payload);
        buf.advance_unparsed(buf.end());
        d.push(
            &ReceivedPacketRef::new(meta, buf, pos, payload.len() as u16),
            h,
        );
        d.check_invariants();
    }

    #[cfg(feature = "h264")]
    fn h264() -> Depacketizer<crate::PacketContext> {
        Depacketizer::new(&PayloadFormat::new("video", "h264", 90_000).with_fmtp(
            "packetization-mode=1;profile-level-id=4d002a;\
             sprop-parameter-sets=Z00AKpWoHgCJ+WEAAAMAAQAAAwAyhA==,aO48gA==",
        ))
        .unwrap()
    }

    fn assert_corrupt(events: &[Event]) {
        assert!(
            matches!(events, [Event::Loss(LossReason::Corrupt { .. })]),
            "{events:#?}"
        );
    }

    #[cfg(feature = "h264")]
    fn idr_frame() -> Vec<Event> {
        vec![
            Event::FrameStart {
                is_random_access_point: true,
                is_disposable: false,
                has_new_parameters: false,
            },
            Event::Data(Position::Complete, hex(b"\x65slice")),
            Event::FrameEnd {
                is_random_access_point: true,
                is_disposable: false,
                has_new_parameters: false,
                data: Some(hex(b"\x00\x00\x00\x06\x65slice")),
            },
        ]
    }

    #[test]
    #[should_panic(expected = "holding data from one MarkBuf")]
    #[cfg(feature = "h264")]
    fn different_buf() {
        let mut d = h264();
        let mut buf1 = MarkBuf::new(65536);
        let mut buf2 = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::Yes);
        push(
            &mut d,
            &mut buf1,
            (0, 0, false, 0),
            b"\x7c\x85start",
            &mut h,
        );
        push(&mut d, &mut buf2, (1, 0, true, 0), b"\x7c\x45end", &mut h);
    }

    #[test]
    #[cfg(feature = "h264")]
    fn is_decodable() {
        /// Records `(is_decodable at start, is_decodable at end)` per frame.
        #[derive(Default)]
        struct H(Vec<(bool, bool)>, Option<bool>);
        impl AudioHandler<crate::PacketContext> for H {}
        impl MessageHandler<crate::PacketContext> for H {}
        impl VideoHandler<crate::PacketContext> for H {
            fn frame_start(
                &mut self,
                fs: &mut VideoFrameStart<'_, crate::PacketContext>,
            ) -> Accumulate {
                self.1 = Some(fs.is_decodable());
                Accumulate::No
            }
            fn frame_end(&mut self, fe: &mut VideoFrameEnd<'_, crate::PacketContext>) {
                self.0.push((self.1.take().unwrap(), fe.is_decodable()));
            }
        }

        crate::testutil::init_logging();
        let mut d = h264();
        let mut buf = MarkBuf::new(65536);
        let mut h = H::default();
        let mut push = |seq: u16, ts: i64, loss: u16, payload: &[u8], h: &mut H| {
            let meta = crate::rtp::ReceivedPacketMeta {
                ctx: crate::PacketContext::dummy(),
                timestamp: crate::Timestamp::new(ts, NonZeroU32::new(90_000).unwrap(), 0).unwrap(),
                ssrc: 0,
                sequence_number: seq,
                mark: true,
                continuity: crate::rtp::Continuity::from_loss(loss),
            };
            let pos = buf.end();
            buf.extend(payload);
            buf.advance_unparsed(buf.end());
            d.push(
                &ReceivedPacketRef::new(meta, &buf, pos, payload.len() as u16),
                h,
            );
        };
        push(0, 0, 0, b"\x41p", &mut h); // before the first IDR.
        push(1, 1, 0, b"\x65idr", &mut h);
        push(2, 2, 0, b"\x41p", &mut h);
        push(4, 3, 1, b"\x41p", &mut h); // after loss.
        push(5, 4, 0, b"\x41p", &mut h);
        push(6, 5, 0, b"\x65idr", &mut h);
        push(7, 6, 0, b"\xe5corrupt", &mut h);
        push(8, 7, 0, b"\x41p", &mut h); // after corruption.
        push(9, 8, 0, b"\x65idr", &mut h);
        assert_eq!(
            h.0,
            [
                (false, false),
                (true, true),
                (true, true),
                (false, false),
                (false, false),
                (true, true),
                (false, false),
                (true, true),
            ]
        );
    }

    /// A random access point preceded by loss is decodable only if it starts a picture.
    #[test]
    #[cfg(feature = "h264")]
    fn is_decodable_missing_prefix() {
        /// Records `(is_decodable at start, is_decodable at end)` per frame.
        #[derive(Default)]
        struct H(Vec<(bool, bool)>, Option<bool>);
        impl AudioHandler<crate::PacketContext> for H {}
        impl MessageHandler<crate::PacketContext> for H {}
        impl VideoHandler<crate::PacketContext> for H {
            fn frame_start(
                &mut self,
                fs: &mut VideoFrameStart<'_, crate::PacketContext>,
            ) -> Accumulate {
                self.1 = Some(fs.is_decodable());
                Accumulate::No
            }
            fn frame_end(&mut self, fe: &mut VideoFrameEnd<'_, crate::PacketContext>) {
                self.0.push((self.1.take().unwrap(), fe.is_decodable()));
            }
        }

        crate::testutil::init_logging();
        let mut d = h264();
        let mut buf = MarkBuf::new(65536);
        let mut h = H::default();
        let mut push = |seq: u16, ts: i64, loss: u16, payload: &[u8], h: &mut H| {
            let meta = crate::rtp::ReceivedPacketMeta {
                ctx: crate::PacketContext::dummy(),
                timestamp: crate::Timestamp::new(ts, NonZeroU32::new(90_000).unwrap(), 0).unwrap(),
                ssrc: 0,
                sequence_number: seq,
                mark: true,
                continuity: crate::rtp::Continuity::from_loss(loss),
            };
            let pos = buf.end();
            buf.extend(payload);
            buf.advance_unparsed(buf.end());
            d.push(
                &ReceivedPacketRef::new(meta, &buf, pos, payload.len() as u16),
                h,
            );
        };

        // Slice bodies starting with bit 1 have `first_mb_in_slice == 0`.
        push(0, 0, 0, b"\x65\x88idr", &mut h);
        push(1, 1, 0, b"\x41\x88p", &mut h);
        push(3, 2, 1, b"\x65\x40idr, missing first slice", &mut h);
        push(4, 3, 0, b"\x41\x88p", &mut h);
        push(6, 4, 1, b"\x65\x88idr, complete", &mut h);
        push(7, 5, 0, b"\x41\x88p", &mut h);
        assert_eq!(
            h.0,
            [
                (true, true),
                (true, true),
                (false, false),
                (false, false),
                (true, true),
                (true, true),
            ]
        );
    }

    /// H.265 RASL pictures are decodable only if their CRA was reached without loss.
    #[test]
    #[cfg(feature = "h265")]
    fn is_decodable_rasl() {
        /// Records `(is_decodable at start, is_decodable at end)` per frame.
        #[derive(Default)]
        struct H(Vec<(bool, bool)>, Option<bool>);
        impl AudioHandler<crate::PacketContext> for H {}
        impl MessageHandler<crate::PacketContext> for H {}
        impl VideoHandler<crate::PacketContext> for H {
            fn frame_start(
                &mut self,
                fs: &mut VideoFrameStart<'_, crate::PacketContext>,
            ) -> Accumulate {
                self.1 = Some(fs.is_decodable());
                Accumulate::No
            }
            fn frame_end(&mut self, fe: &mut VideoFrameEnd<'_, crate::PacketContext>) {
                self.0.push((self.1.take().unwrap(), fe.is_decodable()));
            }
        }

        crate::testutil::init_logging();
        let mut d = Depacketizer::new(&PayloadFormat::new("video", "h265", 90_000)).unwrap();
        let mut buf = MarkBuf::new(65536);
        let mut h = H::default();
        let mut push = |seq: u16, ts: i64, loss: u16, payload: &[u8], h: &mut H| {
            let meta = crate::rtp::ReceivedPacketMeta {
                ctx: crate::PacketContext::dummy(),
                timestamp: crate::Timestamp::new(ts, NonZeroU32::new(90_000).unwrap(), 0).unwrap(),
                ssrc: 0,
                sequence_number: seq,
                mark: true,
                continuity: crate::rtp::Continuity::from_loss(loss),
            };
            let pos = buf.end();
            buf.extend(payload);
            buf.advance_unparsed(buf.end());
            d.push(
                &ReceivedPacketRef::new(meta, &buf, pos, payload.len() as u16),
                h,
            );
        };

        // NAL headers: CRA_NUT (21), RASL_N (8), RADL_N (6), TRAIL_R (1).
        // Slice bodies starting with bit 1 have `first_slice_segment_in_pic_flag`.
        const CRA: &[u8] = b"\x2a\x01\x80cra";
        const RASL: &[u8] = b"\x10\x01\x80rasl";
        const RADL: &[u8] = b"\x0c\x01\x80radl";
        const TRAIL: &[u8] = b"\x02\x01\x80trail";
        push(0, 0, 0, CRA, &mut h); // decoding starts here.
        push(1, 1, 0, RASL, &mut h);
        push(2, 2, 0, RADL, &mut h);
        push(3, 3, 0, TRAIL, &mut h);
        push(4, 4, 0, CRA, &mut h); // reached cleanly.
        push(5, 5, 0, RASL, &mut h);
        push(6, 6, 0, TRAIL, &mut h);
        push(8, 7, 1, TRAIL, &mut h); // after loss.
        push(9, 8, 0, CRA, &mut h); // reached after loss.
        push(10, 9, 0, RASL, &mut h);
        push(11, 10, 0, RADL, &mut h);
        push(12, 11, 0, TRAIL, &mut h);
        assert_eq!(
            h.0,
            [
                (true, true),
                (false, false),
                (true, true),
                (true, true),
                (true, true),
                (true, true),
                (true, true),
                (false, false),
                (true, true),
                (false, false),
                (true, true),
                (true, true),
            ]
        );
    }

    /// JPEG frames with lost or misplaced fragments are discarded.
    #[test]
    fn jpeg_discards_incomplete_frames() {
        crate::testutil::init_logging();
        let mut d = Depacketizer::new(&PayloadFormat::new("video", "jpeg", 90_000)).unwrap();
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::No);

        /// Returns a RTP/JPEG packet: type 1, Q 50, 8x8, then the given scan data.
        fn pkt(frag_offset: u32, data: &[u8]) -> Vec<u8> {
            let mut p = vec![0];
            p.extend_from_slice(&frag_offset.to_be_bytes()[1..]);
            p.extend_from_slice(&[1, 50, 1, 1]);
            p.extend_from_slice(data);
            p
        }
        let kinds = |events: Vec<Event>| -> Vec<&'static str> {
            events
                .into_iter()
                .map(|e| match e {
                    Event::FrameStart { .. } => "start",
                    Event::Data(..) => "data",
                    Event::FrameEnd { .. } => "end",
                    Event::Loss(LossReason::PacketLoss { .. }) => "packet loss",
                    Event::Loss(LossReason::Corrupt { .. }) => "corrupt",
                    e => panic!("unexpected {e:?}"),
                })
                .collect()
        };

        // Complete.
        push(&mut d, &mut buf, (0, 0, false, 0), &pkt(0, b"abcd"), &mut h);
        push(&mut d, &mut buf, (1, 0, true, 0), &pkt(4, b"efgh"), &mut h);
        assert_eq!(kinds(h.take()), ["start", "data", "end"]);

        // Interior loss.
        push(&mut d, &mut buf, (2, 1, false, 0), &pkt(0, b"abcd"), &mut h);
        push(&mut d, &mut buf, (4, 1, true, 1), &pkt(8, b"ijkl"), &mut h);
        assert_eq!(kinds(h.take()), ["packet loss"]);

        // Misplaced fragment without loss.
        push(&mut d, &mut buf, (5, 2, false, 0), &pkt(0, b"abcd"), &mut h);
        push(&mut d, &mut buf, (6, 2, true, 0), &pkt(5, b"efgh"), &mut h);
        assert_eq!(kinds(h.take()), ["corrupt"]);

        // Recovers.
        push(&mut d, &mut buf, (7, 3, true, 0), &pkt(0, b"abcd"), &mut h);
        assert_eq!(kinds(h.take()), ["start", "data", "end"]);
    }

    #[test]
    #[cfg(feature = "h264")]
    fn forbidden_bit_corrupt() {
        crate::testutil::init_logging();
        let mut d = h264();
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::Yes);
        push(&mut d, &mut buf, (0, 0, true, 0), b"\xe5slice", &mut h);
        assert_corrupt(&h.take());
        push(&mut d, &mut buf, (1, 1, true, 0), b"\x65slice", &mut h);
        assert_eq!(h.take(), idr_frame());
    }

    #[test]
    #[cfg(feature = "h264")]
    fn empty_payload_corrupt() {
        crate::testutil::init_logging();
        let mut d = h264();
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::Yes);
        push(&mut d, &mut buf, (0, 0, true, 0), b"", &mut h);
        assert_corrupt(&h.take());
        push(&mut d, &mut buf, (1, 1, true, 0), b"\x65slice", &mut h);
        assert_eq!(h.take(), idr_frame());
    }

    /// Corruption after `frame_start` abandons the frame; the next frame recovers.
    #[test]
    #[cfg(feature = "h264")]
    fn recovery_after_corrupt() {
        crate::testutil::init_logging();
        let mut d = h264();
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::Yes);
        push(&mut d, &mut buf, (0, 0, false, 0), b"\x7c\x85start", &mut h);
        assert_eq!(h.take().len(), 2); // FrameStart, Data(Start).

        // A STAP-A isn't allowed while a FU-A is in progress.
        push(
            &mut d,
            &mut buf,
            (1, 0, false, 0),
            b"\x18\x00\x02\x06x",
            &mut h,
        );
        assert_corrupt(&h.take());

        // The rest of the access unit is ignored until the next one starts.
        push(&mut d, &mut buf, (2, 1, true, 0), b"\x65slice", &mut h);
        assert_eq!(h.take(), idr_frame());
    }

    #[test]
    #[cfg(feature = "h264")]
    fn loss_within_frame() {
        crate::testutil::init_logging();
        let mut d = h264();
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::Yes);
        push(&mut d, &mut buf, (0, 0, false, 0), b"\x7c\x85start", &mut h);
        h.take();
        push(&mut d, &mut buf, (3, 0, true, 2), b"\x7c\x45end", &mut h);
        assert_eq!(
            h.take(),
            vec![Event::Loss(LossReason::PacketLoss { packets: 2 })]
        );
        push(&mut d, &mut buf, (4, 1, true, 0), b"\x65slice", &mut h);
        assert_eq!(h.take(), idr_frame());
    }

    #[cfg(any(feature = "h264", feature = "h265"))]
    fn with_max_frame_bytes(
        mut d: Depacketizer<crate::PacketContext>,
        max_frame_bytes: usize,
    ) -> Depacketizer<crate::PacketContext> {
        let Depacketizer::Video(v) = &mut d else {
            panic!("expected a video depacketizer");
        };
        v.set_max_frame_bytes(max_frame_bytes);
        d
    }

    /// A frame which grows past the limit is abandoned, and the rest of it is
    /// skipped.
    #[test]
    #[cfg(feature = "h264")]
    fn h264_too_large() {
        crate::testutil::init_logging();
        let mut d = with_max_frame_bytes(h264(), 16);
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::Yes);
        push(&mut d, &mut buf, (0, 0, false, 0), b"\x7c\x85start", &mut h);
        h.take();
        push(
            &mut d,
            &mut buf,
            (1, 0, false, 0),
            b"\x7c\x05middle!!",
            &mut h,
        );
        assert_eq!(
            h.take(),
            vec![Event::Loss(LossReason::TooLarge { limit: 16 })]
        );
        push(&mut d, &mut buf, (2, 0, true, 0), b"\x7c\x45end", &mut h);
        assert_eq!(h.take(), vec![]);
        push(&mut d, &mut buf, (3, 1, true, 0), b"\x65slice", &mut h);
        assert_eq!(h.take(), idr_frame());
    }

    /// Under `Accumulate::No`, the limit covers data before `frame_start`...
    #[test]
    #[cfg(feature = "h264")]
    fn h264_too_large_before_frame_start() {
        crate::testutil::init_logging();
        let mut d = with_max_frame_bytes(h264(), 16);
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::No);
        push(&mut d, &mut buf, (0, 0, false, 0), b"\x06sei-data", &mut h);
        assert_eq!(h.take(), vec![]);
        push(&mut d, &mut buf, (1, 0, false, 0), b"\x06sei-data", &mut h);
        assert_eq!(
            h.take(),
            vec![Event::Loss(LossReason::TooLarge { limit: 16 })]
        );
    }

    /// ...but not data after it, which isn't retained.
    #[test]
    #[cfg(feature = "h264")]
    fn h264_streaming_unlimited_after_frame_start() {
        crate::testutil::init_logging();
        let mut d = with_max_frame_bytes(h264(), 16);
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::No);
        push(&mut d, &mut buf, (0, 0, false, 0), b"\x7c\x85start", &mut h);
        for seq in 1..10 {
            push(
                &mut d,
                &mut buf,
                (seq, 0, false, 0),
                b"\x7c\x05middle!!",
                &mut h,
            );
        }
        push(&mut d, &mut buf, (10, 0, true, 0), b"\x7c\x45end", &mut h);
        let events = h.take();
        assert!(
            !events.iter().any(|e| matches!(e, Event::Loss(_))),
            "{events:#?}"
        );
        assert!(
            matches!(events.last(), Some(Event::FrameEnd { data: None, .. })),
            "{events:#?}"
        );
    }

    #[test]
    #[cfg(feature = "h265")]
    fn h265_too_large() {
        crate::testutil::init_logging();
        let mut d = with_max_frame_bytes(
            Depacketizer::new(&PayloadFormat::new("video", "h265", 90_000)).unwrap(),
            20,
        );
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::Yes);
        // Prefix SEI NALs (type 39).
        push(
            &mut d,
            &mut buf,
            (0, 0, false, 0),
            b"\x4e\x01sei-data",
            &mut h,
        );
        assert_eq!(h.take(), vec![]);
        push(
            &mut d,
            &mut buf,
            (1, 0, false, 0),
            b"\x4e\x01sei-data-2",
            &mut h,
        );
        assert_eq!(
            h.take(),
            vec![Event::Loss(LossReason::TooLarge { limit: 20 })]
        );
    }

    /// The case `MarkBuf::set_max_retained` is for: a stream with a small
    /// in-progress frame stops receiving packets while another stream shares
    /// its buffer. The buffer discards the frame's data rather than growing
    /// without bound, and the depacketizer abandons the frame rather than
    /// reading discarded data.
    #[test]
    #[cfg(feature = "h264")]
    fn h264_evicted() {
        crate::testutil::init_logging();
        let mut d = h264();
        let mut buf = MarkBuf::new(64);
        buf.set_max_retained(256);
        let mut h = Recorder::new(Accumulate::Yes);
        push(&mut d, &mut buf, (0, 0, false, 0), b"\x7c\x85start", &mut h);
        h.take();

        // Another stream's packets.
        for _ in 0..16 {
            buf.extend(&[0u8; 32]);
            buf.advance_unparsed(buf.end());
        }
        assert!(buf.capacity() <= 1024, "{}", buf.capacity());

        push(&mut d, &mut buf, (1, 0, true, 0), b"\x7c\x45end", &mut h);
        assert_eq!(h.take(), vec![Event::Loss(LossReason::Evicted)]);
        push(&mut d, &mut buf, (2, 1, true, 0), b"\x65slice", &mut h);
        assert_eq!(h.take(), idr_frame());
    }

    #[test]
    #[cfg(feature = "h264")]
    fn loss_across_frames() {
        crate::testutil::init_logging();
        let mut d = h264();
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::Yes);
        push(&mut d, &mut buf, (0, 0, true, 0), b"\x65slice", &mut h);
        assert_eq!(h.take(), idr_frame());
        push(&mut d, &mut buf, (2, 1, true, 1), b"\x41slice", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::Loss(LossReason::PacketLoss { packets: 1 }),
                Event::FrameStart {
                    is_random_access_point: false,
                    is_disposable: false,
                    has_new_parameters: false,
                },
                Event::Data(Position::Complete, hex(b"\x41slice")),
                Event::FrameEnd {
                    is_random_access_point: false,
                    is_disposable: false,
                    has_new_parameters: false,
                    data: Some(hex(b"\x00\x00\x00\x06\x41slice")),
                },
            ]
        );
    }

    #[test]
    fn audio_events() {
        crate::testutil::init_logging();
        let mut d = Depacketizer::new(&PayloadFormat::new("audio", "pcmu", 8_000)).unwrap();
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::Yes);
        push(&mut d, &mut buf, (0, 0, true, 0), b"abcd", &mut h);
        push(&mut d, &mut buf, (3, 4, true, 2), b"efgh", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::AudioFrame(hex(b"abcd")),
                Event::Loss(LossReason::PacketLoss { packets: 2 }),
                Event::AudioFrame(hex(b"efgh")),
            ]
        );
    }

    #[test]
    fn aac_corrupt() {
        crate::testutil::init_logging();
        let mut d = Depacketizer::new(
            &PayloadFormat::new("audio", "mpeg4-generic", 12_000)
                .with_channels(NonZeroU16::new(2).unwrap())
                .with_fmtp(
                    "profile-level-id=1;mode=AAC-hbr;sizelength=13;indexlength=3;\
                     indexdeltalength=3;config=1490",
                ),
        )
        .unwrap();
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::Yes);
        push(&mut d, &mut buf, (0, 0, true, 0), b"\x00", &mut h);
        assert_corrupt(&h.take());

        // One AU header (size 4), then the AU.
        push(
            &mut d,
            &mut buf,
            (1, 1024, true, 0),
            b"\x00\x10\x00\x20abcd",
            &mut h,
        );
        assert_eq!(h.take(), vec![Event::AudioFrame(hex(b"abcd"))]);
    }

    #[test]
    fn message_events() {
        crate::testutil::init_logging();
        let mut d = Depacketizer::new(&PayloadFormat::new(
            "application",
            "vnd.onvif.metadata",
            90_000,
        ))
        .unwrap();
        let mut buf = MarkBuf::new(65536);
        let mut h = Recorder::new(Accumulate::Yes);
        push(&mut d, &mut buf, (0, 0, false, 0), b"<a>", &mut h);
        push(&mut d, &mut buf, (1, 0, true, 0), b"</a>", &mut h);
        assert_eq!(h.take(), vec![Event::MessageFrame(hex(b"<a></a>"))]);
    }

    /// Parses the RTP packets of one channel of an RTSP interleaved dump into
    /// `buf`, calling `f` with each.
    #[cfg(feature = "h264")]
    fn replay(
        dump: &[u8],
        channel: u8,
        clock_rate: u32,
        mut f: impl FnMut(&MarkBuf, ReceivedPacketMeta<crate::PacketContext>, u64, u16),
    ) {
        let mut buf = MarkBuf::new(4096);
        let mut prev: Option<(u16, u32, i64)> = None;
        let mut remaining = dump;
        while !remaining.is_empty() {
            assert_eq!(remaining[0], b'$');
            let len = u16::from_be_bytes([remaining[2], remaining[3]]);
            let (frame, rest) = remaining.split_at(4 + usize::from(len));
            remaining = rest;
            if frame[1] != channel {
                continue;
            }
            let pos = buf.end();
            buf.extend(&frame[4..]);
            buf.advance_unparsed(buf.end());
            let (header, payload) =
                crate::rtp::PacketHeader::validate(buf.split(pos, len.into())).unwrap();
            let raw = header.timestamp();
            let extended = match prev {
                None => i64::from(raw),
                Some((_, prev_raw, prev_extended)) => {
                    prev_extended + i64::from(raw.wrapping_sub(prev_raw) as i32)
                }
            };
            let loss = prev.map_or(0, |(s, _, _)| {
                header.sequence_number().wrapping_sub(s).wrapping_sub(1)
            });
            prev = Some((header.sequence_number(), raw, extended));
            let meta = ReceivedPacketMeta {
                ctx: crate::PacketContext::dummy(),
                timestamp: crate::Timestamp::new(extended, NonZeroU32::new(clock_rate).unwrap(), 0)
                    .unwrap(),
                sequence_number: header.sequence_number(),
                ssrc: header.ssrc(),
                mark: header.mark(),
                continuity: crate::rtp::Continuity::from_loss(loss),
            };
            f(
                &buf,
                meta,
                pos + u64::from(payload.start),
                payload.end - payload.start,
            );
        }
    }

    #[cfg(feature = "h264")]
    const BUNNY: &[u8] = include_bytes!("../../benches/bunny.rtsp");
    #[cfg(feature = "h264")]
    const BUNNY_H264_FMTP: &str = "packetization-mode=1;profile-level-id=42C01E;\
                                   sprop-parameter-sets=Z0LAHtkDxWhAAAADAEAAAAwDxYuS,aMuMsg==";
    #[cfg(feature = "h264")]
    const BUNNY_AAC_FMTP: &str = "profile-level-id=1;mode=AAC-hbr;sizelength=13;indexlength=3;\
                                  indexdeltalength=3;config=1490";

    /// The test harness's `Collector` and the `Recorder` produce identical
    /// frames; streamed data matches accumulated data.
    #[test]
    #[cfg(feature = "h264")]
    fn bunny_collector_vs_recorder() {
        crate::testutil::init_logging();
        for (channel, media, encoding, clock_rate, fmtp) in [
            (2, "video", "h264", 90_000, BUNNY_H264_FMTP),
            (0, "audio", "mpeg4-generic", 12_000, BUNNY_AAC_FMTP),
        ] {
            let new = || {
                Depacketizer::new(
                    &PayloadFormat::new(media, encoding, clock_rate)
                        .with_channels(NonZeroU16::new(2).unwrap())
                        .with_fmtp(fmtp),
                )
                .unwrap()
            };

            // The test harness.
            let mut d = new();
            let mut collected = Vec::new();
            let mut pending = testutil::Pending::default();
            replay(BUNNY, channel, clock_rate, |buf, meta, pos, len| {
                d.push(
                    &ReceivedPacketRef::new(meta, buf, pos, len),
                    &mut testutil::Collector::new(&mut pending, FrameFormat::default()),
                );
                while let Some(item) = pending.pull() {
                    collected.push(match item.unwrap() {
                        testutil::Item::Video(f) => f.into_data(),
                        testutil::Item::Audio(f) => f.data().to_vec(),
                        _ => unreachable!(),
                    });
                }
            });
            assert!(collected.len() > 100);

            // Handler, accumulating in the default format and in `MP4` (which
            // checks streamed data against the accumulated frame).
            for format in [FrameFormat::default(), FrameFormat::MP4] {
                let mut d = new();
                let mut h = Recorder::new(Accumulate::Yes);
                h.format = format;
                replay(BUNNY, channel, clock_rate, |buf, meta, pos, len| {
                    d.push(&ReceivedPacketRef::new(meta, buf, pos, len), &mut h);
                });
                let frames: Vec<Vec<u8>> = h
                    .take()
                    .into_iter()
                    .filter_map(|e| match e {
                        Event::FrameEnd { data, .. } => Some(data.unwrap().0),
                        Event::AudioFrame(d) => Some(d.0),
                        Event::FrameStart { .. } | Event::Data(..) => None,
                        e => panic!("unexpected event {e:?}"),
                    })
                    .collect();
                assert_eq!(frames.len(), collected.len());
                if format == FrameFormat::default() {
                    for (i, (a, b)) in frames.iter().zip(&collected).enumerate() {
                        assert!(a == b, "frame {i} differs");
                    }
                }
            }

            // Handler, streaming.
            let mut d = new();
            let mut h = Recorder::new(Accumulate::No);
            replay(BUNNY, channel, clock_rate, |buf, meta, pos, len| {
                d.push(&ReceivedPacketRef::new(meta, buf, pos, len), &mut h);
            });
            let ends = h
                .take()
                .iter()
                .filter(|e| matches!(e, Event::FrameEnd { data: None, .. } | Event::AudioFrame(_)))
                .count();
            assert_eq!(ends, collected.len());
        }
    }

    /// As in 0.4.x, JPEG is accepted with media type `image` as well as `video`.
    #[test]
    fn jpeg_image_media_type() {
        let d =
            Depacketizer::<crate::PacketContext>::new(&PayloadFormat::new("image", "jpeg", 90_000));
        assert!(matches!(d, Ok(Depacketizer::Video(_))));
    }

    // See with: cargo test -- --nocapture codec::tests::print_sizes
    #[test]
    fn print_sizes() {
        crate::testutil::init_logging();
        for (name, size) in &[
            (
                "Depacketizer<crate::PacketContext>",
                std::mem::size_of::<Depacketizer<crate::PacketContext>>(),
            ),
            (
                "aac::Depacketizer",
                std::mem::size_of::<aac::Depacketizer<crate::PacketContext>>(),
            ),
            (
                "g723::Depacketizer",
                std::mem::size_of::<g723::Depacketizer>(),
            ),
            #[cfg(feature = "h264")]
            (
                "h264::Depacketizer",
                std::mem::size_of::<h264::Depacketizer<crate::PacketContext>>(),
            ),
            #[cfg(feature = "h265")]
            (
                "h265::Depacketizer",
                std::mem::size_of::<h265::Depacketizer<crate::PacketContext>>(),
            ),
            (
                "onvif::Depacketizer",
                std::mem::size_of::<onvif::Depacketizer<crate::PacketContext>>(),
            ),
            (
                "simple_audio::Depacketizer",
                std::mem::size_of::<simple_audio::Depacketizer>(),
            ),
            ("VideoParameters", std::mem::size_of::<VideoParameters>()),
            ("AudioParameters", std::mem::size_of::<AudioParameters>()),
            (
                "MessageParameters",
                std::mem::size_of::<MessageParameters>(),
            ),
        ] {
            log::info!("{name:-40} {size:4}");
        }
    }
}
