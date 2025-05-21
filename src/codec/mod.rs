// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Codec-specific logic (for audio, video, and application media types).
//!
//! Currently this primarily consists of RTP depacketization logic for each
//! codec, as needed for a client during `PLAY` and a server during `RECORD`.
//! Packetization (needed for the reverse) may be added in the future.

#![cfg_attr(docsrs, feature(doc_cfg))]

use std::num::NonZeroU8;
use std::num::{NonZeroU16, NonZeroU32};

use bytes::Bytes;

use crate::error::ErrorInt;
use crate::rtp::ReceivedPacket;
use crate::ConnectionContext;
use crate::Error;
use crate::StreamContext;

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

pub(crate) mod aac;
pub(crate) mod g723;
mod h26x;
pub(crate) mod jpeg;

#[doc(hidden)]
pub mod h264;

#[cfg(feature = "h265")]
#[doc(hidden)]
pub mod h265;

pub(crate) mod onvif;
pub(crate) mod simple_audio;

/// An item yielded from [`crate::client::Demuxed`]'s [`futures::stream::Stream`] impl.
#[derive(Debug)]
#[non_exhaustive]
pub enum CodecItem {
    VideoFrame(VideoFrame),
    AudioFrame(AudioFrame),
    MessageFrame(MessageFrame),
    Rtcp(crate::rtcp::ReceivedCompoundPacket),
}

/// Reference to parameters which describe a stream.
///
/// Parameters are often, but not always, available immediately
/// after `DESCRIBE` via [`crate::client::Stream::parameters`]. They should
/// always be available after the first frame.
///
/// Video streams' parameters may change mid-stream; if so, the frame which
/// changed them will have `VideoFrame::new_parameters` set, and subsequent
/// calls to [`crate::client::Stream::parameters`] will return the new value.
///
/// Currently audio and message streams' parameters never change mid-stream.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ParametersRef<'a> {
    Video(&'a VideoParameters),
    Audio(&'a AudioParameters),
    Message(&'a MessageParameters),
}

/// Parameters which describe a video stream.
///
/// A video stream's parameters are often, but not always, available immediately
/// after `DESCRIBE` via [`crate::client::Stream::parameters`]. They should
/// always be available after the first frame. They may change mid-stream.
///
/// Video streams' parameters may change mid-stream; if so, the frame which
/// changed them will have `VideoFrame::new_parameters` set, and subsequent
/// calls to [`crate::client::Stream::parameters`] will return the new value.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct VideoParameters {
    pixel_dimensions: (u16, u16),
    rfc6381_codec: String,
    pixel_aspect_ratio: Option<(u32, u32)>,
    frame_rate: Option<(u32, u32)>,
    extra_data: Bytes,

    /// The codec, for internal use in sample entry construction.
    ///
    /// This is more straightforward than reparsing the RFC 6381 codec string.
    codec: VideoParametersCodec,
}

impl VideoParameters {
    /// Returns a codec description in
    /// [RFC-6381](https://tools.ietf.org/html/rfc6381) form, eg `avc1.4D401E`.
    // TODO: use https://github.com/dholroyd/rfc6381-codec crate once published?
    pub fn rfc6381_codec(&self) -> &str {
        &self.rfc6381_codec
    }

    /// Returns a builder for an `.mp4` `VideoSampleEntry` box (as defined in
    /// ISO/IEC 14496-12).
    pub fn mp4_sample_entry(&self) -> VideoSampleEntryBuilder {
        VideoSampleEntryBuilder {
            params: self,
            aspect_ratio_override: None,
        }
    }

    /// Returns the overall dimensions of the video frame in pixels, as `(width, height)`.
    pub fn pixel_dimensions(&self) -> (u32, u32) {
        let (width, height) = self.pixel_dimensions;
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

    /// Raw codec-cpecific paramers (SPS, PPS, VPS)
    pub fn codec_params(&self) -> &VideoParametersCodec {
        &self.codec
    }

    /// The codec-specific "extra data" to feed to eg ffmpeg to decode the video frames.
    /// *   H.264: an AvcDecoderConfig.
    pub fn extra_data(&self) -> &[u8] {
        &self.extra_data
    }
}

impl std::fmt::Debug for VideoParameters {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VideoParameters")
            .field("rfc6381_codec", &self.rfc6381_codec)
            .field("pixel_dimensions", &self.pixel_dimensions)
            .field("pixel_aspect_ratio", &self.pixel_aspect_ratio)
            .field("frame_rate", &self.frame_rate)
            .field(
                "extra_data",
                &crate::hex::LimitedHex::new(&self.extra_data, 256),
            )
            .finish()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum VideoParametersCodec {
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

impl VideoParametersCodec {
    fn visual_sample_entry_box_type(&self) -> [u8; 4] {
        match self {
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
                buf.extend_from_slice(&self.params.pixel_dimensions.0.to_be_bytes()[..]);
                buf.extend_from_slice(&self.params.pixel_dimensions.1.to_be_bytes()[..]);
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
                    VideoParametersCodec::H264 { .. } => {
                        write_mp4_box!(&mut buf, *b"avcC", {
                            buf.extend_from_slice(&self.params.extra_data);
                        });
                    }
                    #[cfg(feature = "h265")]
                    VideoParametersCodec::H265 { .. } => {
                        write_mp4_box!(&mut buf, *b"hvcC", {
                            buf.extend_from_slice(&self.params.extra_data);
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

    /// The codec-specific "extra data" to feed to eg ffmpeg to decode the audio.
    /// *   AAC: a serialized `AudioSpecificConfig`.
    pub fn extra_data(&self) -> &[u8] {
        &self.extra_data
    }

    /// Returns a builder for an `.mp4` `AudioSampleEntry` box (as defined in ISO/IEC 14496-12).
    pub fn mp4_sample_entry(&self) -> AudioSampleEntryBuilder {
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

/// An audio frame, which consists of one or more samples.
pub struct AudioFrame {
    ctx: crate::PacketContext,
    stream_id: usize,
    timestamp: crate::Timestamp,
    frame_length: NonZeroU32,
    loss: u16,
    data: Bytes,
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
    /// [crate::rtp::ReceivedPacket::loss].
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

/// Parameters which describe a message stream, for `application` media types.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MessageParameters(onvif::CompressionType);

/// A single message, for `application` media types.
pub struct MessageFrame {
    ctx: crate::PacketContext,
    timestamp: crate::Timestamp,
    stream_id: usize,
    loss: u16,
    data: Bytes,
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
    /// [crate::rtp::ReceivedPacket::loss].
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
pub struct VideoFrame {
    // A pair of contexts: for the start and for the end.
    // Having both can be useful to measure the total time elapsed while receiving the frame.
    start_ctx: crate::PacketContext,
    end_ctx: crate::PacketContext,

    has_new_parameters: bool,
    loss: u16,
    timestamp: crate::Timestamp,
    stream_id: usize,
    is_random_access_point: bool,
    is_disposable: bool,
    data: Vec<u8>,
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
    /// [`crate::rtp::ReceivedPacket::loss`].
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
    /// H.264 is currently the only supported video codec. A frame is encoded in AAC format with
    /// four-byte lengths. That is, each NAL is encoded as a `u32` length in big-endian format
    /// followed by the actual contents of the NAL (including "emulation prevention three" bytes).
    /// In the future, a configuration parameter may allow the caller to request Annex B encoding
    /// instead.  See [#44](https://github.com/scottlamb/retina/issues/44).
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

/// Turns RTP packets into [`CodecItem`]s.
///
/// This interface unstable and for internal use; it's exposed for direct fuzzing and benchmarking.
#[doc(hidden)]
#[derive(Debug)]
pub struct Depacketizer(DepacketizerInner);

#[derive(Debug)]
enum DepacketizerInner {
    Aac(Box<aac::Depacketizer>),
    SimpleAudio(Box<simple_audio::Depacketizer>),
    G723(Box<g723::Depacketizer>),
    H264(Box<h264::Depacketizer>),
    #[cfg(feature = "h265")]
    H265(Box<h265::Depacketizer>),
    Onvif(Box<onvif::Depacketizer>),
    Jpeg(Box<jpeg::Depacketizer>),
}

impl Depacketizer {
    pub fn new(
        media: &str,
        encoding_name: &str,
        clock_rate: u32,
        channels: Option<NonZeroU16>,
        format_specific_params: Option<&str>,
    ) -> Result<Self, String> {
        use onvif::CompressionType;

        // RTP Payload Format Media Types
        // https://www.iana.org/assignments/rtp-parameters/rtp-parameters.xhtml#rtp-parameters-2
        Ok(Depacketizer(match (media, encoding_name) {
            ("video", "h264") => DepacketizerInner::H264(Box::new(h264::Depacketizer::new(
                clock_rate,
                format_specific_params,
            )?)),
            #[cfg(feature = "h265")]
            ("video", "h265") => DepacketizerInner::H265(Box::new(h265::Depacketizer::new(
                clock_rate,
                format_specific_params,
            )?)),
            ("image" | "video", "jpeg") => {
                DepacketizerInner::Jpeg(Box::new(jpeg::Depacketizer::new()))
            }
            ("audio", "mpeg4-generic") => DepacketizerInner::Aac(Box::new(aac::Depacketizer::new(
                clock_rate,
                channels,
                format_specific_params,
            )?)),
            ("audio", "g726-16") => DepacketizerInner::SimpleAudio(Box::new(
                simple_audio::Depacketizer::new(clock_rate, 2),
            )),
            ("audio", "g726-24") => DepacketizerInner::SimpleAudio(Box::new(
                simple_audio::Depacketizer::new(clock_rate, 3),
            )),
            ("audio", "dvi4") | ("audio", "g726-32") => DepacketizerInner::SimpleAudio(Box::new(
                simple_audio::Depacketizer::new(clock_rate, 4),
            )),
            ("audio", "g726-40") => DepacketizerInner::SimpleAudio(Box::new(
                simple_audio::Depacketizer::new(clock_rate, 5),
            )),
            ("audio", "pcma") | ("audio", "pcmu") | ("audio", "u8") | ("audio", "g722") => {
                DepacketizerInner::SimpleAudio(Box::new(simple_audio::Depacketizer::new(
                    clock_rate, 8,
                )))
            }
            ("audio", "l16") => DepacketizerInner::SimpleAudio(Box::new(
                simple_audio::Depacketizer::new(clock_rate, 16),
            )),
            // Dahua cameras when configured with G723 send packets with a
            // non-standard encoding-name "G723.1" and length 40, which doesn't
            // make sense. Don't try to depacketize these.
            ("audio", "g723") => {
                DepacketizerInner::G723(Box::new(g723::Depacketizer::new(clock_rate)?))
            }
            ("application", "vnd.onvif.metadata") => DepacketizerInner::Onvif(Box::new(
                onvif::Depacketizer::new(CompressionType::Uncompressed),
            )),
            ("application", "vnd.onvif.metadata.gzip") => DepacketizerInner::Onvif(Box::new(
                onvif::Depacketizer::new(CompressionType::GzipCompressed),
            )),
            ("application", "vnd.onvif.metadata.exi.onvif") => DepacketizerInner::Onvif(Box::new(
                onvif::Depacketizer::new(CompressionType::ExiDefault),
            )),
            ("application", "vnd.onvif.metadata.exi.ext") => DepacketizerInner::Onvif(Box::new(
                onvif::Depacketizer::new(CompressionType::ExiInBand),
            )),
            (_, _) => {
                log::info!(
                    "no depacketizer for media/encoding_name {}/{}",
                    media,
                    encoding_name
                );
                return Err(format!(
                    "no depacketizer for media/encoding_name {media}/{encoding_name}"
                ));
            }
        }))
    }

    /// Returns the current codec parameters, if known.
    ///
    /// See documentation at [`crate::client::Stream::parameters`].
    ///
    /// If the caller has called `push` more recently than `pull`, it's currently undefined
    /// whether the depacketizer returns parameters as of the most recently pulled or the upcoming
    /// frame.
    pub fn parameters(&self) -> Option<ParametersRef> {
        match &self.0 {
            DepacketizerInner::Aac(d) => d.parameters(),
            DepacketizerInner::G723(d) => d.parameters(),
            DepacketizerInner::H264(d) => d.parameters(),
            #[cfg(feature = "h265")]
            DepacketizerInner::H265(d) => d.parameters(),
            DepacketizerInner::Onvif(d) => d.parameters(),
            DepacketizerInner::SimpleAudio(d) => d.parameters(),
            DepacketizerInner::Jpeg(d) => d.parameters(),
        }
    }

    /// Supplies a new packet to the depacketizer.
    ///
    /// Depacketizers are not required to buffer unbounded numbers of packets. Between any two
    /// calls to `push`, the caller must call `pull` until `pull` returns `Ok(None)`. The later
    /// `push` call may panic or drop data if this expectation is violated.
    pub fn push(&mut self, input: ReceivedPacket) -> Result<(), String> {
        match &mut self.0 {
            DepacketizerInner::Aac(d) => d.push(input),
            DepacketizerInner::G723(d) => d.push(input),
            DepacketizerInner::H264(d) => d.push(input),
            #[cfg(feature = "h265")]
            DepacketizerInner::H265(d) => d.push(input),
            DepacketizerInner::Onvif(d) => d.push(input),
            DepacketizerInner::SimpleAudio(d) => d.push(input),
            DepacketizerInner::Jpeg(d) => d.push(input),
        }
    }

    /// Retrieves a completed frame from the depacketizer.
    ///
    /// Some packetization formats support aggregating multiple frames into one packet, so a single
    /// `push` call may cause `pull` to return `Ok(Some(...))` more than once.
    pub fn pull(
        &mut self,
        conn_ctx: &ConnectionContext,
        stream_ctx: &StreamContext,
    ) -> Result<Option<CodecItem>, Error> {
        match &mut self.0 {
            DepacketizerInner::Aac(d) => d.pull(conn_ctx, stream_ctx),
            DepacketizerInner::G723(d) => Ok(d.pull()),
            DepacketizerInner::H264(d) => Ok(d.pull()),
            #[cfg(feature = "h265")]
            DepacketizerInner::H265(d) => Ok(d.pull()),
            DepacketizerInner::Onvif(d) => Ok(d.pull()),
            DepacketizerInner::SimpleAudio(d) => Ok(d.pull()),
            DepacketizerInner::Jpeg(d) => Ok(d.pull()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // See with: cargo test -- --nocapture codec::tests::print_sizes
    #[test]
    fn print_sizes() {
        crate::testutil::init_logging();
        for (name, size) in &[
            ("Depacketizer", std::mem::size_of::<Depacketizer>()),
            (
                "aac::Depacketizer",
                std::mem::size_of::<aac::Depacketizer>(),
            ),
            (
                "g723::Depacketizer",
                std::mem::size_of::<g723::Depacketizer>(),
            ),
            (
                "h264::Depacketizer",
                std::mem::size_of::<h264::Depacketizer>(),
            ),
            #[cfg(feature = "h265")]
            (
                "h265::Depacketizer",
                std::mem::size_of::<h265::Depacketizer>(),
            ),
            (
                "onvif::Depacketizer",
                std::mem::size_of::<onvif::Depacketizer>(),
            ),
            (
                "simple_audio::Depacketizer",
                std::mem::size_of::<simple_audio::Depacketizer>(),
            ),
            ("CodecItem", std::mem::size_of::<CodecItem>()),
            ("VideoFrame", std::mem::size_of::<VideoFrame>()),
            ("AudioFrame", std::mem::size_of::<AudioFrame>()),
            ("MessageFrame", std::mem::size_of::<MessageFrame>()),
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
