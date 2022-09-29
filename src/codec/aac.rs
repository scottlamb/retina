// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! AAC (Advanced Audio Codec) depacketization.
//! There are many intertwined standards; see the following references:
//! *   [RFC 3640](https://datatracker.ietf.org/doc/html/rfc3640): RTP Payload
//!     for Transport of MPEG-4 Elementary Streams.
//! *   ISO/IEC 13818-7: Advanced Audio Coding.
//! *   ISO/IEC 14496: Information technology — Coding of audio-visual objects
//!     *   ISO/IEC 14496-1: Systems.
//!     *   ISO/IEC 14496-3: Audio, subpart 1: Main.
//!     *   ISO/IEC 14496-3: Audio, subpart 4: General Audio coding (GA) — AAC, TwinVQ, BSAC.
//!     *   [ISO/IEC 14496-12](https://standards.iso.org/ittf/PubliclyAvailableStandards/c068960_ISO_IEC_14496-12_2015.zip):
//!         ISO base media file format.
//!     *   ISO/IEC 14496-14: MP4 File Format.

use bitstream_io::BitRead;
use bytes::{BufMut, Bytes, BytesMut};
use std::{
    convert::TryFrom,
    fmt::Debug,
    num::{NonZeroU16, NonZeroU32},
};

use crate::{error::ErrorInt, rtp::ReceivedPacket, ConnectionContext, Error, StreamContext};

use super::{AudioParameters, CodecItem};

/// An AudioSpecificConfig as in ISO/IEC 14496-3 section 1.6.2.1.
///
/// Currently stores the raw form and a few fields of interest.
#[derive(Clone, Debug)]
struct AudioSpecificConfig {
    parameters: AudioParameters,

    frame_length: NonZeroU16,
    channels: &'static ChannelConfig,
}

/// A channel configuration as in ISO/IEC 14496-3 Table 1.19.
#[derive(Debug)]
struct ChannelConfig {
    channels: u16,

    /// The "number of considered channels" as defined in ISO/IEC 13818-7 Term
    /// 3.58. Roughly, non-subwoofer channels.
    ncc: u16,

    /// A human-friendly name for the channel configuration.
    // The name is used in tests and in the Debug output. Suppress dead code warning.
    #[cfg_attr(not(test), allow(dead_code))]
    name: &'static str,
}

#[rustfmt::skip]
const CHANNEL_CONFIGS: [Option<ChannelConfig>; 8] = [
    /* 0 */ None, // "defined in AOT related SpecificConfig"
    /* 1 */ Some(ChannelConfig { channels: 1, ncc: 1, name: "mono" }),
    /* 2 */ Some(ChannelConfig { channels: 2, ncc: 2, name: "stereo" }),
    /* 3 */ Some(ChannelConfig { channels: 3, ncc: 3, name: "3.0" }),
    /* 4 */ Some(ChannelConfig { channels: 4, ncc: 4, name: "4.0" }),
    /* 5 */ Some(ChannelConfig { channels: 5, ncc: 5, name: "5.0" }),
    /* 6 */ Some(ChannelConfig { channels: 6, ncc: 5, name: "5.1" }),
    /* 7 */ Some(ChannelConfig { channels: 8, ncc: 7, name: "7.1" }),
];

impl AudioSpecificConfig {
    /// Parses from raw bytes.
    fn parse(raw: &[u8]) -> Result<Self, String> {
        let mut r = bitstream_io::BitReader::endian(raw, bitstream_io::BigEndian);
        let audio_object_type = match r
            .read::<u8>(5)
            .map_err(|e| format!("unable to read audio_object_type: {}", e))?
        {
            31 => {
                32 + r
                    .read::<u8>(6)
                    .map_err(|e| format!("unable to read audio_object_type ext: {}", e))?
            }
            o => o,
        };

        // ISO/IEC 14496-3 section 1.6.3.3.
        let sampling_frequency = match r
            .read::<u8>(4)
            .map_err(|e| format!("unable to read sampling_frequency: {}", e))?
        {
            0x0 => 96_000,
            0x1 => 88_200,
            0x2 => 64_000,
            0x3 => 48_000,
            0x4 => 44_100,
            0x5 => 32_000,
            0x6 => 24_000,
            0x7 => 22_050,
            0x8 => 16_000,
            0x9 => 12_000,
            0xa => 11_025,
            0xb => 8_000,
            0xc => 7_350,
            v @ 0xd | v @ 0xe => {
                return Err(format!("reserved sampling_frequency_index value 0x{:x}", v))
            }
            0xf => r
                .read::<u32>(24)
                .map_err(|e| format!("unable to read sampling_frequency ext: {}", e))?,
            0x10..=0xff => unreachable!(),
        };
        let channels = {
            let c = r
                .read::<u8>(4)
                .map_err(|e| format!("unable to read channels: {}", e))?;
            CHANNEL_CONFIGS
                .get(usize::from(c))
                .ok_or_else(|| format!("reserved channelConfiguration 0x{:x}", c))?
                .as_ref()
                .ok_or_else(|| "program_config_element parsing unimplemented".to_string())?
        };
        if audio_object_type == 5 || audio_object_type == 29 {
            // extensionSamplingFrequencyIndex + extensionSamplingFrequency.
            if r.read::<u8>(4)
                .map_err(|e| format!("unable to read extensionSamplingFrequencyIndex: {}", e))?
                == 0xf
            {
                r.skip(24)
                    .map_err(|e| format!("unable to read extensionSamplingFrequency: {}", e))?;
            }
            // audioObjectType (a different one) + extensionChannelConfiguration.
            if r.read::<u8>(5)
                .map_err(|e| format!("unable to read second audioObjectType: {}", e))?
                == 22
            {
                r.skip(4)
                    .map_err(|e| format!("unable to read extensionChannelConfiguration: {}", e))?;
            }
        }

        // The supported types here are the ones that use GASpecificConfig.
        match audio_object_type {
            1 | 2 | 3 | 4 | 6 | 7 | 17 | 19 | 20 | 21 | 22 | 23 => {}
            o => return Err(format!("unsupported audio_object_type {}", o)),
        }

        // GASpecificConfig, ISO/IEC 14496-3 section 4.4.1.
        let frame_length_flag = r
            .read_bit()
            .map_err(|e| format!("unable to read frame_length_flag: {}", e))?;
        let frame_length = match (audio_object_type, frame_length_flag) {
            (3 /* AAC SR */, false) => NonZeroU16::new(256).expect("non-zero"),
            (3 /* AAC SR */, true) => {
                return Err("frame_length_flag must be false for AAC SSR".into())
            }
            (23 /* ER AAC LD */, false) => NonZeroU16::new(512).expect("non-zero"),
            (23 /* ER AAC LD */, true) => NonZeroU16::new(480).expect("non-zero"),
            (_, false) => NonZeroU16::new(1024).expect("non-zero"),
            (_, true) => NonZeroU16::new(960).expect("non-zero"),
        };

        // https://datatracker.ietf.org/doc/html/rfc6381#section-3.3
        let rfc6381_codec = Some(format!("mp4a.40.{}", audio_object_type));

        Ok(AudioSpecificConfig {
            parameters: AudioParameters {
                // See also TODO asking if clock_rate and sampling_frequency must match.
                clock_rate: sampling_frequency,
                rfc6381_codec,
                frame_length: Some(NonZeroU32::from(frame_length)),
                extra_data: raw.to_owned(),
                sample_entry: Some(make_sample_entry(channels, sampling_frequency, raw)?),
            },
            frame_length,
            channels,
        })
    }
}

/// Overwrites a buffer with a varint length, returning the length of the length.
/// See ISO/IEC 14496-1 section 8.3.3.
fn set_length(len: usize, data: &mut [u8]) -> Result<usize, String> {
    if len < 1 << 7 {
        data[0] = len as u8;
        Ok(1)
    } else if len < 1 << 14 {
        data[0] = ((len & 0x7F) | 0x80) as u8;
        data[1] = (len >> 7) as u8;
        Ok(2)
    } else if len < 1 << 21 {
        data[0] = ((len & 0x7F) | 0x80) as u8;
        data[1] = (((len >> 7) & 0x7F) | 0x80) as u8;
        data[2] = (len >> 14) as u8;
        Ok(3)
    } else if len < 1 << 28 {
        data[0] = ((len & 0x7F) | 0x80) as u8;
        data[1] = (((len >> 7) & 0x7F) | 0x80) as u8;
        data[2] = (((len >> 14) & 0x7F) | 0x80) as u8;
        data[3] = (len >> 21) as u8;
        Ok(4)
    } else {
        // BaseDescriptor sets a maximum length of 2**28 - 1.
        Err(format!("length {} too long", len))
    }
}

/// Writes a box length and type (four-character code) for everything appended
/// in the supplied scope.
macro_rules! write_box {
    ($buf:expr, $fourcc:expr, $b:block) => {
        // The caller uses `&mut buf`. clippy likes to complain about the `&mut`
        // being unnecessary for len(), but it is necessary for other things.
        // The macro also can't store `$buf` in its own local, because `$b`
        // is expected to reference `$buf` via the original name.
        #[allow(clippy::unnecessary_mut_passed)]
        {
            let _: &mut Vec<u8> = $buf; // type-check.

            let pos_start = $buf.len();
            let fourcc: &[u8; 4] = $fourcc;
            $buf.extend_from_slice(&[0, 0, 0, 0, fourcc[0], fourcc[1], fourcc[2], fourcc[3]]);
            let r = {
                $b;
            };
            let pos_end = $buf.len();
            let len = pos_end.checked_sub(pos_start).unwrap();
            $buf[pos_start..pos_start + 4].copy_from_slice(
                &u32::try_from(len)
                    .map_err(|_| format!("box length {} exceeds u32::MAX", len))?
                    .to_be_bytes()[..],
            );
            r
        }
    };
}

/// Writes a descriptor tag and length for everything appended in the supplied
/// scope. See ISO/IEC 14496-1 Table 1 for the `tag`.
macro_rules! write_descriptor {
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
        let len = pos_end.checked_sub(pos_start + 5).unwrap();
        let len_len = set_length(len, &mut $buf[pos_start + 1..pos_start + 4])?;
        $buf.copy_within(pos_start + 5..pos_end, pos_start + 1 + len_len);
        $buf.truncate(pos_end + len_len - 4);
        r
    }};
}

/// Returns an MP4AudioSampleEntry (`mp4a`) box as in ISO/IEC 14496-14 section 5.6.1.
/// `config` should be a raw AudioSpecificConfig.
fn make_sample_entry(
    channels: &ChannelConfig,
    sampling_frequency: u32,
    config: &[u8],
) -> Result<Vec<u8>, String> {
    let mut buf = Vec::new();

    // Write an MP4AudioSampleEntry (`mp4a`), as in ISO/IEC 14496-14 section 5.6.1.
    // It's based on AudioSampleEntry, ISO/IEC 14496-12 section 12.2.3.2,
    // in turn based on SampleEntry, ISO/IEC 14496-12 section 8.5.2.2.
    write_box!(&mut buf, b"mp4a", {
        buf.extend_from_slice(&[
            0, 0, 0, 0, // SampleEntry.reserved
            0, 0, 0, 1, // SampleEntry.reserved, SampleEntry.data_reference_index (1)
            0, 0, 0, 0, // AudioSampleEntry.reserved
            0, 0, 0, 0, // AudioSampleEntry.reserved
        ]);
        buf.put_u16(channels.channels);
        buf.extend_from_slice(&[
            0x00, 0x10, // AudioSampleEntry.samplesize
            0x00, 0x00, 0x00, 0x00, // AudioSampleEntry.pre_defined, AudioSampleEntry.reserved
        ]);

        // ISO/IEC 14496-12 section 12.2.3 says to put the samplerate (aka
        // clock_rate aka sampling_frequency) as a 16.16 fixed-point number or
        // use a SamplingRateBox. The latter also requires changing the
        // version/structure of the AudioSampleEntryBox and the version of the
        // stsd box. Just support the former for now.
        let sampling_frequency = u16::try_from(sampling_frequency)
            .map_err(|_| format!("aac sampling_frequency={} unsupported", sampling_frequency))?;
        buf.put_u32(u32::from(sampling_frequency) << 16);

        // Write the embedded ESDBox (`esds`), as in ISO/IEC 14496-14 section 5.6.1.
        write_box!(&mut buf, b"esds", {
            buf.put_u32(0); // version

            write_descriptor!(&mut buf, 0x03 /* ES_DescrTag */, {
                // The ESDBox contains an ES_Descriptor, defined in ISO/IEC 14496-1 section 8.3.3.
                // ISO/IEC 14496-14 section 3.1.2 has advice on how to set its
                // fields within the scope of a .mp4 file.
                buf.extend_from_slice(&[
                    0, 0,    // ES_ID=0
                    0x00, // streamDependenceFlag, URL_Flag, OCRStreamFlag, streamPriority.
                ]);

                // DecoderConfigDescriptor, defined in ISO/IEC 14496-1 section 7.2.6.6.
                write_descriptor!(&mut buf, 0x04 /* DecoderConfigDescrTag */, {
                    buf.extend_from_slice(&[
                        0x40, // objectTypeIndication = Audio ISO/IEC 14496-3
                        0x15, // streamType = audio, upstream = false, reserved = 1
                    ]);

                    // bufferSizeDb is "the size of the decoding buffer for this
                    // elementary stream in byte". ISO/IEC 13818-7 section
                    // 8.2.2.1 defines the total decoder input buffer size as
                    // 6144 bits per NCC.
                    let buffer_size_bytes = (6144 / 8) * u32::from(channels.ncc);
                    debug_assert!(buffer_size_bytes <= 0xFF_FFFF);

                    // buffer_size_bytes as a 24-bit number
                    buf.put_u8((buffer_size_bytes >> 16) as u8);
                    buf.put_u16(buffer_size_bytes as u16);

                    let max_bitrate =
                        (6144 / 1024) * u32::from(channels.ncc) * u32::from(sampling_frequency);
                    buf.put_u32(max_bitrate);

                    // avg_bitrate. ISO/IEC 14496-1 section 7.2.6.6 says "for streams with
                    // variable bitrate this value shall be set to zero."
                    buf.put_u32(0);

                    // AudioSpecificConfiguration, ISO/IEC 14496-3 subpart 1 section 1.6.2.
                    write_descriptor!(&mut buf, 0x05 /* DecSpecificInfoTag */, {
                        buf.extend_from_slice(config);
                    });
                });

                // SLConfigDescriptor, ISO/IEC 14496-1 section 7.3.2.3.1.
                write_descriptor!(&mut buf, 0x06 /* SLConfigDescrTag */, {
                    buf.put_u8(2); // predefined = reserved for use in MP4 files
                });
            });
        });
    });
    Ok(buf)
}

/// Parses metadata from the `format-specific-params` of a SDP `fmtp` media attribute.
/// The metadata is defined in [RFC 3640 section
/// 4.1](https://datatracker.ietf.org/doc/html/rfc3640#section-4.1).
fn parse_format_specific_params(
    clock_rate: u32,
    format_specific_params: &str,
) -> Result<AudioSpecificConfig, String> {
    let mut mode = None;
    let mut config = None;
    let mut size_length = None;
    let mut index_length = None;
    let mut index_delta_length = None;
    for p in format_specific_params.split(';') {
        let p = p.trim();
        if p.is_empty() {
            // Reolink cameras leave a trailing ';'.
            continue;
        }
        let (key, value) = p
            .split_once('=')
            .ok_or_else(|| format!("bad format-specific-param {}", p))?;
        match &key.to_ascii_lowercase()[..] {
            "config" => {
                config = Some(
                    hex::decode(value)
                        .map_err(|_| "config has invalid hex encoding".to_string())?,
                );
            }
            "mode" => mode = Some(value),
            "sizelength" => {
                size_length =
                    Some(u16::from_str_radix(value, 10).map_err(|_| "bad sizeLength".to_string())?);
            }
            "indexlength" => {
                index_length = Some(
                    u16::from_str_radix(value, 10).map_err(|_| "bad indexLength".to_string())?,
                );
            }
            "indexdeltalength" => {
                index_delta_length = Some(
                    u16::from_str_radix(value, 10)
                        .map_err(|_| "bad indexDeltaLength".to_string())?,
                );
            }
            _ => {}
        }
    }
    // https://datatracker.ietf.org/doc/html/rfc3640#section-3.3.6 AAC-hbr
    if mode != Some("AAC-hbr") {
        return Err(format!("Expected mode AAC-hbr, got {:#?}", mode));
    }
    let config = config.ok_or_else(|| "config must be specified".to_string())?;
    if size_length != Some(13) || index_length != Some(3) || index_delta_length != Some(3) {
        return Err(format!(
            "Unexpected sizeLength={:?} indexLength={:?} indexDeltaLength={:?}",
            size_length, index_length, index_delta_length
        ));
    }

    let config = AudioSpecificConfig::parse(&config[..])?;

    // TODO: is this a requirement? I might have read somewhere that the RTP clock rate can be
    // a multiple of the AudioSpecificConfig sampling_frequency or vice versa.
    if clock_rate != config.parameters.clock_rate {
        return Err(format!(
            "Expected RTP clock rate {} and AAC sampling frequency {} to match",
            clock_rate, config.parameters.clock_rate,
        ));
    }

    Ok(config)
}

#[derive(Debug)]
pub(crate) struct Depacketizer {
    config: AudioSpecificConfig,
    state: DepacketizerState,
}

/// [DepacketizerState] holding access units within a single RTP packet.
///
/// This is the state used when there are multiple access units within a packet
/// (thus the name), when there's a single access unit, and even at the
/// beginning of a fragment.
#[derive(Debug)]
struct Aggregate {
    pkt: ReceivedPacket,

    /// RTP packets lost before the next frame in this aggregate. Includes old
    /// loss that caused a previous fragment to be too short.
    /// This should be 0 when `frame_i > 0`.
    loss: u16,

    /// True iff there was loss immediately before the packet that started this
    /// aggregate. The distinction between old and recent loss is relevant
    /// because only the latter should be capable of causing following fragments
    /// to be too short.
    loss_since_mark: bool,

    /// The index in range `[0, frame_count)` of the next frame to return from `pull`.
    frame_i: u16,

    /// The total non-zero total frames within this aggregate (including ones which have already
    /// been returned by `pull`).
    frame_count: u16,

    /// The starting byte offset of `frame_i`'s data within `pkt.payload()`.
    data_off: usize,
}

/// The received prefix of a single access unit which has been spread across multiple packets.
#[derive(Debug)]
struct Fragment {
    rtp_timestamp: u16,

    /// Number of RTP packets lost before between the previous output AudioFrame
    /// and now.
    loss: u16,

    /// True iff packets have been lost since the last mark. If so, this
    /// fragment may be incomplete.
    loss_since_mark: bool,

    size: u16,
    buf: BytesMut,
}

/// State of the depacketizer between calls to `push` and `pull`.
#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
enum DepacketizerState {
    /// State when there's no buffered data.
    Idle {
        prev_loss: u16,
        loss_since_mark: bool,
    },

    /// State after a packet has been RTP packet has been received. As described at
    /// [`Aggregate`], this may hold the first packet of a fragment, one packet, or multiple
    /// complete packets.
    Aggregated(Aggregate),

    /// State when a prefix of a fragmented packet has been received.
    Fragmented(Fragment),
    Ready(super::AudioFrame),
}

impl Default for DepacketizerState {
    fn default() -> Self {
        DepacketizerState::Idle {
            prev_loss: 0,
            loss_since_mark: false,
        }
    }
}

impl Depacketizer {
    pub(super) fn new(
        clock_rate: u32,
        channels: Option<NonZeroU16>,
        format_specific_params: Option<&str>,
    ) -> Result<Self, String> {
        let format_specific_params = format_specific_params
            .ok_or_else(|| "AAC requires format specific params".to_string())?;
        let config = parse_format_specific_params(clock_rate, format_specific_params)?;
        if matches!(channels, Some(c) if c.get() != config.channels.channels) {
            return Err(format!(
                "Expected RTP channels {:?} and AAC channels {:?} to match",
                channels, config.channels
            ));
        }
        Ok(Self {
            config,
            state: DepacketizerState::default(),
        })
    }

    pub(super) fn parameters(&self) -> Option<super::ParametersRef> {
        Some(super::ParametersRef::Audio(&self.config.parameters))
    }

    pub(super) fn push(&mut self, pkt: ReceivedPacket) -> Result<(), String> {
        if pkt.loss() > 0 {
            if let DepacketizerState::Fragmented(ref mut f) = self.state {
                log::debug!(
                    "Discarding in-progress fragmented AAC frame due to loss of {} RTP packets.",
                    pkt.loss(),
                );
                self.state = DepacketizerState::Idle {
                    prev_loss: f.loss, // note this packet's loss will be added in later.
                    loss_since_mark: true,
                };
            }
        }

        // Read the AU headers.
        let payload = pkt.payload();
        if payload.len() < 2 {
            return Err("packet too short for au-header-length".to_string());
        }
        let au_headers_length_bits = u16::from_be_bytes([payload[0], payload[1]]);

        // AAC-hbr requires 16-bit AU headers: 13-bit size, 3-bit index.
        if (au_headers_length_bits & 0x7) != 0 {
            return Err(format!("bad au-headers-length {}", au_headers_length_bits));
        }
        let au_headers_count = au_headers_length_bits >> 4;
        let data_off = 2 + (usize::from(au_headers_count) << 1);
        if payload.len() < data_off {
            return Err("packet too short for au-headers".to_string());
        }
        match &mut self.state {
            DepacketizerState::Fragmented(ref mut frag) => {
                if au_headers_count != 1 {
                    return Err(format!(
                        "Got {}-AU packet while fragment in progress",
                        au_headers_count
                    ));
                }
                if (pkt.timestamp().timestamp as u16) != frag.rtp_timestamp {
                    return Err(format!(
                        "Timestamp changed from 0x{:04x} to 0x{:04x} mid-fragment",
                        frag.rtp_timestamp,
                        pkt.timestamp().timestamp as u16
                    ));
                }
                let au_header = u16::from_be_bytes([payload[2], payload[3]]);
                let size = usize::from(au_header >> 3);
                if size != usize::from(frag.size) {
                    return Err(format!("size changed {}->{} mid-fragment", frag.size, size));
                }
                let data = &payload[data_off..];
                match (frag.buf.len() + data.len()).cmp(&size) {
                    std::cmp::Ordering::Less => {
                        if pkt.mark() {
                            if frag.loss_since_mark {
                                self.state = DepacketizerState::Idle {
                                    prev_loss: frag.loss,
                                    loss_since_mark: false,
                                };
                                return Ok(());
                            }
                            return Err(format!(
                                "frag marked complete when {}+{}<{}",
                                frag.buf.len(),
                                data.len(),
                                size
                            ));
                        }
                        frag.buf.extend_from_slice(data);
                    }
                    std::cmp::Ordering::Equal => {
                        if !pkt.mark() {
                            return Err(
                                "frag not marked complete when full data present".to_string()
                            );
                        }
                        frag.buf.extend_from_slice(data);
                        self.state = DepacketizerState::Ready(super::AudioFrame {
                            ctx: *pkt.ctx(),
                            loss: frag.loss,
                            frame_length: NonZeroU32::from(self.config.frame_length),
                            stream_id: pkt.stream_id(),
                            timestamp: pkt.timestamp(),
                            data: std::mem::take(&mut frag.buf).freeze(),
                        });
                    }
                    std::cmp::Ordering::Greater => return Err("too much data in fragment".into()),
                }
            }
            DepacketizerState::Aggregated(_) => panic!("push when already in state aggregated"),
            DepacketizerState::Idle {
                prev_loss,
                loss_since_mark,
            } => {
                if au_headers_count == 0 {
                    return Err("aggregate with no headers".to_string());
                }
                let loss = pkt.loss();
                self.state = DepacketizerState::Aggregated(Aggregate {
                    pkt,
                    loss: *prev_loss + loss,
                    loss_since_mark: *loss_since_mark || loss > 0,
                    frame_i: 0,
                    frame_count: au_headers_count,
                    data_off,
                });
            }
            DepacketizerState::Ready(..) => panic!("push when in state ready"),
        }
        Ok(())
    }

    pub(super) fn pull(
        &mut self,
        conn_ctx: &ConnectionContext,
        stream_ctx: &StreamContext,
    ) -> Result<Option<super::CodecItem>, Error> {
        match std::mem::take(&mut self.state) {
            s @ DepacketizerState::Idle { .. } | s @ DepacketizerState::Fragmented(..) => {
                self.state = s;
                Ok(None)
            }
            DepacketizerState::Ready(f) => {
                self.state = DepacketizerState::default();
                Ok(Some(CodecItem::AudioFrame(f)))
            }
            DepacketizerState::Aggregated(mut agg) => {
                let i = usize::from(agg.frame_i);
                let payload = agg.pkt.payload();
                let mark = agg.pkt.mark();
                let au_header = u16::from_be_bytes([payload[2 + (i << 1)], payload[3 + (i << 1)]]);
                let size = usize::from(au_header >> 3);
                let index = au_header & 0b111;
                if index != 0 {
                    // First AU's index must be zero; subsequent AU's deltas > 1
                    // indicate interleaving, which we don't support.
                    // TODO: https://datatracker.ietf.org/doc/html/rfc3640#section-3.3.6
                    // says "receivers MUST support de-interleaving".
                    return Err(error(
                        *conn_ctx,
                        stream_ctx,
                        agg,
                        "interleaving not yet supported".to_owned(),
                    ));
                }
                if size > payload.len() - agg.data_off {
                    // start of fragment
                    if agg.frame_count != 1 {
                        return Err(error(
                            *conn_ctx,
                            stream_ctx,
                            agg,
                            "fragmented AUs must not share packets".to_owned(),
                        ));
                    }
                    if mark {
                        if agg.loss_since_mark {
                            log::debug!(
                                "Discarding in-progress fragmented AAC frame due to loss of {} RTP packets.",
                                agg.loss
                            );
                            self.state = DepacketizerState::Idle {
                                prev_loss: agg.loss,
                                loss_since_mark: false,
                            };
                            return Ok(None);
                        }
                        return Err(error(
                            *conn_ctx,
                            stream_ctx,
                            agg,
                            "mark can't be set on beginning of fragment".to_owned(),
                        ));
                    }
                    let mut buf = BytesMut::with_capacity(size);
                    buf.extend_from_slice(&payload[agg.data_off..]);
                    self.state = DepacketizerState::Fragmented(Fragment {
                        rtp_timestamp: agg.pkt.timestamp().timestamp as u16,
                        loss: agg.loss,
                        loss_since_mark: agg.loss_since_mark,
                        size: size as u16,
                        buf,
                    });
                    return Ok(None);
                }
                if !mark {
                    return Err(error(
                        *conn_ctx,
                        stream_ctx,
                        agg,
                        "mark must be set on non-fragmented au".to_owned(),
                    ));
                }

                let delta = u32::from(agg.frame_i) * u32::from(self.config.frame_length.get());
                let agg_timestamp = agg.pkt.timestamp();
                let frame = super::AudioFrame {
                    ctx: *agg.pkt.ctx(),
                    loss: agg.loss,
                    stream_id: agg.pkt.stream_id(),
                    frame_length: NonZeroU32::from(self.config.frame_length),

                    // u16 * u16 can't overflow u32, but i64 + u32 can overflow i64.
                    timestamp: match agg_timestamp.try_add(delta) {
                        Some(t) => t,
                        None => {
                            return Err(error(
                                *conn_ctx,
                                stream_ctx,
                                agg,
                                format!(
                                    "aggregate timestamp {} + {} overflows",
                                    agg_timestamp, delta
                                ),
                            ))
                        }
                    },
                    data: Bytes::copy_from_slice(&payload[agg.data_off..agg.data_off + size]),
                };
                agg.loss = 0;
                agg.data_off += size;
                agg.frame_i += 1;
                if agg.frame_i < agg.frame_count {
                    self.state = DepacketizerState::Aggregated(agg);
                }
                Ok(Some(CodecItem::AudioFrame(frame)))
            }
        }
    }
}

fn error(
    conn_ctx: ConnectionContext,
    stream_ctx: &StreamContext,
    agg: Aggregate,
    description: String,
) -> Error {
    Error(std::sync::Arc::new(ErrorInt::RtpPacketError {
        conn_ctx,
        stream_ctx: *stream_ctx,
        pkt_ctx: *agg.pkt.ctx(),
        stream_id: agg.pkt.stream_id(),
        ssrc: agg.pkt.ssrc(),
        sequence_number: agg.pkt.sequence_number(),
        description,
    }))
}

#[cfg(test)]
mod tests {
    use crate::{rtp::ReceivedPacketBuilder, PacketContext};

    use super::*;

    #[test]
    fn parse_audio_specific_config() {
        let dahua = AudioSpecificConfig::parse(&[0x11, 0x88]).unwrap();
        assert_eq!(dahua.parameters.clock_rate, 48_000);
        assert_eq!(dahua.channels.name, "mono");
        assert_eq!(dahua.parameters.rfc6381_codec(), Some("mp4a.40.2"));

        let bunny = AudioSpecificConfig::parse(&[0x14, 0x90]).unwrap();
        assert_eq!(bunny.parameters.clock_rate, 12_000);
        assert_eq!(bunny.channels.name, "stereo");
        assert_eq!(bunny.parameters.rfc6381_codec(), Some("mp4a.40.2"));

        let rfc3640 = AudioSpecificConfig::parse(&[0x11, 0xB0]).unwrap();
        assert_eq!(rfc3640.parameters.clock_rate, 48_000);
        assert_eq!(rfc3640.channels.name, "5.1");
        assert_eq!(rfc3640.parameters.rfc6381_codec(), Some("mp4a.40.2"));
    }

    #[test]
    fn depacketize_happy_path() {
        let mut d = Depacketizer::new(
            48_000, // clock rate, as specified in rtpmap
            None, // channels, as specified in rtpmap
            Some("streamtype=5;profile-level-id=1;mode=AAC-hbr;sizelength=13;indexlength=3;indexdeltalength=3;config=1188"),
        ).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 42,
            clock_rate: NonZeroU32::new(48_000).unwrap(),
            start: 0,
        };

        // Single frame.
        d.push(
            ReceivedPacketBuilder {
                ctx: PacketContext::dummy(),
                stream_id: 0,
                sequence_number: 0,
                timestamp,
                payload_type: 0,
                ssrc: 0,
                mark: true,
                loss: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x20, // AU-header: AU-size=4 + AU-index=0
                b'a', b's', b'd', b'f',
            ])
            .unwrap(),
        )
        .unwrap();
        let a = match d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
        {
            Some(CodecItem::AudioFrame(a)) => a,
            _ => unreachable!(),
        };
        assert_eq!(a.timestamp, timestamp);
        assert_eq!(&a.data[..], b"asdf");
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());

        // Aggregate of 3 frames.
        d.push(
            ReceivedPacketBuilder {
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x30, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 3 headers
                0x00, 0x18, // AU-header: AU-size=3 + AU-index=0
                0x00, 0x18, // AU-header: AU-size=3 + AU-index-delta=0
                0x00, 0x18, // AU-header: AU-size=3 + AU-index-delta=0
                b'f', b'o', b'o', b'b', b'a', b'r', b'b', b'a', b'z',
            ])
            .unwrap(),
        )
        .unwrap();
        let a = match d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
        {
            Some(CodecItem::AudioFrame(a)) => a,
            _ => unreachable!(),
        };
        assert_eq!(a.timestamp, timestamp);
        assert_eq!(&a.data[..], b"foo");
        let a = match d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
        {
            Some(CodecItem::AudioFrame(a)) => a,
            _ => unreachable!(),
        };
        assert_eq!(a.timestamp, timestamp.try_add(1_024).unwrap());
        assert_eq!(&a.data[..], b"bar");
        let a = match d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
        {
            Some(CodecItem::AudioFrame(a)) => a,
            _ => unreachable!(),
        };
        assert_eq!(a.timestamp, timestamp.try_add(2_048).unwrap());
        assert_eq!(&a.data[..], b"baz");
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());

        // Fragment across 3 packets.
        d.push(
            ReceivedPacketBuilder {
                // fragment 1/3.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x48, // AU-header: AU-size=9 + AU-index=0
                b'f', b'o', b'o',
            ])
            .unwrap(),
        )
        .unwrap();
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());
        d.push(
            ReceivedPacketBuilder {
                // fragment 2/3.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x48, // AU-header: AU-size=9 + AU-index=0
                b'b', b'a', b'r',
            ])
            .unwrap(),
        )
        .unwrap();
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());
        d.push(
            ReceivedPacketBuilder {
                // fragment 3/3.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x48, // AU-header: AU-size=9 + AU-index=0
                b'b', b'a', b'z',
            ])
            .unwrap(),
        )
        .unwrap();
        let a = match d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
        {
            Some(CodecItem::AudioFrame(a)) => a,
            _ => unreachable!(),
        };
        assert_eq!(a.timestamp, timestamp);
        assert_eq!(&a.data[..], b"foobarbaz");
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());
    }

    /// Tests that depacketization skips/reports a frame in which its first packet was lost.
    #[test]
    fn depacketize_fragment_initial_loss() {
        let mut d = Depacketizer::new(
            48_000, // clock rate, as specified in rtpmap
            None, // channels, as specified in rtpmap
            Some("streamtype=5;profile-level-id=1;mode=AAC-hbr;sizelength=13;indexlength=3;indexdeltalength=3;config=1188"),
        ).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 42,
            clock_rate: NonZeroU32::new(48_000).unwrap(),
            start: 0,
        };

        // Fragment
        d.push(
            ReceivedPacketBuilder {
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 1,
                mark: false,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x48, // AU-header: AU-size=9 + AU-index=0
                b'b', b'a', b'r',
            ])
            .unwrap(),
        )
        .unwrap();
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());
        d.push(
            ReceivedPacketBuilder {
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x48, // AU-header: AU-size=9 + AU-index=0
                b'b', b'a', b'z',
            ])
            .unwrap(),
        )
        .unwrap();
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());

        // Following frame reports the loss.
        d.push(
            ReceivedPacketBuilder {
                // single frame.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x20, // AU-header: AU-size=4 + AU-index=0
                b'a', b's', b'd', b'f',
            ])
            .unwrap(),
        )
        .unwrap();
        let a = match d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
        {
            Some(CodecItem::AudioFrame(a)) => a,
            _ => unreachable!(),
        };
        assert_eq!(a.loss, 1);
        assert_eq!(&a.data[..], b"asdf");
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());
    }

    /// Tests that depacketization skips/reports a frame in which an interior frame is lost.
    #[test]
    fn depacketize_fragment_interior_loss() {
        let mut d = Depacketizer::new(
            48_000, // clock rate, as specified in rtpmap
            None, // channels, as specified in rtpmap
            Some("streamtype=5;profile-level-id=1;mode=AAC-hbr;sizelength=13;indexlength=3;indexdeltalength=3;config=1188"),
        ).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 42,
            clock_rate: NonZeroU32::new(48_000).unwrap(),
            start: 0,
        };

        d.push(
            ReceivedPacketBuilder {
                // 1/3
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x48, // AU-header: AU-size=9 + AU-index=0
                b'f', b'o', b'o',
            ])
            .unwrap(),
        )
        .unwrap();
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());
        // Fragment 2/3 is lost
        d.push(
            ReceivedPacketBuilder {
                // 3/3 reports the loss
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 1,
                mark: true,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x48, // AU-header: AU-size=9 + AU-index=0
                b'b', b'a', b'z',
            ])
            .unwrap(),
        )
        .unwrap();
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());

        // Following frame reports the loss.
        d.push(
            ReceivedPacketBuilder {
                // single frame.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x20, // AU-header: AU-size=4 + AU-index=0
                b'a', b's', b'd', b'f',
            ])
            .unwrap(),
        )
        .unwrap();
        let a = match d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
        {
            Some(CodecItem::AudioFrame(a)) => a,
            _ => unreachable!(),
        };
        assert_eq!(a.loss, 1);
        assert_eq!(&a.data[..], b"asdf");
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());
    }

    /// Tests that depacketization skips/reports a frame in which the interior frame is lost.
    #[test]
    fn depacketize_fragment_final_loss() {
        let mut d = Depacketizer::new(
            48_000, // clock rate, as specified in rtpmap
            None, // channels, as specified in rtpmap
            Some("streamtype=5;profile-level-id=1;mode=AAC-hbr;sizelength=13;indexlength=3;indexdeltalength=3;config=1188"),
        ).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 42,
            clock_rate: NonZeroU32::new(48_000).unwrap(),
            start: 0,
        };

        d.push(
            ReceivedPacketBuilder {
                // 1/3
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x48, // AU-header: AU-size=9 + AU-index=0
                b'f', b'o', b'o',
            ])
            .unwrap(),
        )
        .unwrap();
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());
        // Fragment 2/3 is lost
        d.push(
            ReceivedPacketBuilder {
                // 3/3 reports the loss
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 1,
                mark: true,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x48, // AU-header: AU-size=9 + AU-index=0
                b'b', b'a', b'z',
            ])
            .unwrap(),
        )
        .unwrap();
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());

        // Following frame reports the loss.
        d.push(
            ReceivedPacketBuilder {
                // single frame.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x20, // AU-header: AU-size=4 + AU-index=0
                b'a', b's', b'd', b'f',
            ])
            .unwrap(),
        )
        .unwrap();
        let a = match d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
        {
            Some(CodecItem::AudioFrame(a)) => a,
            _ => unreachable!(),
        };
        assert_eq!(a.loss, 1);
        assert_eq!(&a.data[..], b"asdf");
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());
    }

    /// Tests the distinction between `loss` and `loss_since_last_mark`.
    ///
    /// Old loss should get reported via the CodecItem but shouldn't suppress
    /// error checking.
    #[test]
    fn depacketize_fragment_old_loss_doesnt_prevent_error() {
        let mut d = Depacketizer::new(
            48_000, // clock rate, as specified in rtpmap
            None, // channels, as specified in rtpmap
            Some("streamtype=5;profile-level-id=1;mode=AAC-hbr;sizelength=13;indexlength=3;indexdeltalength=3;config=1188"),
        ).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 42,
            clock_rate: NonZeroU32::new(48_000).unwrap(),
            start: 0,
        };

        d.push(
            ReceivedPacketBuilder {
                // end of previous fragment, first parts missing.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 1,
                mark: true,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x48, // AU-header: AU-size=9 + AU-index=0
                b'b', b'a', b'r',
            ])
            .unwrap(),
        )
        .unwrap();
        assert!(d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap()
            .is_none());

        // Incomplete fragment with no reported loss.
        d.push(
            ReceivedPacketBuilder {
                // end of previous fragment, first parts missing.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build([
                // https://datatracker.ietf.org/doc/html/rfc3640#section-3.2.1
                0x00,
                0x10, // AU-headers-length: 16 bits (13-bit size + 3-bit index) => 1 header
                0x00, 0x48, // AU-header: AU-size=9 + AU-index=0
                b'b', b'a', b'r',
            ])
            .unwrap(),
        )
        .unwrap();
        let e = d
            .pull(&ConnectionContext::dummy(), &StreamContext::dummy())
            .unwrap_err();
        let e_str = e.to_string();
        assert!(
            e_str.contains("mark can't be set on beginning of fragment"),
            "{}",
            e
        );
    }
}
