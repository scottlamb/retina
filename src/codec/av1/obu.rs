// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! AV1 Open Bitstream Unit helpers: OBU headers, leb128, the sequence header,
//! the av1C record, the RFC 6381 codec string and random-access detection.
//!
//! References:
//! - AV1 Bitstream & Decoding Process Specification (cited as "AV1 §x").
//! - AV1 Codec ISO Media File Format Binding (cited as "AV1-ISOBMFF §x").

use std::fmt;

/// OBU types (AV1 §6.2.2, obu_type).
pub const OBU_SEQUENCE_HEADER: u8 = 1;
pub const OBU_TEMPORAL_DELIMITER: u8 = 2;
pub const OBU_FRAME_HEADER: u8 = 3;
#[cfg(test)]
pub const OBU_TILE_GROUP: u8 = 4;
#[cfg(test)]
pub const OBU_METADATA: u8 = 5;
pub const OBU_FRAME: u8 = 6;
pub const OBU_TILE_LIST: u8 = 8;
pub const OBU_PADDING: u8 = 15;

/// frame_type KEY_FRAME (AV1 §6.8.2).
const KEY_FRAME: u32 = 0;

/// The largest value leb128() may return (AV1 §4.10.5: "less than or equal
/// to (1 << 32) - 1").
const LEB128_MAX: u64 = 0xFFFF_FFFF;

/// Bound on OBUs walked in one temporal unit by the helpers below. A TU from
/// the depacketizer is already bounded; this keeps the helpers safe on any
/// other input.
const MAX_OBUS_WALKED: usize = 65_536;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObuError {
    /// The input ended before the structure did.
    Truncated,
    /// obu_forbidden_bit was 1 (AV1 §6.2.2 requires 0).
    ForbiddenBit,
    /// A leb128 value used more than 8 bytes (AV1 §4.10.5).
    Leb128TooLong,
    /// A leb128 value exceeded (1 << 32) - 1 (AV1 §4.10.5).
    Leb128TooLarge,
    /// A Low Overhead Bitstream Format OBU had obu_has_size_field = 0
    /// (AV1 §5.2 / AV1-ISOBMFF §2.4 require it).
    MissingSizeField,
    /// obu_size did not match the bytes available for the OBU.
    SizeMismatch,
    /// The OBU handed to av1c_record was not a sequence header.
    NotSequenceHeader,
    /// seq_profile 3..7 are reserved (AV1 §6.4.1).
    ReservedProfile(u8),
    /// A sequence header field had a value the specification forbids.
    InvalidSequenceHeader(&'static str),
    /// More OBUs than the helper is willing to walk.
    TooManyObus,
}

impl fmt::Display for ObuError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ObuError::Truncated => write!(f, "AV1 OBU data truncated"),
            ObuError::ForbiddenBit => write!(f, "AV1 obu_forbidden_bit set"),
            ObuError::Leb128TooLong => write!(f, "AV1 leb128 longer than 8 bytes"),
            ObuError::Leb128TooLarge => write!(f, "AV1 leb128 value above 2^32-1"),
            ObuError::MissingSizeField => write!(f, "AV1 OBU without obu_size field"),
            ObuError::SizeMismatch => write!(f, "AV1 obu_size does not match the data"),
            ObuError::NotSequenceHeader => write!(f, "AV1 OBU is not a sequence header"),
            ObuError::ReservedProfile(p) => write!(f, "AV1 reserved seq_profile {p}"),
            ObuError::InvalidSequenceHeader(why) => {
                write!(f, "AV1 invalid sequence header: {why}")
            }
            ObuError::TooManyObus => write!(f, "AV1 temporal unit has too many OBUs"),
        }
    }
}

impl std::error::Error for ObuError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ObuHeader {
    pub obu_type: u8,
    pub has_extension: bool,
    pub has_size_field: bool,
    pub temporal_id: u8,
    pub spatial_id: u8,
    /// 1, or 2 with the extension header.
    pub header_len: usize,
}

/// Parse obu_header() and obu_extension_header() (AV1 §5.3.2, §5.3.3).
/// obu_reserved_1bit and extension_header_reserved_3bits are ignored, as
/// AV1 §6.2.2 tells decoders to do.
pub fn parse_obu_header(b: &[u8]) -> Result<ObuHeader, ObuError> {
    let (&first, rest) = b.split_first().ok_or(ObuError::Truncated)?;
    if first & 0x80 != 0 {
        return Err(ObuError::ForbiddenBit);
    }
    let obu_type = (first >> 3) & 0x0F;
    let has_extension = first & 0x04 != 0;
    let has_size_field = first & 0x02 != 0;
    let (temporal_id, spatial_id, header_len) = if has_extension {
        let &ext = rest.first().ok_or(ObuError::Truncated)?;
        ((ext >> 5) & 0x07, (ext >> 3) & 0x03, 2)
    } else {
        (0, 0, 1)
    };
    Ok(ObuHeader {
        obu_type,
        has_extension,
        has_size_field,
        temporal_id,
        spatial_id,
        header_len,
    })
}

/// leb128() (AV1 §4.10.5). Returns (value, bytes consumed). At most 8 bytes
/// are read; a value above (1 << 32) - 1 is refused, which also guarantees
/// the value fits in usize on every platform this code targets (32-bit and
/// up).
pub fn read_leb128(b: &[u8]) -> Result<(u64, usize), ObuError> {
    let mut value: u64 = 0;
    for (i, &byte) in b.iter().take(8).enumerate() {
        let shift = u32::try_from(i)
            .ok()
            .and_then(|i| i.checked_mul(7))
            .ok_or(ObuError::Leb128TooLong)?;
        let part = u64::from(byte & 0x7F)
            .checked_shl(shift)
            .ok_or(ObuError::Leb128TooLarge)?;
        value |= part;
        if value > LEB128_MAX {
            return Err(ObuError::Leb128TooLarge);
        }
        if byte & 0x80 == 0 {
            let used = i.checked_add(1).ok_or(ObuError::Leb128TooLong)?;
            return Ok((value, used));
        }
    }
    if b.len() >= 8 {
        Err(ObuError::Leb128TooLong)
    } else {
        Err(ObuError::Truncated)
    }
}

/// Read a leb128 and convert it to usize.
pub(crate) fn read_leb128_usize(b: &[u8]) -> Result<(usize, usize), ObuError> {
    let (v, n) = read_leb128(b)?;
    let v = usize::try_from(v).map_err(|_| ObuError::Leb128TooLarge)?;
    Ok((v, n))
}

/// Write the shortest leb128 encoding of `v` (AV1 §4.10.5). Values above
/// (1 << 32) - 1 are still encoded correctly (up to 10 bytes) but would be
/// refused by read_leb128; callers here only write OBU sizes, which are far
/// smaller.
pub fn write_leb128(v: u64, out: &mut Vec<u8>) {
    let mut v = v;
    loop {
        let low = (v & 0x7F) as u8;
        v = v.checked_shr(7).unwrap_or(0);
        if v == 0 {
            out.push(low);
            return;
        }
        out.push(low | 0x80);
    }
}

/// One OBU of a Low Overhead Bitstream Format buffer (every OBU carries its
/// size field).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Obu<'a> {
    pub header: ObuHeader,
    pub payload: &'a [u8],
    /// header + size field + payload.
    pub raw: &'a [u8],
}

/// Split one size-delimited OBU off the front of `b`.
fn next_obu(b: &[u8]) -> Result<(Obu<'_>, &[u8]), ObuError> {
    let header = parse_obu_header(b)?;
    if !header.has_size_field {
        return Err(ObuError::MissingSizeField);
    }
    let after_header = b.get(header.header_len..).ok_or(ObuError::Truncated)?;
    let (size, leb_len) = read_leb128_usize(after_header)?;
    let after_size = after_header.get(leb_len..).ok_or(ObuError::Truncated)?;
    let (payload, rest) = after_size
        .split_at_checked(size)
        .ok_or(ObuError::Truncated)?;
    let raw_len = header
        .header_len
        .checked_add(leb_len)
        .and_then(|n| n.checked_add(size))
        .ok_or(ObuError::Truncated)?;
    let raw = b.get(..raw_len).ok_or(ObuError::Truncated)?;
    Ok((
        Obu {
            header,
            payload,
            raw,
        },
        rest,
    ))
}

struct ObuIter<'a> {
    rest: &'a [u8],
    done: bool,
}

impl<'a> Iterator for ObuIter<'a> {
    type Item = Result<Obu<'a>, ObuError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done || self.rest.is_empty() {
            return None;
        }
        match next_obu(self.rest) {
            Ok((obu, rest)) => {
                self.rest = rest;
                Some(Ok(obu))
            }
            Err(e) => {
                self.done = true;
                Some(Err(e))
            }
        }
    }
}

/// Iterate the OBUs of a Low Overhead Bitstream Format buffer (AV1 §5.2).
/// Stops after the first error.
pub fn iter_obus(tu: &[u8]) -> impl Iterator<Item = Result<Obu<'_>, ObuError>> {
    ObuIter {
        rest: tu,
        done: false,
    }
}

/// MSB-first bit reader for the f(n) and uvlc() descriptors (AV1 §4.10).
struct BitReader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> BitReader<'a> {
    fn new(data: &'a [u8]) -> Self {
        BitReader { data, pos: 0 }
    }

    fn bit(&mut self) -> Result<u32, ObuError> {
        let byte = *self.data.get(self.pos >> 3).ok_or(ObuError::Truncated)?;
        let shift = 7u32.wrapping_sub((self.pos & 7) as u32);
        self.pos = self.pos.checked_add(1).ok_or(ObuError::Truncated)?;
        Ok(u32::from(byte.checked_shr(shift).unwrap_or(0) & 1))
    }

    fn flag(&mut self) -> Result<bool, ObuError> {
        Ok(self.bit()? == 1)
    }

    /// f(n), n <= 32.
    fn f(&mut self, n: u32) -> Result<u32, ObuError> {
        let mut v: u32 = 0;
        for _ in 0..n.min(32) {
            v = v.checked_shl(1).unwrap_or(0) | self.bit()?;
        }
        Ok(v)
    }

    fn f8(&mut self, n: u32) -> Result<u8, ObuError> {
        u8::try_from(self.f(n.min(8))?).map_err(|_| ObuError::Truncated)
    }

    /// uvlc() (AV1 §4.10.3). 32 or more leading zeros decode to 2^32-1.
    fn uvlc(&mut self) -> Result<u32, ObuError> {
        let mut leading_zeros: u32 = 0;
        loop {
            if self.flag()? {
                break;
            }
            leading_zeros = leading_zeros.saturating_add(1);
            if leading_zeros > 64 {
                return Err(ObuError::InvalidSequenceHeader("uvlc too long"));
            }
        }
        if leading_zeros >= 32 {
            return Ok(u32::MAX);
        }
        let value = self.f(leading_zeros)?;
        let base = 1u32
            .checked_shl(leading_zeros)
            .map(|b| b.wrapping_sub(1))
            .unwrap_or(u32::MAX);
        Ok(value.saturating_add(base))
    }
}

/// The sequence header fields a CMAF writer and the frame header parse need
/// (AV1 §5.5, semantics §6.4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Av1SequenceInfo {
    pub seq_profile: u8,
    pub still_picture: bool,
    pub reduced_still_picture_header: bool,
    pub seq_level_idx_0: u8,
    pub seq_tier_0: u8,
    pub max_frame_width: u32,
    pub max_frame_height: u32,
    pub high_bitdepth: bool,
    pub twelve_bit: bool,
    pub mono_chrome: bool,
    pub chroma_subsampling_x: bool,
    pub chroma_subsampling_y: bool,
    pub chroma_sample_position: u8,
    pub initial_display_delay_present: bool,
    pub initial_display_delay_minus_one_0: Option<u8>,
    pub color_description_present: bool,
    pub color_primaries: u8,
    pub transfer_characteristics: u8,
    pub matrix_coefficients: u8,
    pub color_range: bool,
    pub frame_id_numbers_present: bool,
    pub equal_picture_interval: bool,
    pub additional_frame_id_length_minus_one: u8,
    pub delta_frame_id_length_minus_two: u8,
    pub decoder_model_info_present: bool,
    pub frame_width_bits_minus_1: u8,
    pub frame_height_bits_minus_1: u8,
    pub order_hint_bits: u8,
    pub enable_order_hint: bool,
    pub seq_force_screen_content_tools: u8,
    pub seq_force_integer_mv: u8,
    pub film_grain_params_present: bool,
    pub timing_info_present: bool,
    pub operating_points_cnt_minus_1: u8,
    pub operating_point_idc_0: u16,
    pub use_128x128_superblock: bool,
    pub enable_superres: bool,
    pub enable_cdef: bool,
    pub enable_restoration: bool,
    /// BitDepth (AV1 §6.4.2): 8, 10 or 12.
    pub bit_depth: u8,
}

/// SELECT_SCREEN_CONTENT_TOOLS / SELECT_INTEGER_MV (AV1 §6.4.1).
const SELECT: u8 = 2;
/// CP_BT_709, TC_SRGB, MC_IDENTITY, *_UNSPECIFIED (AV1 §6.4.2).
const CP_BT_709: u8 = 1;
const TC_SRGB: u8 = 13;
const MC_IDENTITY: u8 = 0;
const UNSPECIFIED: u8 = 2;

/// sequence_header_obu() (AV1 §5.5.1) through color_config() and
/// film_grain_params_present. `payload` is the OBU payload (after the header
/// and size field). Trailing bits are not checked: a CMAF writer stores the
/// OBU as received.
pub fn parse_sequence_header(payload: &[u8]) -> Result<Av1SequenceInfo, ObuError> {
    let mut r = BitReader::new(payload);
    let seq_profile = r.f8(3)?;
    if seq_profile > 2 {
        return Err(ObuError::ReservedProfile(seq_profile));
    }
    let still_picture = r.flag()?;
    let reduced_still_picture_header = r.flag()?;
    if reduced_still_picture_header && !still_picture {
        // AV1 §6.4.1: reduced_still_picture_header may be 1 only when
        // still_picture is 1.
        return Err(ObuError::InvalidSequenceHeader(
            "reduced_still_picture_header without still_picture",
        ));
    }

    let mut timing_info_present = false;
    let mut decoder_model_info_present = false;
    let mut equal_picture_interval = false;
    let mut initial_display_delay_present = false;
    let mut initial_display_delay_minus_one_0 = None;
    let mut operating_points_cnt_minus_1 = 0u8;
    let mut operating_point_idc_0 = 0u16;
    let seq_level_idx_0;
    let mut seq_tier_0 = 0u8;

    if reduced_still_picture_header {
        seq_level_idx_0 = r.f8(5)?;
    } else {
        timing_info_present = r.flag()?;
        let mut buffer_delay_length_minus_1 = 0u32;
        if timing_info_present {
            // timing_info() (AV1 §5.5.3).
            let _num_units_in_display_tick = r.f(32)?;
            let _time_scale = r.f(32)?;
            equal_picture_interval = r.flag()?;
            if equal_picture_interval {
                let _num_ticks_per_picture_minus_1 = r.uvlc()?;
            }
            decoder_model_info_present = r.flag()?;
            if decoder_model_info_present {
                // decoder_model_info() (AV1 §5.5.4).
                buffer_delay_length_minus_1 = r.f(5)?;
                let _num_units_in_decoding_tick = r.f(32)?;
                let _buffer_removal_time_length_minus_1 = r.f(5)?;
                let _frame_presentation_time_length_minus_1 = r.f(5)?;
            }
        }
        initial_display_delay_present = r.flag()?;
        operating_points_cnt_minus_1 = r.f8(5)?;
        let mut level0 = 0u8;
        for i in 0..=operating_points_cnt_minus_1 {
            let idc = r.f(12)?;
            let level = r.f8(5)?;
            let tier = if level > 7 { r.f8(1)? } else { 0 };
            if decoder_model_info_present {
                let decoder_model_present_for_this_op = r.flag()?;
                if decoder_model_present_for_this_op {
                    // operating_parameters_info() (AV1 §5.5.5).
                    let n = buffer_delay_length_minus_1.saturating_add(1);
                    let _decoder_buffer_delay = r.f(n)?;
                    let _encoder_buffer_delay = r.f(n)?;
                    let _low_delay_mode_flag = r.flag()?;
                }
            }
            let mut idd = None;
            if initial_display_delay_present {
                let present_for_this_op = r.flag()?;
                if present_for_this_op {
                    idd = Some(r.f8(4)?);
                }
            }
            if i == 0 {
                operating_point_idc_0 = u16::try_from(idc).map_err(|_| ObuError::Truncated)?;
                level0 = level;
                seq_tier_0 = tier;
                initial_display_delay_minus_one_0 = idd;
            }
        }
        seq_level_idx_0 = level0;
    }

    let frame_width_bits_minus_1 = r.f8(4)?;
    let frame_height_bits_minus_1 = r.f8(4)?;
    let max_frame_width = r
        .f(u32::from(frame_width_bits_minus_1).saturating_add(1))?
        .checked_add(1)
        .ok_or(ObuError::InvalidSequenceHeader("max_frame_width"))?;
    let max_frame_height = r
        .f(u32::from(frame_height_bits_minus_1).saturating_add(1))?
        .checked_add(1)
        .ok_or(ObuError::InvalidSequenceHeader("max_frame_height"))?;

    let mut frame_id_numbers_present = false;
    let mut delta_frame_id_length_minus_two = 0u8;
    let mut additional_frame_id_length_minus_one = 0u8;
    if !reduced_still_picture_header {
        frame_id_numbers_present = r.flag()?;
    }
    if frame_id_numbers_present {
        delta_frame_id_length_minus_two = r.f8(4)?;
        additional_frame_id_length_minus_one = r.f8(3)?;
    }
    let use_128x128_superblock = r.flag()?;
    let _enable_filter_intra = r.flag()?;
    let _enable_intra_edge_filter = r.flag()?;

    let mut enable_order_hint = false;
    let mut order_hint_bits = 0u8;
    let mut seq_force_screen_content_tools = SELECT;
    let mut seq_force_integer_mv = SELECT;
    if !reduced_still_picture_header {
        let _enable_interintra_compound = r.flag()?;
        let _enable_masked_compound = r.flag()?;
        let _enable_warped_motion = r.flag()?;
        let _enable_dual_filter = r.flag()?;
        enable_order_hint = r.flag()?;
        if enable_order_hint {
            let _enable_jnt_comp = r.flag()?;
            let _enable_ref_frame_mvs = r.flag()?;
        }
        let seq_choose_screen_content_tools = r.flag()?;
        seq_force_screen_content_tools = if seq_choose_screen_content_tools {
            SELECT
        } else {
            r.f8(1)?
        };
        seq_force_integer_mv = if seq_force_screen_content_tools > 0 {
            let seq_choose_integer_mv = r.flag()?;
            if seq_choose_integer_mv {
                SELECT
            } else {
                r.f8(1)?
            }
        } else {
            SELECT
        };
        if enable_order_hint {
            order_hint_bits = r.f8(3)?.saturating_add(1);
        }
    }
    let enable_superres = r.flag()?;
    let enable_cdef = r.flag()?;
    let enable_restoration = r.flag()?;

    // color_config() (AV1 §5.5.2).
    let high_bitdepth = r.flag()?;
    let mut twelve_bit = false;
    let bit_depth = if seq_profile == 2 && high_bitdepth {
        twelve_bit = r.flag()?;
        if twelve_bit { 12 } else { 10 }
    } else if high_bitdepth {
        10
    } else {
        8
    };
    let mono_chrome = if seq_profile == 1 { false } else { r.flag()? };
    let color_description_present = r.flag()?;
    let (color_primaries, transfer_characteristics, matrix_coefficients) =
        if color_description_present {
            (r.f8(8)?, r.f8(8)?, r.f8(8)?)
        } else {
            (UNSPECIFIED, UNSPECIFIED, UNSPECIFIED)
        };
    let color_range;
    let mut chroma_subsampling_x = true;
    let mut chroma_subsampling_y = true;
    let mut chroma_sample_position = 0u8;
    if mono_chrome {
        color_range = r.flag()?;
    } else if color_primaries == CP_BT_709
        && transfer_characteristics == TC_SRGB
        && matrix_coefficients == MC_IDENTITY
    {
        color_range = true;
        chroma_subsampling_x = false;
        chroma_subsampling_y = false;
        if seq_profile != 1 && !(seq_profile == 2 && bit_depth == 12) {
            // AV1 §6.4.2: sRGB 4:4:4 needs profile 1, or profile 2 at 12 bit.
            return Err(ObuError::InvalidSequenceHeader("sRGB in a 4:2:0 profile"));
        }
    } else {
        color_range = r.flag()?;
        match seq_profile {
            0 => {}
            1 => {
                chroma_subsampling_x = false;
                chroma_subsampling_y = false;
            }
            _ => {
                if bit_depth == 12 {
                    chroma_subsampling_x = r.flag()?;
                    chroma_subsampling_y = if chroma_subsampling_x {
                        r.flag()?
                    } else {
                        false
                    };
                } else {
                    chroma_subsampling_y = false;
                }
            }
        }
        if chroma_subsampling_x && chroma_subsampling_y {
            chroma_sample_position = r.f8(2)?;
        }
    }
    if !mono_chrome {
        let _separate_uv_delta_q = r.flag()?;
    }
    let film_grain_params_present = r.flag()?;

    Ok(Av1SequenceInfo {
        seq_profile,
        still_picture,
        reduced_still_picture_header,
        seq_level_idx_0,
        seq_tier_0,
        max_frame_width,
        max_frame_height,
        high_bitdepth,
        twelve_bit,
        mono_chrome,
        chroma_subsampling_x,
        chroma_subsampling_y,
        chroma_sample_position,
        initial_display_delay_present,
        initial_display_delay_minus_one_0,
        color_description_present,
        color_primaries,
        transfer_characteristics,
        matrix_coefficients,
        color_range,
        frame_id_numbers_present,
        equal_picture_interval,
        additional_frame_id_length_minus_one,
        delta_frame_id_length_minus_two,
        decoder_model_info_present,
        frame_width_bits_minus_1,
        frame_height_bits_minus_1,
        order_hint_bits,
        enable_order_hint,
        seq_force_screen_content_tools,
        seq_force_integer_mv,
        film_grain_params_present,
        timing_info_present,
        operating_points_cnt_minus_1,
        operating_point_idc_0,
        use_128x128_superblock,
        enable_superres,
        enable_cdef,
        enable_restoration,
        bit_depth,
    })
}

/// Split an OBU that may or may not carry obu_size into (header, payload).
/// When obu_size is present it must cover the rest of `obu` exactly.
pub(crate) fn split_obu_any(obu: &[u8]) -> Result<(ObuHeader, &[u8], &[u8]), ObuError> {
    let header = parse_obu_header(obu)?;
    let (hdr_bytes, after_header) = obu
        .split_at_checked(header.header_len)
        .ok_or(ObuError::Truncated)?;
    let payload = if header.has_size_field {
        let (size, leb_len) = read_leb128_usize(after_header)?;
        let p = after_header.get(leb_len..).ok_or(ObuError::Truncated)?;
        if p.len() != size {
            return Err(ObuError::SizeMismatch);
        }
        p
    } else {
        after_header
    };
    Ok((header, hdr_bytes, payload))
}

/// Append `header` bytes (with obu_has_size_field forced to 1), obu_size and
/// `payload`: the Low Overhead Bitstream Format form (AV1 §5.2).
pub(crate) fn write_obu_with_size(hdr_bytes: &[u8], payload: &[u8], out: &mut Vec<u8>) {
    let mut iter = hdr_bytes.iter();
    if let Some(&first) = iter.next() {
        out.push(first | 0x02);
    }
    out.extend(iter);
    write_leb128(payload.len() as u64, out);
    out.extend_from_slice(payload);
}

/// The av1C box body: AV1CodecConfigurationRecord (AV1-ISOBMFF §2.3.3) with
/// the sequence header OBU as configOBUs, rewritten with obu_has_size_field
/// = 1 (AV1-ISOBMFF §2.3.4).
///
/// initial_presentation_delay_present is written as 0: that field counts
/// samples of the ISOBMFF track, which the sequence header's
/// initial_display_delay does not give, and AV1-ISOBMFF §2.3.4 makes it
/// optional. This matches ffmpeg and GStreamer's isofmp4mux.
pub fn av1c_record(
    sequence_header_obu: &[u8],
    info: &Av1SequenceInfo,
) -> Result<Vec<u8>, ObuError> {
    let (header, hdr_bytes, payload) = split_obu_any(sequence_header_obu)?;
    if header.obu_type != OBU_SEQUENCE_HEADER {
        return Err(ObuError::NotSequenceHeader);
    }
    let b = |v: bool, shift: u32| -> u8 { u8::from(v).checked_shl(shift).unwrap_or(0) };
    let mut out = Vec::with_capacity(payload.len().saturating_add(10));
    // marker = 1, version = 1.
    out.push(0x81);
    out.push(((info.seq_profile & 0x07) << 5) | (info.seq_level_idx_0 & 0x1F));
    out.push(
        b(info.seq_tier_0 != 0, 7)
            | b(info.high_bitdepth, 6)
            | b(info.twelve_bit, 5)
            | b(info.mono_chrome, 4)
            | b(info.chroma_subsampling_x, 3)
            | b(info.chroma_subsampling_y, 2)
            | (info.chroma_sample_position & 0x03),
    );
    // reserved = 0, initial_presentation_delay_present = 0, reserved = 0.
    out.push(0);
    write_obu_with_size(hdr_bytes, payload, &mut out);
    Ok(out)
}

/// RFC 6381 codec string (AV1-ISOBMFF §5, "Codecs Parameter String").
///
/// The short form `av01.P.LLT.DD` is written when the optional fields all
/// hold what the short form implies: no colour description in the sequence
/// header, 4:2:0 with chroma_sample_position 0, not monochrome, limited
/// range. Otherwise the long form is written with the values the sequence
/// header gives, using 2 (unspecified) for the colour fields when it carries
/// no colour description. GStreamer instead fills the colour fields from its
/// caps colorimetry, so its long form can differ from ours in those fields
/// only.
pub fn codec_string(info: &Av1SequenceInfo) -> String {
    let tier = if info.seq_tier_0 != 0 { 'H' } else { 'M' };
    let mut s = format!(
        "av01.{}.{:02}{}.{:02}",
        info.seq_profile, info.seq_level_idx_0, tier, info.bit_depth
    );
    let default_chroma = !info.mono_chrome
        && info.chroma_subsampling_x
        && info.chroma_subsampling_y
        && info.chroma_sample_position == 0;
    if info.color_description_present || !default_chroma || info.color_range {
        s.push_str(&format!(
            ".{}.{}{}{}.{:02}.{:02}.{:02}.{}",
            u8::from(info.mono_chrome),
            u8::from(info.chroma_subsampling_x),
            u8::from(info.chroma_subsampling_y),
            info.chroma_sample_position,
            info.color_primaries,
            info.transfer_characteristics,
            info.matrix_coefficients,
            u8::from(info.color_range),
        ));
    }
    s
}

/// What the start of a frame header says (AV1 §5.9.2, uncompressed_header()
/// up to show_frame).
struct FrameStart {
    show_existing_frame: bool,
    frame_type: u32,
    show_frame: bool,
}

fn parse_frame_start(payload: &[u8], seq: &Av1SequenceInfo) -> Result<FrameStart, ObuError> {
    if seq.reduced_still_picture_header {
        // AV1 §5.9.2: a reduced still picture header implies a shown key
        // frame and reads no bits here.
        return Ok(FrameStart {
            show_existing_frame: false,
            frame_type: KEY_FRAME,
            show_frame: true,
        });
    }
    let mut r = BitReader::new(payload);
    let show_existing_frame = r.flag()?;
    if show_existing_frame {
        return Ok(FrameStart {
            show_existing_frame,
            frame_type: 0,
            show_frame: true,
        });
    }
    let frame_type = r.f(2)?;
    let show_frame = r.flag()?;
    Ok(FrameStart {
        show_existing_frame,
        frame_type,
        show_frame,
    })
}

/// True when this temporal unit can start decoding (AV1-ISOBMFF §2.4, sync
/// sample): a sequence header OBU comes before the first frame header, and
/// that first frame (OBU_FRAME or OBU_FRAME_HEADER) is a shown KEY_FRAME
/// with show_existing_frame = 0. `tu` is Low Overhead Bitstream Format.
pub fn is_random_access(tu: &[u8]) -> Result<bool, ObuError> {
    let mut seq: Option<Av1SequenceInfo> = None;
    for (n, obu) in iter_obus(tu).enumerate() {
        if n >= MAX_OBUS_WALKED {
            return Err(ObuError::TooManyObus);
        }
        let obu = obu?;
        match obu.header.obu_type {
            OBU_SEQUENCE_HEADER => seq = Some(parse_sequence_header(obu.payload)?),
            OBU_FRAME | OBU_FRAME_HEADER => {
                let Some(seq) = seq.as_ref() else {
                    return Ok(false);
                };
                let f = parse_frame_start(obu.payload, seq)?;
                return Ok(!f.show_existing_frame && f.frame_type == KEY_FRAME && f.show_frame);
            }
            _ => {}
        }
    }
    Ok(false)
}

/// The sequence header OBU (raw, with size field) inside a TU, if any.
pub fn find_sequence_header(tu: &[u8]) -> Result<Option<&[u8]>, ObuError> {
    for (n, obu) in iter_obus(tu).enumerate() {
        if n >= MAX_OBUS_WALKED {
            return Err(ObuError::TooManyObus);
        }
        let obu = obu?;
        if obu.header.obu_type == OBU_SEQUENCE_HEADER {
            return Ok(Some(obu.raw));
        }
    }
    Ok(None)
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::panic,
    clippy::arithmetic_side_effects
)]
mod tests {
    use super::*;

    #[test]
    fn leb128_round_trip_and_bounds() {
        for v in [0u64, 1, 127, 128, 300, 16_383, 16_384, 0xFFFF_FFFF] {
            let mut out = Vec::new();
            write_leb128(v, &mut out);
            assert_eq!(read_leb128(&out).unwrap(), (v, out.len()), "{v}");
        }
        // Non-minimal encodings are legal (AV1 §4.10.5).
        assert_eq!(read_leb128(&[0x81, 0x80, 0x00]).unwrap(), (1, 3));
        // Eight bytes all with continuation: too long.
        assert_eq!(read_leb128(&[0x80; 9]), Err(ObuError::Leb128TooLong));
        assert_eq!(read_leb128(&[0x80; 8]), Err(ObuError::Leb128TooLong));
        // Above 2^32 - 1.
        assert_eq!(
            read_leb128(&[0x80, 0x80, 0x80, 0x80, 0x10]),
            Err(ObuError::Leb128TooLarge)
        );
        assert_eq!(read_leb128(&[0x80]), Err(ObuError::Truncated));
        assert_eq!(read_leb128(&[]), Err(ObuError::Truncated));
    }

    #[test]
    fn obu_header_fields() {
        let h = parse_obu_header(&[0x0A]).unwrap();
        assert_eq!(
            (h.obu_type, h.has_extension, h.has_size_field, h.header_len),
            (OBU_SEQUENCE_HEADER, false, true, 1)
        );
        let h = parse_obu_header(&[0x34, 0b1101_0000]).unwrap();
        assert_eq!(
            (h.obu_type, h.temporal_id, h.spatial_id, h.header_len),
            (6, 6, 2, 2)
        );
        assert_eq!(parse_obu_header(&[0x34]), Err(ObuError::Truncated));
        assert_eq!(parse_obu_header(&[0x80]), Err(ObuError::ForbiddenBit));
    }

    #[test]
    fn iter_obus_requires_size_and_stops_at_error() {
        let buf = [0x12, 0x00, 0x32, 0x02, 0xAA, 0xBB, 0x30, 0x01];
        let v: Vec<_> = iter_obus(&buf).collect();
        assert_eq!(v.len(), 3);
        assert_eq!(
            v[0].as_ref().unwrap().header.obu_type,
            OBU_TEMPORAL_DELIMITER
        );
        assert_eq!(v[1].as_ref().unwrap().payload, &[0xAA, 0xBB]);
        assert_eq!(v[1].as_ref().unwrap().raw, &buf[2..6]);
        assert_eq!(v[2], Err(ObuError::MissingSizeField));
        let short = [0x32, 0x05, 0x01];
        assert_eq!(iter_obus(&short).next(), Some(Err(ObuError::Truncated)));
    }

    /// A reduced still picture header: profile 0, level 2.0 (idx 0),
    /// 16x16, 8-bit 4:2:0, no colour description.
    fn reduced_still_seq() -> Vec<u8> {
        // seq_profile=000 still=1 reduced=1 seq_level_idx=00000
        // fwb-1=0011 fhb-1=0011 w-1=1111 h-1=1111
        // sb128=0 filter_intra=0 edge=0 superres=0 cdef=0 restoration=0
        // high_bitdepth=0 mono=0 color_desc=0 color_range=0 csp=00
        // separate_uv=0 film_grain=0, then trailing bit.
        let bits = [
            "000", "1", "1", "00000", "0011", "0011", "1111", "1111", "000", "000", "0", "0", "0",
            "0", "00", "0", "0", "1",
        ]
        .concat();
        let mut out = Vec::new();
        for chunk in bits.as_bytes().chunks(8) {
            let mut b = 0u8;
            for (i, c) in chunk.iter().enumerate() {
                if *c == b'1' {
                    b |= 0x80 >> i;
                }
            }
            out.push(b);
        }
        out
    }

    #[test]
    fn reduced_still_picture_sequence_header() {
        let info = parse_sequence_header(&reduced_still_seq()).unwrap();
        assert!(info.still_picture && info.reduced_still_picture_header);
        assert_eq!((info.max_frame_width, info.max_frame_height), (16, 16));
        assert_eq!(info.bit_depth, 8);
        assert!(info.chroma_subsampling_x && info.chroma_subsampling_y);
        assert_eq!(codec_string(&info), "av01.0.00M.08");

        // A TU of that sequence header and any frame header is a sync sample
        // without reading frame header bits (AV1 §5.9.2).
        let mut tu = Vec::new();
        write_obu_with_size(&[OBU_SEQUENCE_HEADER << 3], &reduced_still_seq(), &mut tu);
        write_obu_with_size(&[OBU_FRAME << 3], &[0x00], &mut tu);
        assert!(is_random_access(&tu).unwrap());
        assert!(find_sequence_header(&tu).unwrap().is_some());

        let rec = av1c_record(
            &tu[..find_sequence_header(&tu).unwrap().unwrap().len()],
            &info,
        )
        .unwrap();
        assert_eq!(&rec[..4], &[0x81, 0x00, 0x0C, 0x00]);
        assert_eq!(&rec[4..], find_sequence_header(&tu).unwrap().unwrap());
    }

    #[test]
    fn random_access_needs_sequence_header_first() {
        let seq = reduced_still_seq();
        let mut tu = Vec::new();
        write_obu_with_size(&[OBU_FRAME << 3], &[0x00], &mut tu);
        write_obu_with_size(&[OBU_SEQUENCE_HEADER << 3], &seq, &mut tu);
        assert!(!is_random_access(&tu).unwrap());
        assert!(!is_random_access(&[]).unwrap());
    }

    #[test]
    fn reserved_profile_and_truncation() {
        assert_eq!(
            parse_sequence_header(&[0xE0]),
            Err(ObuError::ReservedProfile(7))
        );
        assert_eq!(parse_sequence_header(&[0x00]), Err(ObuError::Truncated));
        assert_eq!(parse_sequence_header(&[]), Err(ObuError::Truncated));
    }

    #[test]
    fn av1c_refuses_other_obus() {
        let info = parse_sequence_header(&reduced_still_seq()).unwrap();
        assert_eq!(
            av1c_record(&[OBU_FRAME << 3, 0], &info),
            Err(ObuError::NotSequenceHeader)
        );
    }

    #[test]
    fn codec_string_long_form() {
        let mut info = parse_sequence_header(&reduced_still_seq()).unwrap();
        info.color_description_present = true;
        info.color_primaries = 9;
        info.transfer_characteristics = 16;
        info.matrix_coefficients = 9;
        info.color_range = true;
        info.seq_tier_0 = 1;
        info.seq_level_idx_0 = 12;
        info.bit_depth = 10;
        assert_eq!(codec_string(&info), "av01.0.12H.10.0.110.09.16.09.1");
    }
}
