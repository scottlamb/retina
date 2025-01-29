// Copyright (C) 2024 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! H.265 NAL unit parsing.
//!
//! This is an internal module, `pub` only for the benefit of fuzz testing.
//!
//! Relevant specifications:
//!
//! * [ITU-T H.265 "High efficiency video coding"](https://www.itu.int/rec/T-REC-H.265) is the
//!   main H.265 specification, including all the RBSP layouts described here.
//! * [ISO/IEC 14496-15 "Carriage of network abstraction layer (NAL) unit structured video in the ISO base media file format"](https://www.iso.org/standard/68933.html)
//!   defines the format of the RFC 6381 codec ID.  I have been unable to
//!   find a legal, free copy of the finalized document. However, I believe the relevant parts are
//!   unchanged since [this working draft](https://mpeg.chiariglione.org/standards/mpeg-4/carriage-nal-unit-structured-video-iso-base-media-file-format/wd-isoiec-14496).

use h264_reader::rbsp::{BitRead, BitReaderError};

/// Whether a unit type is VCL or non-VCL, as defined in T.REC H.265 Table 7-1.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum UnitTypeClass {
    Vcl { intra_coded: bool },
    NonVcl,
}

/// NAL unit type, as in T.REC H.265 Table 7-1.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[repr(u8)]
pub enum UnitType {
    TrailN = 0,
    TrailR = 1,
    TsaN = 2,
    TsaR = 3,
    StsaN = 4,
    StsaR = 5,
    RadlN = 6,
    RadlR = 7,
    RaslN = 8,
    RaslR = 9,
    RsvVclN10 = 10,
    RsvVclR11 = 11,
    RsvVclN12 = 12,
    RsvVclR13 = 13,
    RsvVclN14 = 14,
    RsvVclR15 = 15,
    BlaWLp = 16,
    BlaWRadl = 17,
    BlaNLp = 18,
    IdrWRadl = 19,
    IdrNLp = 20,
    CraNut = 21,
    RsvIrapVcl22 = 22,
    RsvIrapVcl23 = 23,
    RsvVcl24 = 24,
    RsvVcl25 = 25,
    RsvVcl26 = 26,
    RsvVcl27 = 27,
    RsvVcl28 = 28,
    RsvVcl29 = 29,
    RsvVcl30 = 30,
    RsvVcl31 = 31,
    VpsNut = 32,
    SpsNut = 33,
    PpsNut = 34,

    /// Access unit delimiter.
    AudNut = 35,

    /// End of sequence.
    EosNut = 36,

    /// End of bitstream.
    EobNut = 37,
    FdNut = 38,
    PrefixSeiNut = 39,
    SuffixSeiNut = 40,
    RsvNvcl41 = 41,
    RsvNvcl42 = 42,
    RsvNvcl43 = 43,
    RsvNvcl44 = 44,
    RsvNvcl45 = 45,
    RsvNvcl46 = 46,
    RsvNvcl47 = 47,
    Unspec48 = 48,
    Unspec49 = 49,
    Unspec50 = 50,
    Unspec51 = 51,
    Unspec52 = 52,
    Unspec53 = 53,
    Unspec54 = 54,
    Unspec55 = 55,
    Unspec56 = 56,
    Unspec57 = 57,
    Unspec58 = 58,
    Unspec59 = 59,
    Unspec60 = 60,
    Unspec61 = 61,
    Unspec62 = 62,
    Unspec63 = 63,
}

impl UnitType {
    pub fn unit_type_class(self) -> UnitTypeClass {
        match self {
            UnitType::TrailN
            | UnitType::TrailR
            | UnitType::TsaN
            | UnitType::TsaR
            | UnitType::StsaN
            | UnitType::StsaR
            | UnitType::RadlN
            | UnitType::RadlR
            | UnitType::RaslN
            | UnitType::RaslR
            | UnitType::RsvVclN10
            | UnitType::RsvVclR11
            | UnitType::RsvVclN12
            | UnitType::RsvVclR13
            | UnitType::RsvVclN14
            | UnitType::RsvVclR15
            | UnitType::BlaWLp
            | UnitType::BlaWRadl
            | UnitType::BlaNLp
            | UnitType::CraNut
            | UnitType::RsvIrapVcl22
            | UnitType::RsvIrapVcl23
            | UnitType::RsvVcl24
            | UnitType::RsvVcl25
            | UnitType::RsvVcl26
            | UnitType::RsvVcl27
            | UnitType::RsvVcl28
            | UnitType::RsvVcl29
            | UnitType::RsvVcl30
            | UnitType::RsvVcl31 => UnitTypeClass::Vcl { intra_coded: false },
            UnitType::IdrWRadl | UnitType::IdrNLp => UnitTypeClass::Vcl { intra_coded: true },
            _ => UnitTypeClass::NonVcl,
        }
    }
}

impl TryFrom<u8> for UnitType {
    type Error = Error;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value > 63 {
            return Err(Error(format!("NAL 0x{:02X} is out of range", value)));
        }

        // SAFETY: `UnitType` is `repr(u8)` and C-like; `value` is in range.
        Ok(unsafe { std::mem::transmute::<u8, UnitType>(value) })
    }
}

impl From<UnitType> for u8 {
    fn from(t: UnitType) -> u8 {
        // SAFETY: `UnitType` is `repr(u8)` and C-like.
        unsafe { std::mem::transmute(t) }
    }
}

/// `nal_unit_header` as in T.REC H.265 section 7.3.1.2.
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Header([u8; 2]);

impl std::fmt::Debug for Header {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Header")
            .field("unit_type", &self.unit_type())
            .field("nuh_layer_id", &self.nuh_layer_id())
            .field("nuh_temporal_id_plus1", &self.nuh_temporal_id_plus1())
            .finish()
    }
}

impl TryFrom<[u8; 2]> for Header {
    type Error = Error;

    fn try_from(value: [u8; 2]) -> Result<Self, Self::Error> {
        if (value[0] & 0b1000_0000) != 0 {
            return Err(Error(format!(
                "forbidden zero bit is set in NAL header 0x{:02X}{:02X}",
                value[0], value[1]
            )));
        }
        if (value[1] & 0b111) == 0 {
            return Err(Error(format!(
                "zero temporal_id_plus1 in NAL header 0x{:02X}{:02X}",
                value[0], value[1]
            )));
        }
        Ok(Self(value))
    }
}

impl std::ops::Deref for Header {
    type Target = [u8; 2];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Header {
    /// Returns a new header of the given unit type.
    pub fn with_unit_type(self, t: UnitType) -> Self {
        let mut out = self.0;
        out[0] = (out[0] & 0b1000_0001) | (u8::from(t) << 1);
        Self(out)
    }

    /// The NAL unit type.
    pub fn unit_type(self) -> UnitType {
        UnitType::try_from(self.0[0] >> 1).expect("6-bit value must be valid NAL type")
    }

    /// The `nul_layer_id`, as a 6-bit value.
    pub fn nuh_layer_id(self) -> u8 {
        (self.0[0] & 0b1) << 5 | (self.0[1] >> 3)
    }

    /// The `num_temporal_id_plus1`, as a non-zero 3-bit value.
    pub fn nuh_temporal_id_plus1(self) -> u8 {
        self.0[1] & 0b111
    }
}

/// Splits a NAL unit into the header and a `BitReader` that can be used with
/// the respective NAL type's `from_bits` method.
pub fn split(nal: &[u8]) -> Result<(Header, impl BitRead + '_), Error> {
    let Some((hdr_bytes, rest)) = nal.split_first_chunk::<2>() else {
        return Err(Error("NAL unit too short".to_owned()));
    };
    let header = Header::try_from(*hdr_bytes)?;
    let bytes = h264_reader::rbsp::ByteReader::without_skip(rest);
    let bits = h264_reader::rbsp::BitReader::new(bytes);
    Ok((header, bits))
}

#[derive(Debug)]
pub struct Error(pub(crate) String);

impl From<BitReaderError> for Error {
    fn from(e: BitReaderError) -> Self {
        Error(format!("{:?}", e))
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for Error {}

// T.REC H.265 section 7.3.2.2
#[derive(Debug)]
pub struct Sps {
    sps_max_sub_layers_minus1: u8,
    sps_temporal_id_nesting_flag: bool,
    profile_tier_level: ProfileTierLevel,
    chroma_format_idc: u8,
    pic_width_in_luma_samples: u32,
    pic_height_in_luma_samples: u32,
    conformance_window: Option<ConformanceWindow>,
    bit_depth_luma_minus8: u8,
    bit_depth_chroma_minus8: u8,
    vui: Option<VuiParameters>,
}

impl Sps {
    pub fn from_bits<R: BitRead>(mut r: R) -> Result<Self, Error> {
        // See T.REC H.265 section 7.3.2.2.1, seq_parameter_set_rbsp.
        r.skip(4, "sps_video_parameter_set_id")?;
        let sps_max_sub_layers_minus1: u8 = r.read(3, "sps_max_sub_layers_minus1")?;
        if sps_max_sub_layers_minus1 > 6 {
            return Err(Error(
                "sps_max_sub_layers_minus1 must be in [0, 6]".to_owned(),
            ));
        }
        let sps_temporal_id_nesting_flag = r.read_bool("sps_temporal_id_nesting_flag")?;
        let profile_tier_level =
            ProfileTierLevel::from_bits(&mut r, true, sps_max_sub_layers_minus1)?;
        let _ = r.read_ue("sps_seq_parameter_set_id")?;
        let chroma_format_idc = r.read_ue("chroma_format_idc")?;
        if chroma_format_idc > 3 {
            return Err(Error("chroma_format_idc must be in [0, 3]".to_owned()));
        }
        let chroma_format_idc = chroma_format_idc as u8;
        let _ = chroma_format_idc == 3 && r.read_bool("separate_colour_plane_flag")?;
        let pic_width_in_luma_samples = r.read_ue("pic_width_in_luma_samples")?;
        let pic_height_in_luma_samples = r.read_ue("pic_height_in_luma_samples")?;
        let conformance_window = if r.read_bool("conformance_window_flag")? {
            Some(ConformanceWindow::from_bits(&mut r)?)
        } else {
            None
        };
        let bit_depth_luma_minus8 = r.read_ue("bit_depth_luma_minus8")?;
        if bit_depth_luma_minus8 > 8 {
            return Err(Error("bit_depth_luma_minus8 must be in [0, 8]".to_owned()));
        }
        let bit_depth_luma_minus8 = bit_depth_luma_minus8 as u8;
        let bit_depth_chroma_minus8 = r.read_ue("bit_depth_chroma_minus8")?;
        if bit_depth_chroma_minus8 > 8 {
            return Err(Error(
                "bit_depth_chroma_minus8 must be in [0, 8]".to_owned(),
            ));
        }
        let bit_depth_chroma_minus8 = bit_depth_chroma_minus8 as u8;
        let log2_max_pic_order_cnt_lsb_minus4 = r.read_ue("log2_max_pic_order_cnt_lsb_minus4")?;
        let sps_sub_layer_ordering_info_present_flag =
            r.read_bool("sps_sub_layer_ordering_info_present_flag")?;
        {
            let start = if sps_sub_layer_ordering_info_present_flag {
                0
            } else {
                sps_max_sub_layers_minus1
            };
            for _ in start..=sps_max_sub_layers_minus1 {
                let _sps_max_dec_pic_buffering_minus1 =
                    r.read_ue("sps_max_dec_pic_buffering_minus1")?;
                let _sps_max_num_reorder_pics = r.read_ue("sps_max_num_reorder_pics")?;
                let _sps_max_latency_increase_plus1 =
                    r.read_ue("sps_max_latency_increase_plus1")?;
            }
        }
        let _ = r.read_ue("log2_min_luma_coding_block_size_minus3")?;
        let _ = r.read_ue("log2_diff_max_min_luma_coding_block_size")?;
        let _ = r.read_ue("log2_min_luma_transform_block_size_minus2")?;
        let _ = r.read_ue("log2_diff_max_min_luma_transform_block_size")?;
        let _ = r.read_ue("max_transform_hierarchy_depth_inter")?;
        let _ = r.read_ue("max_transform_hierarchy_depth_intra")?;
        let scaling_list_enabled_flag = r.read_bool("scaling_list_enabled_flag")?;
        if scaling_list_enabled_flag {
            let sps_scaling_list_data_present_flag =
                r.read_bool("sps_scaling_list_data_present_flag")?;
            if sps_scaling_list_data_present_flag {
                let _scaling_list_data = ScalingListData::from_bits(&mut r)?;
            }
        }
        let _ = r.read_bool("amp_enabled_flag")?;
        let _ = r.read_bool("sample_adaptive_offset_enabled_flag")?;
        let pcm_enabled_flag = r.read_bool("pcm_enabled_flag")?;
        if pcm_enabled_flag {
            r.skip(4, "pcm_sample_bit_depth_luma_minus1")?;
            r.skip(4, "pcm_sample_bit_depth_chroma_minus1")?;
            let _log2_min_pcm_luma_coding_block_size_minus3 =
                r.read_ue("log2_min_pcm_luma_coding_block_size_minus3")?;
            let _log2_diff_max_min_pcm_luma_coding_block_size =
                r.read_ue("log2_diff_max_min_pcm_luma_coding_block_size")?;
            let _pcm_loop_filter_disabled_flag = r.read_bool("pcm_loop_filter_disabled_flag")?;
        }
        let num_short_term_ref_pic_sets = r.read_ue("num_short_term_ref_pic_sets")?;
        for i in 0..num_short_term_ref_pic_sets as usize {
            let _short_term_ref_pic_set = ShortTermRefPicSet::from_bits(&mut r, i)?;
        }
        let long_term_ref_pics_present_flag = r.read_bool("long_term_ref_pics_present_flag")?;
        if long_term_ref_pics_present_flag {
            let num_long_term_ref_pics_sps = r.read_ue("num_long_term_ref_pics_sps")?;
            for _i in 0..num_long_term_ref_pics_sps {
                r.skip(
                    log2_max_pic_order_cnt_lsb_minus4 + 4,
                    "lt_ref_pic_poc_lsb_sps",
                )?;
                let _used_by_curr_pic_lt_sps_flag = r.read_bool("used_by_curr_pic_lt_sps_flag")?;
            }
        }
        let _ = r.read_bool("sps_temporal_mvp_enabled_flag")?;
        let _ = r.read_bool("strong_intra_smoothing_enabled_flag")?;
        let vui = if r.read_bool("vui_parameters_present_flag")? {
            Some(VuiParameters::from_bits(&mut r)?)
        } else {
            None
        };
        let sps_extension_flag = r.read_bool("sps_extension_flag")?;
        if sps_extension_flag {
            let sps_range_extension_flag = r.read_bool("sps_range_extension_flag")?;
            let sps_multilayer_extension_flag = r.read_bool("sps_multilayer_extension_flag")?;
            let sps_3d_extension_flag = r.read_bool("sps_3d_extension_flag")?;
            let sps_scc_extension_flag = r.read_bool("sps_scc_extension_flag")?;
            let sps_extension_4bits: u8 = r.read(4, "sps_extension_4bits")?;
            if sps_range_extension_flag {
                // H.265 section 7.3.2.2.2, `sps_range_extension`.
                r.skip(9, "sps_range_extension")?;
            }
            if sps_multilayer_extension_flag {
                // H.265 section F.7.3.2.2.4, `sps_multilayer_extension`.
                r.skip(1, "inter_view_mv_vert_constraint_flag")?;
            }
            if sps_3d_extension_flag {
                // d == 0
                r.skip(1, "iv_di_mc_enabled_flag")?;
                r.skip(1, "iv_mv_scal_enabled_flag")?;
                let _ = r.read_ue("log2_ivmc_sub_pb_size_minus3")?;
                r.skip(1, "iv_res_pred_enabled_flag")?;
                r.skip(1, "depth_ref_enabled_flag")?;
                r.skip(1, "vsp_mc_enabled_flag")?;
                r.skip(1, "dbbp_enabled_flag")?;

                // d == 1
                r.skip(1, "tex_mc_enabled_flag")?;
                let _ = r.read_ue("log2_texmc_sub_pb_size_minus3")?;
                r.skip(1, "intra_contour_enabled_flag")?;
                r.skip(1, "intra_dc_only_wedge_enabled_flag")?;
                r.skip(1, "cqt_cu_part_pred_enabled_flag")?;
                r.skip(1, "inter_dc_only_enabled_flag")?;
                r.skip(1, "skip_intra_enabled_flag")?;
            }
            if sps_scc_extension_flag {
                // H.265 section 7.3.2.2.3, `sps_scc_extension`.
                r.skip(1, "sps_curr_pic_ref_enabled_flag")?;
                if r.read_bool("palette_mode_enabled_flag")? {
                    let _ = r.read_ue("palette_max_size");
                    let _ = r.read_ue("delta_palette_max_predictor_size")?;
                    if r.read_bool("sps_palette_predictor_initializers_present_flag")? {
                        let _ = r.read_ue("sps_num_palette_predictor_initializers_minus1")?;
                    }
                }
            }
            if sps_extension_4bits != 0 {
                return Err(Error("sps_extension_4bits unimplemented".to_owned()));
            }
        }
        r.finish_rbsp()?;
        Ok(Self {
            sps_max_sub_layers_minus1,
            sps_temporal_id_nesting_flag,
            profile_tier_level,
            chroma_format_idc,
            pic_width_in_luma_samples,
            pic_height_in_luma_samples,
            conformance_window,
            bit_depth_luma_minus8,
            bit_depth_chroma_minus8,
            vui,
        })
    }

    pub(crate) fn profile(&self) -> &Profile {
        self.profile_tier_level
            .profile
            .as_ref()
            .expect("profile must be set on sps")
    }

    pub(crate) fn general_level_idc(&self) -> u8 {
        self.profile_tier_level.general_level_idc
    }

    /// The maximum sub layers, in the range [1, 7].
    pub fn max_sub_layers(&self) -> u8 {
        self.sps_max_sub_layers_minus1 + 1
    }

    pub fn temporal_id_nesting_flag(&self) -> bool {
        self.sps_temporal_id_nesting_flag
    }

    pub fn vui(&self) -> Option<&VuiParameters> {
        self.vui.as_ref()
    }

    /// Returns the pixel dimensions `(width, height)`, unless the conformance
    /// cropping window is larger than the picture.
    pub fn pixel_dimensions(&self) -> Result<(u32, u32), String> {
        let mut width = self.pic_width_in_luma_samples;
        let mut height = self.pic_height_in_luma_samples;
        if let Some(ref c) = self.conformance_window {
            // Subtract out the conformance window, which is specified in
            // *chroma* samples.
            let width_shift = (self.chroma_format_idc == 1 || self.chroma_format_idc == 2) as u32;
            let height_shift = (self.chroma_format_idc == 1) as u32;
            let sub_width = c
                .left_offset
                .checked_add(c.right_offset)
                .and_then(|x| x.checked_shl(width_shift))
                .ok_or("bad conformance window")?;
            let sub_height = c
                .top_offset
                .checked_add(c.bottom_offset)
                .and_then(|x| x.checked_shl(height_shift))
                .ok_or("bad conformance window")?;
            width = width
                .checked_sub(sub_width)
                .ok_or("bad conformance window")?;
            height = height
                .checked_sub(sub_height)
                .ok_or("bad conformance window")?;
        }
        Ok((width, height))
    }

    pub fn rfc6381_codec(&self) -> String {
        let profile = self.profile();

        // See ISO/IEC 14496-15, or the working draft mentioned here:
        // <https://mpeg.chiariglione.org/standards/mpeg-4/carriage-nal-unit-structured-video-iso-base-media-file-format/wd-isoiec-14496>.
        // Section E.3.

        // > When the first element of a value is a code indicating a codec from
        // > the High Efficiency Video Coding specification (ISO/IEC 23008-2),
        // > as documented in clause 8 (such as 'hev1', 'hev2', 'hvc1', 'hvc2',
        // > 'shv1' or 'shc1'), the elements following are a series of values
        // > from the HEVC or SHVC decoder configuration record, separated by
        // > period characters (“.”). In all numeric encodings, leading zeroes
        // > may be omitted,

        // > 1. the general_profile_space, encoded as no character
        // >    (general_profile_space == 0), or ‘A’, ‘B’, ‘C’ for
        // >    general_profile_space 1, 2, 3, followed by the general_profile_idc
        // >    encoded as a decimal number;
        let general_profile_space = match profile.general_profile_space() {
            0 => "",
            1 => "A",
            2 => "B",
            3 => "C",
            _ => unreachable!("profile_space is 2 bits"),
        };
        let general_profile_idc = profile.general_profile_idc();

        // > 2. the general_profile_compatibility_flags, encoded in hexadecimal
        // >    (leading zeroes may be omitted);
        let general_profile_compatibility_flags = profile.general_profile_compatibility_flags();

        // > 3. the general_tier_flag, encoded as ‘L’ (general_tier_flag==0) or
        // >    ‘H’ (general_tier_flag==1), followed by the general_level_idc,
        // >    encoded as a decimal number;
        let general_tier_flag = match profile.general_tier_flag() {
            true => "H",
            false => "L",
        };
        let general_level_idc = self.profile_tier_level.general_level_idc;
        let mut out = format!("hvc1.{general_profile_space}{general_profile_idc}.{general_profile_compatibility_flags:02X}.{general_tier_flag}{general_level_idc}");

        // > 4. each of the 6 bytes of the constraint flags, starting from the
        //      byte containing the general_progressive_source_flag, each encoded
        //      encoded as a hexadecimal number, and the encoding of each byte
        //      separated by a period; trailing bytes that are zero may be
        //      omitted.
        let mut general_constraint_indicator_flags =
            &profile.general_constraint_indicator_flags()[..];
        while let [head @ .., 0] = general_constraint_indicator_flags {
            if head.is_empty() {
                // don't omit the leading byte, even if 0.
                break;
            }
            general_constraint_indicator_flags = head;
        }
        use std::fmt::Write as _;
        for b in general_constraint_indicator_flags {
            write!(&mut out, ".{b:02X}").expect("write to String should succeed");
        }
        out
    }

    pub(crate) fn chroma_format_idc(&self) -> u8 {
        self.chroma_format_idc
    }

    pub(crate) fn bit_depth_luma_minus8(&self) -> u8 {
        self.bit_depth_luma_minus8
    }

    pub(crate) fn bit_depth_chroma_minus8(&self) -> u8 {
        self.bit_depth_chroma_minus8
    }
}

/// Conformance cropping window, in luma samples.
#[derive(Debug)]
pub struct ConformanceWindow {
    pub left_offset: u32,
    pub right_offset: u32,
    pub top_offset: u32,
    pub bottom_offset: u32,
}

impl ConformanceWindow {
    pub fn from_bits<R: BitRead>(r: &mut R) -> Result<Self, BitReaderError> {
        let left_offset = r.read_ue("left_offset")?;
        let right_offset = r.read_ue("right_offset")?;
        let top_offset = r.read_ue("top_offset")?;
        let bottom_offset = r.read_ue("bottom_offset")?;
        Ok(Self {
            left_offset,
            right_offset,
            top_offset,
            bottom_offset,
        })
    }
}

/// H.265 section 7.3.3, `profile_tier_level`, `if( profilePresentFlag )` block.
#[derive(Debug)]
pub struct Profile(pub [u8; 11]);

impl Profile {
    pub fn from_bits<R: BitRead>(r: &mut R) -> Result<Self, BitReaderError> {
        Ok(Profile(r.read_to("profile")?))
    }

    #[inline]
    pub fn general_profile_space(&self) -> u8 {
        self.0[0] >> 6
    }

    /// Returns the `general_profile_compatibility_flags` as defined in ISO/IEC 14496-15 section 8.3.3.1.3:
    /// "`general_profile_compatibility_flag[ i ]`` for i from 0 to 31, inclusive".
    #[inline]
    pub fn general_profile_compatibility_flags(&self) -> u32 {
        u32::from_be_bytes([self.0[1], self.0[2], self.0[3], self.0[4]])
    }

    /// Returns the `general_constraint_indicator_flags` as defined in ISO/IEC 14496-15 section 8.3.3.1.3:
    /// "the 6 bytes starting with the byte containing the `general_progressive_source_flag`".
    #[inline]
    pub fn general_constraint_indicator_flags(&self) -> &[u8; 6] {
        self.0[5..11].try_into().expect("6 bytes")
    }

    #[inline]
    pub fn general_tier_flag(&self) -> bool {
        (self.0[0] & 0b0010_0000) != 0
    }

    #[inline]
    pub fn general_profile_idc(&self) -> u8 {
        self.0[0] & 0b0001_1111
    }
}

/// H.265 section 7.3.3.
#[derive(Debug)]
pub struct ProfileTierLevel {
    profile: Option<Profile>,
    general_level_idc: u8,
}

impl ProfileTierLevel {
    pub fn from_bits<R: BitRead>(
        r: &mut R,
        profile_present_flag: bool,
        sps_max_sub_layers_minus1: u8,
    ) -> Result<Self, BitReaderError> {
        // See H.265 section 7.3.3, profile_tier_level( 1, sps_max_sub_layers_minus1 ).
        let profile = if profile_present_flag {
            Some(Profile::from_bits(r)?)
        } else {
            None
        };
        let general_level_idc: u8 = r.read(8, "general_level_idc")?;
        if sps_max_sub_layers_minus1 > 0 {
            let sub_layer_presence_flags: u16 = r.read(16, "sub_layer_presence_flags")?;
            for i in 0..sps_max_sub_layers_minus1 {
                // TODO: check endianness here.
                let sub_layer_profile_present_flag = sub_layer_presence_flags & (1 << (2 * i)) != 0;
                let sub_layer_level_present_flag =
                    sub_layer_presence_flags & (1 << (2 * i + 1)) != 0;
                if sub_layer_profile_present_flag {
                    r.skip(2, "sub_layer_profile_space")?;
                    r.skip(1, "sub_layer_tier_flag")?;
                    r.skip(5, "sub_layer_profile_idc")?;
                    r.skip(32, "sub_layer_profile_compatibility_flags")?;
                    r.skip(1, "sub_layer_progressive_source_flag")?;
                    r.skip(1, "sub_layer_interlaced_source_flag")?;
                    r.skip(1, "sub_layer_non_packed_constraint_flag")?;
                    r.skip(1, "sub_layer_frame_only_constraint_flag")?;
                }
                r.skip(44, "stuff")?;
                if sub_layer_level_present_flag {
                    r.skip(8, "sub_layer_level_idc")?;
                }
            }
        }
        Ok(Self {
            profile,
            general_level_idc,
        })
    }
}

// H.265 section 7.3.2.3.
#[derive(Debug)]
pub struct Pps {
    tiles_enabled_flag: bool,
    entropy_coding_sync_enabled_flag: bool,
}

impl Pps {
    pub fn from_bits<R: BitRead>(mut r: R) -> Result<Self, Error> {
        let _pps_pic_parameter_set_id = r.read_ue("pps_pic_parameter_set_id")?;
        let _pps_seq_parameter_set_id = r.read_ue("pps_seq_parameter_set_id")?;
        let _dependent_slice_segments_enabled_flag =
            r.read_bool("dependent_slice_segments_enabled_flag")?;
        let _output_flag_present_flag = r.read_bool("output_flag_present_flag")?;
        let _num_extra_slice_header_bits: u8 = r.read(3, "num_extra_slice_header_bits")?;
        let _sign_data_hiding_enabled_flag = r.read_bool("sign_data_hiding_enabled_flag")?;
        let _cabac_init_present_flag = r.read_bool("cabac_init_present_flag")?;
        let _num_ref_idx_l0_default_active_minus1 =
            r.read_ue("num_ref_idx_l0_default_active_minus1")?;
        let _num_ref_idx_l1_default_active_minus1 =
            r.read_ue("num_ref_idx_l1_default_active_minus1")?;
        let _init_qp_minus26 = r.read_se("init_qp_minus26")?;
        let _constrained_intra_pred_flag = r.read_bool("constrained_intra_pred_flag")?;
        let _transform_skip_enabled_flag = r.read_bool("transform_skip_enabled_flag")?;
        let cu_qp_delta_enabled_flag = r.read_bool("cu_qp_delta_enabled_flag")?;
        if cu_qp_delta_enabled_flag {
            let _diff_cu_qp_delta_depth = r.read_ue("diff_cu_qp_delta_depth")?;
        }
        let _pps_cb_qp_offset = r.read_se("pps_cb_qp_offset")?;
        let _pps_cr_qp_offset = r.read_se("pps_cr_qp_offset")?;
        let _pps_slice_chroma_qp_offsets_present_flag =
            r.read_bool("pps_slice_chroma_qp_offsets_present_flag")?;
        let _weighted_pred_flag = r.read_bool("weighted_pred_flag")?;
        let _weighted_bipred_flag = r.read_bool("weighted_bipred_flag")?;
        let _transquant_bypass_enabled_flag = r.read_bool("transquant_bypass_enabled_flag")?;
        let tiles_enabled_flag = r.read_bool("tiles_enabled_flag")?;
        let entropy_coding_sync_enabled_flag = r.read_bool("entropy_coding_sync_enabled_flag")?;
        if tiles_enabled_flag {
            let _num_tile_columns_minus1 = r.read_ue("num_tile_columns_minus1")?;
            let _num_tile_rows_minus1 = r.read_ue("num_tile_rows_minus1")?;
            let uniform_spacing_flag = r.read_bool("uniform_spacing_flag")?;
            if !uniform_spacing_flag {
                for _i in 0..=_num_tile_columns_minus1 {
                    let _column_width_minus1 = r.read_ue("column_width_minus1")?;
                }
                for _i in 0..=_num_tile_rows_minus1 {
                    let _row_height_minus1 = r.read_ue("row_height_minus1")?;
                }
            }
            let _loop_filter_across_tiles_enabled_flag =
                r.read_bool("loop_filter_across_tiles_enabled_flag")?;
        }
        let _pps_loop_filter_across_slices_enabled_flag =
            r.read_bool("pps_loop_filter_across_slices_enabled_flag")?;
        let deblocking_filter_control_present_flag =
            r.read_bool("deblocking_filter_control_present_flag")?;
        if deblocking_filter_control_present_flag {
            let _deblocking_filter_override_enabled_flag =
                r.read_bool("deblocking_filter_override_enabled_flag")?;
            let pps_deblocking_filter_disabled_flag =
                r.read_bool("pps_deblocking_filter_disabled_flag")?;
            if !pps_deblocking_filter_disabled_flag {
                let _pps_beta_offset_div2 = r.read_se("pps_beta_offset_div2")?;
                let _pps_tc_offset_div2 = r.read_se("pps_tc_offset_div2")?;
            }
        }
        let pps_scaling_list_data_present_flag =
            r.read_bool("pps_scaling_list_data_present_flag")?;
        if pps_scaling_list_data_present_flag {
            return Err(Error(
                "pps_scaling_list_data_present unimplemented".to_owned(),
            ));
        }
        let _lists_modification_present_flag = r.read_bool("lists_modification_present_flag")?;
        let _log2_parallel_merge_level_minus2 = r.read_ue("log2_parallel_merge_level_minus2")?;
        let _slice_segment_header_extension_present_flag =
            r.read_bool("slice_segment_header_extension_present_flag")?;
        let pps_extension_present_flag = r.read_bool("pps_extension_present_flag")?;
        if pps_extension_present_flag {
            let pps_range_extension_flag = r.read_bool("pps_range_extension_flag")?;
            let pps_multilayer_extension_flag = r.read_bool("pps_multilayer_extension_flag")?;
            let pps_3d_extension_flag = r.read_bool("pps_3d_extension_flag")?;
            let pps_scc_extension_flag = r.read_bool("pps_scc_extension_flag")?;
            let pps_extension_4bits: u8 = r.read(4, "pps_extension_4bits")?;
            if pps_range_extension_flag {
                return Err(Error("pps_range_extension_flag unimplemented".to_owned()));
            }
            if pps_multilayer_extension_flag {
                return Err(Error(
                    "pps_multilayer_extension_flag unimplemented".to_owned(),
                ));
            }
            if pps_3d_extension_flag {
                return Err(Error("pps_3d_extension_flag unimplemented".to_owned()));
            }
            if pps_scc_extension_flag {
                return Err(Error("pps_scc_extension_flag unimplemented".to_owned()));
            }
            if pps_extension_4bits != 0 {
                return Err(Error("pps_extension_4bits unimplemented".to_owned()));
            }
        }
        r.finish_rbsp()?;
        Ok(Self {
            tiles_enabled_flag,
            entropy_coding_sync_enabled_flag,
        })
    }

    pub(crate) fn entropy_coding_sync_enabled_flag(&self) -> bool {
        self.entropy_coding_sync_enabled_flag
    }

    pub(crate) fn tiles_enabled_flag(&self) -> bool {
        self.tiles_enabled_flag
    }
}

/// T.REC H.265 section 7.3.4, `scaling_list_data`.
#[derive(Debug)]
pub struct ScalingListData {}

impl ScalingListData {
    pub fn from_bits<R: BitRead>(r: &mut R) -> Result<Self, Error> {
        for size_id in 0..4 {
            let num_matrices = if size_id == 3 { 2 } else { 6 };
            for _ in 0..num_matrices {
                if !r.read_bool("scaling_list_pred_mode_flag")? {
                    let _ = r.read_ue("scaling_list_pred_matrix_id_delta")?;
                } else {
                    let coef_num = std::cmp::min(64, 1 << (4 + (size_id << 1)));
                    if size_id > 1 {
                        let _ = r.read_se("scaling_list_dc_coef_minus8")?;
                    }
                    for _ in 0..coef_num {
                        let _ = r.read_se("scaling_list_delta_coef");
                    }
                }
            }
        }
        Ok(Self {})
    }
}

/// T.REC H.265 section 7.3.7.
#[derive(Debug)]
pub struct ShortTermRefPicSet {}

impl ShortTermRefPicSet {
    pub fn from_bits<R: BitRead>(r: &mut R, st_rps_idx: usize) -> Result<Self, Error> {
        // See T.REC H.265 section 7.3.7, st_ref_pic_set.
        let inter_ref_pic_set_prediction_flag =
            st_rps_idx != 0 && r.read_bool("inter_ref_pic_set_prediction_flag")?;
        if inter_ref_pic_set_prediction_flag {
            return Err(Error(
                "inter_ref_pic_set_prediction_flag unimplemented".to_owned(),
            ));
        } else {
            let num_negative_pics = r.read_ue("num_negative_pics")?;
            let num_positive_pics = r.read_ue("num_positive_pics")?;
            for _i in 0..num_negative_pics {
                let _delta_poc_s0_minus1 = r.read_ue("delta_poc_s0_minus1")?;
                let _used_by_curr_pic_s0_flag = r.read_bool("used_by_curr_pic_s0_flag")?;
            }
            for _i in 0..num_positive_pics {
                let _delta_poc_s1_minus1 = r.read_ue("delta_poc_s1_minus1")?;
                let _used_by_curr_pic_s1_flag = r.read_bool("used_by_curr_pic_s1_flag")?;
            }
        }
        Ok(Self {})
    }
}

/// Aspect ratio information.
// This is copied from `h264_reader`; the H.264 and H.265 formats are
// apparently identical. Licenses are compatible. Copying seems safer in case
// the formats diverge in future specifications, and in any case
// `h264_reader::nal::sps::AspectRatioInfo::read` is private at present.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub enum AspectRatioInfo {
    #[default]
    Unspecified,
    Ratio1_1,
    Ratio12_11,
    Ratio10_11,
    Ratio16_11,
    Ratio40_33,
    Ratio24_11,
    Ratio20_11,
    Ratio32_11,
    Ratio80_33,
    Ratio18_11,
    Ratio15_11,
    Ratio64_33,
    Ratio160_99,
    Ratio4_3,
    Ratio3_2,
    Ratio2_1,
    Reserved(u8),
    Extended(u16, u16),
}
impl AspectRatioInfo {
    fn from_bits<R: BitRead>(r: &mut R) -> Result<Option<AspectRatioInfo>, BitReaderError> {
        let aspect_ratio_info_present_flag = r.read_bool("aspect_ratio_info_present_flag")?;
        Ok(if aspect_ratio_info_present_flag {
            let aspect_ratio_idc = r.read(8, "aspect_ratio_idc")?;
            Some(match aspect_ratio_idc {
                0 => AspectRatioInfo::Unspecified,
                1 => AspectRatioInfo::Ratio1_1,
                2 => AspectRatioInfo::Ratio12_11,
                3 => AspectRatioInfo::Ratio10_11,
                4 => AspectRatioInfo::Ratio16_11,
                5 => AspectRatioInfo::Ratio40_33,
                6 => AspectRatioInfo::Ratio24_11,
                7 => AspectRatioInfo::Ratio20_11,
                8 => AspectRatioInfo::Ratio32_11,
                9 => AspectRatioInfo::Ratio80_33,
                10 => AspectRatioInfo::Ratio18_11,
                11 => AspectRatioInfo::Ratio15_11,
                12 => AspectRatioInfo::Ratio64_33,
                13 => AspectRatioInfo::Ratio160_99,
                14 => AspectRatioInfo::Ratio4_3,
                15 => AspectRatioInfo::Ratio3_2,
                16 => AspectRatioInfo::Ratio2_1,
                255 => {
                    AspectRatioInfo::Extended(r.read(16, "sar_width")?, r.read(16, "sar_height")?)
                }
                _ => AspectRatioInfo::Reserved(aspect_ratio_idc),
            })
        } else {
            None
        })
    }

    /// Returns the aspect ratio as `(width, height)`, if specified.
    pub fn get(self) -> Option<(u16, u16)> {
        match self {
            AspectRatioInfo::Unspecified => None,
            AspectRatioInfo::Ratio1_1 => Some((1, 1)),
            AspectRatioInfo::Ratio12_11 => Some((12, 11)),
            AspectRatioInfo::Ratio10_11 => Some((10, 11)),
            AspectRatioInfo::Ratio16_11 => Some((16, 11)),
            AspectRatioInfo::Ratio40_33 => Some((40, 33)),
            AspectRatioInfo::Ratio24_11 => Some((24, 11)),
            AspectRatioInfo::Ratio20_11 => Some((20, 11)),
            AspectRatioInfo::Ratio32_11 => Some((32, 11)),
            AspectRatioInfo::Ratio80_33 => Some((80, 33)),
            AspectRatioInfo::Ratio18_11 => Some((18, 11)),
            AspectRatioInfo::Ratio15_11 => Some((15, 11)),
            AspectRatioInfo::Ratio64_33 => Some((64, 33)),
            AspectRatioInfo::Ratio160_99 => Some((160, 99)),
            AspectRatioInfo::Ratio4_3 => Some((4, 3)),
            AspectRatioInfo::Ratio3_2 => Some((3, 2)),
            AspectRatioInfo::Ratio2_1 => Some((2, 1)),
            AspectRatioInfo::Reserved(_) => None,
            AspectRatioInfo::Extended(width, height) => {
                // ISO/IEC 14496-10 section E.2.1: "When ... sar_width is equal to 0 or sar_height
                // is equal to 0, the sample aspect ratio shall be considered unspecified by this
                // Recommendation | International Standard."
                if width == 0 || height == 0 {
                    None
                } else {
                    Some((width, height))
                }
            }
        }
    }
}

/// T.REC H.265 section E.2.1 `vui_parameters`.
#[derive(Debug)]
pub struct VuiParameters {
    aspect_ratio: Option<AspectRatioInfo>,
    timing_info: Option<VuiTimingInfo>,
    bitstream_restriction: Option<BitstreamRestriction>,
}

impl VuiParameters {
    pub fn from_bits<R: BitRead>(r: &mut R) -> Result<Self, Error> {
        // See T.REC H.265 section E.2.1, vui_parameters.
        let aspect_ratio = AspectRatioInfo::from_bits(r)?;
        let overscan_info_present_flag = r.read_bool("overscan_info_present_flag")?;
        if overscan_info_present_flag {
            let _overscan_appropriate_flag = r.read_bool("overscan_appropriate_flag")?;
        }
        let video_signal_type_present_flag = r.read_bool("video_signal_type_present_flag")?;
        if video_signal_type_present_flag {
            r.skip(3, "video_format")?;
            let _video_full_range_flag = r.read_bool("video_full_range_flag")?;
            let colour_description_present_flag = r.read_bool("colour_description_present_flag")?;
            if colour_description_present_flag {
                r.skip(8, "colour_primaries")?;
                r.skip(8, "transfer_characteristics")?;
                r.skip(8, "matrix_coeffs")?;
            }
        }
        let chroma_loc_info_present_flag = r.read_bool("chroma_loc_info_present_flag")?;
        if chroma_loc_info_present_flag {
            let _chroma_sample_loc_type_top_field =
                r.read_ue("chroma_sample_loc_type_top_field")?;
            let _chroma_sample_loc_type_bottom_field =
                r.read_ue("chroma_sample_loc_type_bottom_field")?;
        }
        let _neutral_chroma_indication_flag = r.read_bool("neutral_chroma_indication_flag")?;
        let _field_seq_flag = r.read_bool("field_seq_flag")?;
        let _frame_field_info_present_flag = r.read_bool("frame_field_info_present_flag")?;
        let default_display_window_flag = r.read_bool("default_display_window_flag")?;
        if default_display_window_flag {
            let _def_disp_win_left_offset = r.read_ue("def_disp_win_left_offset")?;
            let _def_disp_win_right_offset = r.read_ue("def_disp_win_right_offset")?;
            let _def_disp_win_top_offset = r.read_ue("def_disp_win_top_offset")?;
            let _def_disp_win_bottom_offset = r.read_ue("def_disp_win_bottom_offset")?;
        }
        let timing_info = if r.read_bool("vui_timing_info_present_flag")? {
            Some(VuiTimingInfo::from_bits(r)?)
        } else {
            None
        };
        let bitstream_restriction = if r.read_bool("bitstream_restriction_flag")? {
            Some(BitstreamRestriction::from_bits(r)?)
        } else {
            None
        };
        Ok(Self {
            aspect_ratio,
            timing_info,
            bitstream_restriction,
        })
    }

    pub fn aspect_ratio(&self) -> Option<AspectRatioInfo> {
        self.aspect_ratio
    }

    pub fn timing_info(&self) -> Option<&VuiTimingInfo> {
        self.timing_info.as_ref()
    }

    pub fn min_spatial_segmentation_idc(&self) -> Option<u16> {
        self.bitstream_restriction
            .as_ref()
            .map(|b| b.min_spatial_segmentation_idc)
    }
}

#[derive(Debug)]
struct BitstreamRestriction {
    min_spatial_segmentation_idc: u16,
}

impl BitstreamRestriction {
    fn from_bits<R: BitRead>(r: &mut R) -> Result<Self, Error> {
        let _tiles_fixed_structure_flag = r.read_bool("tiles_fixed_structure_flag")?;
        let _motion_vectors_over_pic_boundaries_flag =
            r.read_bool("motion_vectors_over_pic_boundaries_flag")?;
        let _restricted_ref_pic_lists_flag = r.read_bool("restricted_ref_pic_lists_flag")?;
        let min_spatial_segmentation_idc = r.read_ue("min_spatial_segmentation_idc")?;
        if min_spatial_segmentation_idc >= 4096 {
            return Err(Error(
                "min_spatial_segmentation_idc must be less than 4096".into(),
            ));
        }
        let min_spatial_segmentation_idc = min_spatial_segmentation_idc as u16;
        let _max_bytes_per_pic_denom = r.read_ue("max_bytes_per_pic_denom")?;
        let _max_bits_per_min_cu_denom = r.read_ue("max_bits_per_min_cu_denom")?;
        let _log2_max_mv_length_horizontal = r.read_ue("log2_max_mv_length_horizontal")?;
        let _log2_max_mv_length_vertical = r.read_ue("log2_max_mv_length_vertical")?;
        Ok(Self {
            min_spatial_segmentation_idc,
        })
    }
}

/// T.REC H.265 section E.2.1 `vui_parameters`, `if( vui_timing_info_present_flag )` block.
#[derive(Debug)]
pub struct VuiTimingInfo {
    num_units_in_tick: u32,
    time_scale: u32,
}

impl VuiTimingInfo {
    pub fn from_bits<R: BitRead>(r: &mut R) -> Result<Self, Error> {
        let num_units_in_tick = r.read(32, "vui_num_units_in_tick")?;
        let time_scale = r.read(32, "vui_time_scale")?;
        if r.read_bool("vui_poc_proportional_to_timing_flag")? {
            let _ = r.read_ue("vui_num_ticks_poc_diff_one_minus1")?;
        }
        let hrd_parameters_present_flag = r.read_bool("vui_hrd_parameters_present_flag")?;
        if hrd_parameters_present_flag {
            return Err(Error(
                "hrd_parameters_present_flag unimplemented".to_owned(),
            ));
        }
        Ok(Self {
            num_units_in_tick,
            time_scale,
        })
    }

    pub fn num_units_in_tick(&self) -> u32 {
        self.num_units_in_tick
    }

    pub fn time_scale(&self) -> u32 {
        self.time_scale
    }
}

#[cfg(test)]
mod tests {
    use crate::testutil::init_logging;

    use super::*;

    struct LoggingBitReader<R>(R);

    impl<R: h264_reader::rbsp::BitRead> h264_reader::rbsp::BitRead for LoggingBitReader<R> {
        fn read_ue(&mut self, name: &'static str) -> Result<u32, BitReaderError> {
            let res = self.0.read_ue(name)?;
            log::debug!("read_ue: {} -> {}", name, res);
            Ok(res)
        }

        fn read_se(&mut self, name: &'static str) -> Result<i32, BitReaderError> {
            let res = self.0.read_se(name)?;
            log::debug!("read_se: {} -> {}", name, res);
            Ok(res)
        }

        fn read_bool(&mut self, name: &'static str) -> Result<bool, BitReaderError> {
            let res = self.0.read_bool(name)?;
            log::debug!("read_bool: {} -> {}", name, res);
            Ok(res)
        }

        fn read<U: h264_reader::rbsp::Numeric>(
            &mut self,
            bit_count: u32,
            name: &'static str,
        ) -> Result<U, BitReaderError> {
            let res = self.0.read(bit_count, name)?;
            log::debug!("read: {}({}) -> {:?}", name, bit_count, res);
            Ok(res)
        }

        fn read_to<V: h264_reader::rbsp::Primitive>(
            &mut self,
            name: &'static str,
        ) -> Result<V, BitReaderError> {
            let res = self.0.read_to(name)?;
            log::debug!("read_to: {}({})", name, std::mem::size_of::<V>() * 8);
            Ok(res)
        }

        fn skip(&mut self, bit_count: u32, name: &'static str) -> Result<(), BitReaderError> {
            self.0.skip(bit_count, name)?;
            log::debug!("skip: {}({})", name, bit_count);
            Ok(())
        }

        fn has_more_rbsp_data(&mut self, name: &'static str) -> Result<bool, BitReaderError> {
            let res = self.0.has_more_rbsp_data(name)?;
            log::debug!("has_more_rbsp_data: {} -> {}", name, res);
            Ok(res)
        }

        fn finish_rbsp(self) -> Result<(), BitReaderError> {
            self.0.finish_rbsp()?;
            log::debug!("finish_rbsp");
            Ok(())
        }

        fn finish_sei_payload(self) -> Result<(), BitReaderError> {
            self.0.finish_sei_payload()?;
            log::debug!("finish_sei_payload");
            Ok(())
        }
    }

    #[test]
    fn parse_sps_own() {
        init_logging();
        let data = &b"\x42\x01\x01\x01\x60\x00\x00\x03\x00\xb0\x00\x00\x03\x00\x00\x03\x00\x5a\xa0\x05\x82\x01\xe1\x63\x6b\x92\x45\x2f\xcd\xc1\x41\x81\x41\x00\x00\x03\x00\x01\x00\x00\x03\x00\x0c\xa1"[..];
        let (h, bits) = split(data).unwrap();
        assert_eq!(h.unit_type(), UnitType::SpsNut);
        let bits = LoggingBitReader(bits);
        let sps = dbg!(Sps::from_bits(bits).unwrap());
        let rfc6381_codec = sps.rfc6381_codec();
        assert_eq!(rfc6381_codec, "hvc1.1.60000000.L90.B0");
        assert_eq!(sps.pixel_dimensions().unwrap(), (704, 480));
        let vui = sps.vui().unwrap();
        let timing = vui.timing_info().unwrap();
        assert_eq!(timing.num_units_in_tick(), 1);
        assert_eq!(timing.time_scale(), 12);
    }

    #[test]
    fn parse_pps() {
        init_logging();
        let data = &b"D\x01\xc0\xf2\xc6\x8d\x03\xb3@"[..];
        let (h, bits) = split(data).unwrap();
        assert_eq!(h.unit_type(), UnitType::PpsNut);
        let bits = LoggingBitReader(bits);
        let _pps = dbg!(Pps::from_bits(bits).unwrap());
        // panic!("pps: {pps:#?}");
    }

    #[test]
    fn unit_type_roundtrip() {
        init_logging();
        for raw in 0..64 {
            let unit_type = UnitType::try_from(raw).unwrap();
            assert_eq!(raw, u8::from(unit_type));
        }
    }
}
