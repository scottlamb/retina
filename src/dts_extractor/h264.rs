// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

// https://github.com/bluenviron/mediacommon/blob/b90ac7271130c8dd5c507a199e4ede9563b8eded/pkg/codecs/h264/dts_extractor.go

use crate::{codec::TolerantBitReader, dts_extractor::NalUnitIter};
use h264_reader::{
    nal::{
        NalHeader, NalHeaderError, UnitType,
        sps::{FrameMbsFlags, PicOrderCntType, SeqParameterSet, SpsError},
    },
    rbsp::{BitRead, BitReaderError, ByteReader},
};
use std::ops::{AddAssign, Div, Mul};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum H264DtsExtractorError {
    #[error("decode sps: {0}")]
    DecodeSps(std::io::Error),

    #[error("parse sps: {0:?}")]
    ParseSps(SpsError),

    #[error("{0}")]
    FromInt(#[from] std::num::TryFromIntError),

    #[error("too many reordered frames ({0})")]
    TooManyReorderedFrames(i64),

    #[error("access unit doesn't contain an IDR or non-IDR NALU")]
    NoIdrOrNonIdr,

    #[error("pic_order_cnt_type = 1 is not supported yet")]
    PicOrderCntType1Unsupported,

    #[error("random access frame not received yet")]
    RandomAccessNotReceivedYet,

    #[error("DTS is greater than PTS: '{0}' vs '{1}'")]
    DtsGreaterThanPts(i64, i64),

    #[error("DTS is not monotonically increasing, was {0}, now is {1}")]
    DtsNotIncreasing(i64, i64),

    #[error("read: {0}")]
    Read(#[from] std::io::Error),

    #[error("unit type value {0:?} out of range")]
    ParseNalHeader(NalHeaderError),

    #[error("no unit type header")]
    NoHeader,

    #[error("{0:?}")]
    BitReader(BitReaderError),
}

// Allows to extract DTS from PTS.
#[derive(Debug)]
pub struct H264DtsExtractor {
    sps: Vec<u8>,
    spsp: Option<SeqParameterSet>,
    prev_dts: Option<i64>,
    random_received: bool,
    expected_poc: u32,
    reordered_frames: i64,
    pause: i64,
    au_count: i64,
    poc_increment: PocIncrement,
    prev_poc: u32,
    prev_prev_poc: u32,
}

impl Default for H264DtsExtractor {
    fn default() -> Self {
        Self::new()
    }
}

const MAX_REORDERED_FRAMES: i64 = 10;

impl H264DtsExtractor {
    pub fn new() -> Self {
        Self {
            sps: Vec::new(),
            spsp: None,
            prev_dts: None,
            random_received: false,
            expected_poc: 0,
            reordered_frames: 0,
            pause: 0,
            au_count: 0,
            poc_increment: PocIncrement::Two,
            prev_poc: 0,
            prev_prev_poc: 0,
        }
    }

    // Extracts the decode timestamp of an access unit. The first call must be an IDR.
    pub fn extract(
        &mut self,
        sps: &[u8],
        au: &[u8],
        pts: i64,
    ) -> Result<i64, H264DtsExtractorError> {
        use H264DtsExtractorError::*;

        let (dts, skip_checks) = self.extract_inner(sps, NalUnitIter::new(au), pts)?;
        if !skip_checks && dts > pts {
            return Err(DtsGreaterThanPts(dts, pts));
        }
        if let Some(prev_dts) = self.prev_dts
            && dts < prev_dts
        {
            return Err(DtsNotIncreasing(prev_dts, dts));
        }
        self.prev_dts = Some(dts);
        Ok(dts)
    }

    fn extract_inner(
        &mut self,
        sps: &[u8],
        au: NalUnitIter,
        pts: i64,
    ) -> Result<(i64, bool), H264DtsExtractorError> {
        use H264DtsExtractorError::*;
        use PocIncrement::*;

        if sps != self.sps {
            self.sps = sps.to_vec();

            // Reset state.
            self.spsp = None;
            self.random_received = false;
            self.expected_poc = 0;
            self.reordered_frames = 0;
            self.pause = 0;
            self.poc_increment = Two;
            self.prev_poc = 0;
            self.prev_prev_poc = 0;
        }
        let sps = match self.spsp.as_mut() {
            Some(sps) => sps,
            None => {
                let sps_rbsp = h264_reader::rbsp::decode_nal(sps).map_err(DecodeSps)?;
                let mut sps_has_extra_trailing_data = false;
                let sps = SeqParameterSet::from_bits(TolerantBitReader {
                    inner: h264_reader::rbsp::BitReader::new(&*sps_rbsp),
                    has_extra_trailing_data: &mut sps_has_extra_trailing_data,
                })
                .map_err(ParseSps)?;
                self.spsp.insert(sps)
            }
        };

        // A value of 00 indicates that the content of the NAL unit is not
        // used to reconstruct reference pictures for inter picture
        // prediction.  Such NAL units can be discarded without risking
        // the integrity of the reference pictures.  Values greater thanMore actions
        // 00 indicate that the decoding of the NAL unit is required to
        // maintain the integrity of the reference pictures.
        let mut non_zero_nal_ref_id_found = false;
        let mut idr = None;
        let mut non_idr = None;

        for nalu in au {
            non_zero_nal_ref_id_found = non_zero_nal_ref_id_found || ((nalu[0] & 0x60) > 0);
            match get_unit_type(nalu)? {
                UnitType::SliceLayerWithoutPartitioningNonIdr => {
                    non_idr = Some(nalu);
                    break;
                }
                UnitType::SliceLayerWithoutPartitioningIdr => {
                    idr = Some(nalu);
                    break;
                }
                _ => {}
            }
        }

        let FrameMbsFlags::Frames = sps.frame_mbs_flags else {
            return Ok((pts, false));
        };

        let log2_max_pic_order_cnt_lsb_minus4 = match sps.pic_order_cnt {
            PicOrderCntType::TypeZero {
                log2_max_pic_order_cnt_lsb_minus4,
            } => log2_max_pic_order_cnt_lsb_minus4,
            PicOrderCntType::TypeOne {
                delta_pic_order_always_zero_flag: _,
                offset_for_non_ref_pic: _,
                offset_for_top_to_bottom_field: _,
                offsets_for_ref_frame: _,
            } => return Err(PicOrderCntType1Unsupported),
            PicOrderCntType::TypeTwo => return Ok((pts, false)),
        };

        if !self.random_received {
            if idr.is_none() {
                return Err(RandomAccessNotReceivedYet);
            }
            self.random_received = true;
        }

        let mut pts_dts_diff;

        if let Some(idr) = idr {
            self.expected_poc = get_picture_order_count(
                idr,
                true,
                sps.log2_max_frame_num_minus4,
                log2_max_pic_order_cnt_lsb_minus4,
            )?;

            if matches!(self.poc_increment, Two) {
                if !self.expected_poc.is_multiple_of(2) {
                    self.poc_increment = One;
                }

                self.au_count = 1;
                self.prev_prev_poc = 0;
                self.prev_poc = self.expected_poc;
            }

            pts_dts_diff = 0
        } else if let Some(non_idr) = non_idr {
            let poc = get_picture_order_count(
                non_idr,
                false,
                sps.log2_max_frame_num_minus4,
                log2_max_pic_order_cnt_lsb_minus4,
            )?;

            if self.au_count < 5 && matches!(self.poc_increment, Two) {
                if (poc % 2) != 0 {
                    self.poc_increment = One;
                    self.expected_poc /= 2;

                    if self.reordered_frames != 0 {
                        let increase = self.reordered_frames;
                        if (self.reordered_frames + increase) > MAX_REORDERED_FRAMES {
                            return Err(TooManyReorderedFrames(self.reordered_frames + increase));
                        }

                        self.reordered_frames += increase;
                        self.pause += increase;
                    }
                } else if self.au_count >= 2
                    && (poc % 4) == 0
                    && poc == (self.prev_poc + 4)
                    && self.prev_poc == (self.prev_prev_poc + 4)
                {
                    self.poc_increment = PocIncrement::Four;
                    self.expected_poc *= 2;
                }

                self.au_count += 1;
                self.prev_prev_poc = self.prev_poc;
                self.prev_poc = poc;
            }

            self.expected_poc += u32::from(self.poc_increment);
            self.expected_poc &= (1 << (log2_max_pic_order_cnt_lsb_minus4 + 4)) - 1;

            let diff = picture_order_count_diff(
                poc,
                self.expected_poc,
                log2_max_pic_order_cnt_lsb_minus4,
            )?;
            pts_dts_diff = i64::from(diff) / self.poc_increment;
        } else if !non_zero_nal_ref_id_found {
            let Some(prev_dts) = self.prev_dts else {
                return Ok((pts, true));
            };
            return Ok((prev_dts, false));
        } else {
            return Err(NoIdrOrNonIdr);
        }

        pts_dts_diff += self.reordered_frames;

        if pts_dts_diff > (2 * self.reordered_frames + 1) {
            let increase = pts_dts_diff - ((2 * self.reordered_frames) + 1);
            if (self.reordered_frames + increase) > MAX_REORDERED_FRAMES {
                return Err(TooManyReorderedFrames(self.reordered_frames + increase));
            }

            self.reordered_frames += increase;
            self.pause += increase;
            pts_dts_diff += increase;
        } else if pts_dts_diff < 0 {
            let increase = -pts_dts_diff;
            if (self.reordered_frames + increase) > MAX_REORDERED_FRAMES {
                return Err(TooManyReorderedFrames(self.reordered_frames + increase));
            }

            self.reordered_frames += increase;
            self.pause += increase;
            pts_dts_diff += increase;
        }

        if self.pause > 0 {
            self.pause -= 1;
            let Some(prev_dts) = self.prev_dts else {
                return Ok((pts, true));
            };
            return Ok((prev_dts + 90, true));
        }

        let Some(prev_dts) = self.prev_dts else {
            return Ok((pts, true));
        };

        let dts = prev_dts + (pts - prev_dts) / (pts_dts_diff + 1);
        Ok((dts, false))
    }
}

fn picture_order_count_diff(
    a: u32,
    b: u32,
    log2_max_pic_order_cnt_lsb_minus4: u8,
) -> Result<i32, std::num::TryFromIntError> {
    let max = u32::try_from(1 << (log2_max_pic_order_cnt_lsb_minus4 + 4))?;
    let d = a.wrapping_sub(b) & (max - 1);
    if d > (max / 2) {
        Ok(i32::try_from(d)? - i32::try_from(max)?)
    } else {
        Ok(i32::try_from(d)?)
    }
}

// Read the Picture Order Count in a `SliceLayerWithoutPartitioningNonIdr` nalu.
fn get_picture_order_count(
    nal: &[u8],
    idr: bool,
    log2_max_frame_num_minus4: u8,
    log2_max_pic_order_cnt_lsb_minus4: u8,
) -> Result<u32, H264DtsExtractorError> {
    use H264DtsExtractorError::BitReader;
    let mut r = h264_reader::rbsp::BitReader::new(ByteReader::skipping_h264_header(nal));
    r.read_ue("first_mb_in_slice").map_err(BitReader)?;
    r.read_ue("slice type").map_err(BitReader)?;
    r.read_ue("pic_parameter_set_id").map_err(BitReader)?;
    r.read::<u32>((log2_max_frame_num_minus4 + 4).into(), "frame_num")
        .map_err(BitReader)?;

    if idr {
        r.read_ue("idr_pic_id").map_err(BitReader)?;
    }

    let pic_order_cnt_lsb: u32 = r
        .read(
            (log2_max_pic_order_cnt_lsb_minus4 + 4).into(),
            "pic_order_cnt_lsb",
        )
        .map_err(H264DtsExtractorError::BitReader)?;

    Ok(pic_order_cnt_lsb)
}

fn get_unit_type(nal: &[u8]) -> Result<UnitType, H264DtsExtractorError> {
    use H264DtsExtractorError::*;
    Ok(NalHeader::new(*nal.first().ok_or(NoHeader)?)
        .map_err(ParseNalHeader)?
        .nal_unit_type())
}

#[derive(Copy, Clone, Debug)]
enum PocIncrement {
    One,
    Two,
    Four,
}

impl From<PocIncrement> for u32 {
    fn from(value: PocIncrement) -> Self {
        match value {
            PocIncrement::One => 1,
            PocIncrement::Two => 2,
            PocIncrement::Four => 4,
        }
    }
}

impl AddAssign<PocIncrement> for u32 {
    fn add_assign(&mut self, rhs: PocIncrement) {
        match rhs {
            PocIncrement::One => *self += 1,
            PocIncrement::Two => *self += 2,
            PocIncrement::Four => *self += 4,
        };
    }
}

impl Mul<PocIncrement> for i64 {
    type Output = i64;

    fn mul(self, rhs: PocIncrement) -> Self::Output {
        match rhs {
            PocIncrement::One => self,
            PocIncrement::Two => self * 2,
            PocIncrement::Four => self * 4,
        }
    }
}

impl Div<PocIncrement> for i64 {
    type Output = i64;

    fn div(self, rhs: PocIncrement) -> Self::Output {
        match rhs {
            PocIncrement::One => self,
            PocIncrement::Two => self / 2,
            PocIncrement::Four => self / 4,
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use test_case::test_case;

    struct Sample<'a> {
        nalus: &'a [&'a [u8]],
        dts: i64,
        pts: i64,
    }

    #[test_case(
        &[
            Sample{
                nalus: &[
                    // SPS.
                    &[
                        0x67, 0x64, 0x00, 0x28, 0xac, 0xd9, 0x40, 0x78,
                        0x02, 0x27, 0xe5, 0x84, 0x00, 0x00, 0x03, 0x00,
                        0x04, 0x00, 0x00, 0x03, 0x00, 0xf0, 0x3c, 0x60,
                        0xc6, 0x58,
                    ],
                    &[0x65, 0x88, 0x84, 0x00, 0x33, 0xff], // IDR
                ],
                dts: 56890 + 0,
                pts: 56890 + 0,
            },
            Sample{
                nalus: &[&[0x41, 0x9a, 0x21, 0x6c, 0x45, 0xff]],
                dts: 56890 + 3000,
                pts: 56890 + 3000,
            },
            Sample{
                nalus: &[&[0x41, 0x9a, 0x42, 0x3c, 0x21, 0x93]],
                dts: 56890 + 6000,
                pts: 56890 + 6000,
            },
            Sample{
                nalus: &[&[0x41, 0x9a, 0x63, 0x49, 0xe1, 0x0f]],
                dts: 56890 + 9000,
                pts: 56890 + 9000,
            },
            Sample{
                nalus: &[&[0x41, 0x9a, 0x86, 0x49, 0xe1, 0x0f]],
                dts: 56890 + 9090,
                pts: 56890 + 18000,
            },
            Sample{
                nalus: &[&[0x41, 0x9e, 0xa5, 0x42, 0x7f, 0xf9]],
                dts: 56890 + 12045,
                pts: 56890 + 15000,
            },
            Sample{
                nalus: &[&[0x01, 0x9e, 0xc4, 0x69, 0x13, 0xff]],
                dts: 56890 + 12135,
                pts: 56890 + 12000,
            },
            Sample{
                nalus: &[&[0x41, 0x9a, 0xc8, 0x4b, 0xa8, 0x42]],
                dts: 56890 + 15101,
                pts: 56890 + 24000,
            },
            Sample{
                nalus: &[
                    // IDR
                    &[0x65, 0x88, 0x84, 0x00, 0x33, 0xff],
                ],
                dts: 56890 + 18067,
                pts: 56890 + 24000,
            },
        ]; "with timing info"
    )]
    #[test_case(
        &[
            Sample{
                nalus: &[
                    // SPS.
                    &[
                        0x27, 0x64, 0x00, 0x20, 0xac, 0x52, 0x18, 0x0f,
                        0x01, 0x17, 0xef, 0xff, 0x00, 0x01, 0x00, 0x01,
                        0x6a, 0x02, 0x02, 0x03, 0x6d, 0x85, 0x6b, 0xde,
                        0xf8, 0x08,
                    ],
                    &[0x25, 0xb8, 0x08, 0x02, 0x1f, 0xff], // IDR
                ],
                dts: 35050 + 0,
                pts: 35050 + 0,
            },
            Sample{
                nalus: &[&[0x21, 0xe1, 0x05, 0xc7, 0x38, 0xbf]],
                dts: 35050 + 1500,
                pts: 35050 + 1500,
            },
            Sample{
                nalus: &[&[0x21, 0xe2, 0x09, 0xa1, 0xce, 0x0b]],
                dts: 35050 + 3000,
                pts: 35050 + 3000,
            },
            Sample{
                nalus: &[&[0x21, 0xe3, 0x0d, 0xb1, 0xce, 0x02]],
                dts: 35050 + 4500,
                pts: 35050 + 4500,
            },
            Sample{
                nalus: &[&[0x21, 0xe4, 0x11, 0x90, 0x73, 0x80]],
                dts: 35050 + 6000,
                pts: 35050 + 6000,
            },
            Sample{
                nalus: &[&[0x21, 0xe5, 0x19, 0x0e, 0x70, 0x01]],
                dts: 35050 + 6045,
                pts: 35050 + 6090,
            },
            Sample{
                nalus: &[&[0x01, 0xa9, 0x85, 0x7c, 0x93, 0xff]],
                dts: 35050 + 6135,
                pts: 35050 + 7500,
            },
            Sample{
                nalus: &[&[0x21, 0xe6, 0x1d, 0x0e, 0x70, 0x01]],
                dts: 35050 + 8317,
                pts: 35050 + 10500,
            },
            Sample{
                nalus: &[&[0x21, 0xe7, 0x21, 0x0e, 0x70, 0x01]],
                dts: 35050 + 10158,
                pts: 35050 + 12000,
            },
            Sample{
                nalus: &[&[0x21, 0xe8, 0x25, 0x0e, 0x70, 0x01]],
                dts: 35050 + 11829,
                pts: 35050 + 13500,
            },
            Sample{
                nalus: &[&[0x21, 0xe9, 0x29, 0x0e, 0x70, 0x01]],
                dts: 35050 + 13414,
                pts: 35050 + 15000,
            },
            Sample{
                nalus: &[&[0x21, 0xea, 0x31, 0x0e, 0x70, 0x01]],
                dts: 35050 + 14942,
                pts: 35050 + 18000,
            },
            Sample{
                nalus: &[&[0x01, 0xaa, 0xcb, 0x7c, 0x93, 0xff]],
                dts: 35050 + 16500,
                pts: 35050 + 16500,
            },
        ]; "no timing info"
    )]
    #[test_case(
        &[
            Sample{
                // IDR.
                nalus: &[
                    // SPS.
                    &[
                        0x67, 0x64, 0x00, 0x2a, 0xac, 0x2c, 0x6a, 0x81,
                        0xe0, 0x08, 0x9f, 0x96, 0x6e, 0x02, 0x02, 0x02,
                        0x80, 0x00, 0x03, 0x84, 0x00, 0x00, 0xaf, 0xc8,
                        0x02,
                    ],
                    &[0x65, 0xb8, 0x00, 0x00, 0x0b, 0xc8, 0x00, 0x00, 0x01]], // IDR.
                dts: 5490,
                pts: 5490,
            },
            Sample{
                nalus: &[&[0x61, 0xe0, 0x20, 0x00, 0x39, 0x37]],
                dts: 9090,
                pts: 9090,
            },
            Sample{
                nalus: &[&[0x61, 0xe0, 0x40, 0x00, 0x59, 0x37]],
                dts: 12690,
                pts: 12690,
            },
            Sample{
                nalus: &[&[0x61, 0xe0, 0x60, 0x00, 0x79, 0x37]],
                dts: 16290,
                pts: 16290,
            },
        ]; "poc increment = 1"
    )]
    #[test_case(
        &[
            Sample{
                nalus: &[
                    // SPS.
                    &[
                        0x27, 0x64, 0x00, 0x2a, 0xac, 0x2d, 0x90, 0x07,
                        0x80, 0x22, 0x7e, 0x5c, 0x05, 0xa8, 0x08, 0x08,
                        0x0a, 0x00, 0x00, 0x03, 0x00, 0x02, 0x00, 0x00,
                        0x03, 0x00, 0xf1, 0xd0, 0x80, 0x04, 0xc4, 0x80,
                        0x00, 0x09, 0x89, 0x68, 0xde, 0xf7, 0xc1, 0xda,
                        0x1c, 0x31, 0x92,
                    ],
                    &[0x65, 0x88, 0x80, 0x14, 0x3, 0xff, 0xde, 0x8, 0xe4, 0x74], // IDR.
                ],
                dts: 172440,
                pts: 172440,
            },
            Sample{
                // B-frame.
                nalus: &[&[0x41, 0x9e, 0x3, 0xe4, 0x3f, 0x0, 0x0, 0x3, 0x0, 0x0]],
                dts: 172530,
                pts: 169470,
            },
            Sample{
                // B-frame.
                nalus: &[&[0x1, 0x9e, 0x5, 0xd4, 0x7f, 0x0, 0x0, 0x3, 0x0, 0x0]],
                dts: 172620,
                pts: 168030,
            },
            Sample{
                // P-frame.
                nalus: &[&[0x1, 0x9e, 0x5, 0xf4, 0x7f, 0x0, 0x0, 0x3, 0x0, 0x0]],
                dts: 172710,
                pts: 170910,
            },
            Sample{
                // P-frame.
                nalus: &[&[0x1, 0x9e, 0x5, 0xf4, 0x7f, 0x0, 0x0, 0x3, 0x0, 0x0]],
                dts: 172800,
                pts: 178470,
            },
        ]; "B-frames after IDR (OBS 29.1.3 QuickSync on Windows)"
    )]
    #[test_case(
        &[
            Sample{
                nalus: &[
                    // SPS.
                    &[
                        0x67, 0x4d, 0x40, 0x28, 0xab, 0x60, 0x3c, 0x02,
                        0x23, 0xef, 0x01, 0x10, 0x00, 0x00, 0x03, 0x00,
                        0x10, 0x00, 0x00, 0x03, 0x03, 0x2e, 0x94, 0x00,
                        0x35, 0x64, 0x06, 0xb2, 0x85, 0x08, 0x0e, 0xe2,
                        0xc5, 0x22, 0xc0,
                    ],
                    &[0x68, 0xca, 0x41, 0xf2], // PPS.
                    &[0x6, 0x0, 0x6, 0x85, 0x7e, 0x40, 0x0, 0x0, 0x10, 0x1], // SEI.
                    &[0x65, 0x88, 0x82, 0x80, 0x1f, 0xff, 0xfb, 0xf0, 0xa2, 0x88], // IDR.
                    &[0x6, 0x1, 0x2, 0x4, 0x24, 0x80], // SEI.
                    &[0x41, 0x9a, 0xc, 0x1c, 0x2f, 0xe4, 0xed, 0x23, 0xb5, 0x63], // non-IDR.
                ],
                dts: 0,
                pts: 0,
            },
            Sample{
                nalus: &[
                    &[0x6, 0x1, 0x2, 0x8, 0x14, 0x80], // SEI.
                    &[0x41, 0x9a, 0x18, 0x2a, 0x1f, 0xeb, 0x2f, 0xa2, 0xb1, 0x7e], // non-IDR.
                ],
                dts: 3600,
                pts: 3600,
            },
            Sample{
                nalus: &[
                    &[0x6, 0x1, 0x2, 0xc, 0x24, 0x80], // SEIMore actions.
                    &[0x41, 0x9a, 0x1c, 0x3a, 0xf, 0xfa, 0x55, 0xc2, 0x55, 0xea], // non-IDR.
                ],
                dts: 7200,
                pts: 7200,
            },
        ]; "mbs_only_flag = 0"
    )]
    #[test_case(
        &[
            Sample{
                nalus: &[
                    &[0x67, 0x42, 0xc0, 0x1e, 0x8c, 0x8d, 0x40, 0x50, 0x17, 0xfc, 0xb0, 0x0f, 0x08, 0x84, 0x6a], // SPS.
                    &[0x68, 0xce, 0x3c, 0x80], // PPS.
                    &[0x65, 0x88, 0x80, 0x14, 0x3, 0x00, 0x00, 0x01, 0x00, 0x00], // IDR.
                ],
                dts: 0,
                pts: 0,
            },
            Sample{
                // non-IDR.
                nalus: &[&[0x61, 0x00, 0xf0, 0xe0, 0x00, 0x40, 0x00, 0xbe, 0x47, 0x9b]],
                dts: 3600,
                pts: 3600,
            },
        ]; "Log2MaxPicOrderCntLsbMinus4 = 12"
    )]
    #[test_case(
        &[
            Sample{
                nalus: &[
                    // SPS.
                    &[
                        0x27, 0x64, 0x00, 0x2a, 0xac, 0x2d, 0x90, 0x07,
                        0x80, 0x22, 0x7e, 0x5c, 0x05, 0xa8, 0x08, 0x08,
                        0x0a, 0x00, 0x00, 0x03, 0x00, 0x02, 0x00, 0x00,
                        0x03, 0x00, 0xf1, 0xd0, 0x80, 0x04, 0xc4, 0x80,
                        0x00, 0x09, 0x89, 0x68, 0xde, 0xf7, 0xc1, 0xda,
                        0x1c, 0x31, 0x92,
                    ],
                    &[0x68, 0xca, 0x41, 0xf2], // PPS.
                    &[0x6, 0x0, 0x6, 0x85, 0x7e, 0x40, 0x0, 0x0, 0x10, 0x1], // SEI.
                    &[0x65, 0x88, 0x82, 0x80, 0x1f, 0xff, 0xfb, 0xf0, 0xa2, 0x88], // IDR.
                    &[0x6, 0x1, 0x2, 0x4, 0x24, 0x80], // SEI.
                    &[0x41, 0x9a, 0xc, 0x1c, 0x2f, 0xe4, 0xed, 0x23, 0xb5, 0x63], // non-IDR.
                ],
                dts: 0,
                pts: 0,
            },
            Sample{
                // SEI.
                nalus: &[&[0x6, 0x1, 0x2, 0x8, 0x14, 0x80]],
                dts: 0,
                pts: 0,
            },
            Sample{
                // non-IDR
                nalus: &[&[0x61, 0x00, 0xf0, 0xe0, 0x00, 0x40, 0x00, 0xbe, 0x47, 0x9b]],
                dts: 3600,
                pts: 3600,
            },
            Sample{
                // SEI.
                nalus: &[&[0x6, 0x1, 0x2, 0x8, 0x14, 0x80]],
                dts: 3600,
                pts: 7200,
            },
        ]; "issue mediamtx/3614 (only SEI received)"
    )]
    #[test_case(
        &[
            Sample{
                nalus: &[
                    // SPS.
                    &[
					    0x67, 0x42, 0x80, 0x28, 0x8c, 0x8d, 0x40, 0x5a,
						0x09, 0x22,
                    ],
                    // PPS.
                    &[
                        0x68, 0xce, 0x3c, 0x80,
                    ],
                    // IDR.
                    &[
                        0x65, 0xb8, 0x00, 0x0c, 0xa2, 0x40, 0x33, 0x93,
						0x14, 0x00, 0x04, 0x1a, 0x6d, 0x6d, 0x6d, 0x6d,
						0x6d, 0x6d, 0x5d, 0xaa, 0xb5, 0xb5, 0xb5, 0xb5,
						0xb5, 0xb5, 0xb5, 0xb5, 0xb5, 0xb5, 0xb5, 0xb5,
						0xb5, 0xb5, 0x76, 0xb6, 0xb6, 0xb6, 0xaa, 0xd6,
						0xd6, 0xd6, 0xd6, 0xd6, 0xd6, 0xd6, 0xd6, 0xd6,
						0xd6, 0xd6, 0xd6, 0xd6, 0xd6, 0xd6, 0xd6, 0xd5,
						0xda, 0xda, 0xaa, 0x7a, 0x7a, 0x7a, 0x7a, 0x7a,
						0x79, 0x1e, 0xde, 0xde, 0xde, 0xde, 0xde, 0xde,
						0xde, 0xde, 0xde, 0xde, 0xde, 0xde, 0xde, 0xde,
						0xde, 0xde, 0xde, 0xde, 0xde, 0xde, 0xde, 0xde,
						0xde, 0xde, 0xde, 0xde, 0xde, 0xde, 0xde, 0xde,
						0xde, 0xde, 0xde, 0xde,
                    ],
                ],
                dts: 0,
                pts: 0,
            },
            Sample{
                nalus: &[&[
                    0x41, 0xe0, 0x00, 0x65, 0x12, 0x80, 0xce, 0x78,
                    0x16, 0x00, 0x99, 0xff, 0xff, 0xff, 0xe0, 0xe4,
                    0x1a, 0x7f, 0xff, 0xff, 0xea, 0x11, 0x01, 0x01,
                    0xff, 0xff, 0xfc, 0x20, 0x08, 0x3f, 0xff, 0xff,
                    0xfc, 0x0f, 0x22, 0x7f, 0xff, 0xff, 0xff, 0xff,
                    0xff, 0xff, 0xff, 0xff, 0xb8, 0x60, 0x04, 0x87,
                    0x02, 0xc8, 0x18, 0x38, 0x60, 0x04, 0x87, 0x03,
                    0x00, 0x35, 0xa8, 0x16, 0x40, 0x9b, 0x04, 0xd0,
                    0x11, 0x00, 0x24, 0x38, 0x11, 0x01, 0x6c, 0x16,
                    0x41, 0x60, 0x2c, 0x82, 0xd8, 0x2c, 0x05, 0x90,
                    0x5b, 0x05, 0x80, 0xb2, 0x0b, 0x60, 0xb0, 0x16,
                    0x41, 0x6c, 0x16, 0x02, 0xc8, 0x2d, 0x82, 0xc0,
                    0x59, 0x05, 0xb0, 0x58,
                ]],
                dts: 10000,
                pts: 10000,
            },
            Sample{
                nalus: &[&[
                    0x41, 0xe0, 0x00, 0xa5, 0x13, 0x00, 0xce, 0xf0,
                    0x2c, 0x70, 0x20, 0x01, 0x43, 0xc0, 0x8b, 0xc3,
                    0x01, 0x99, 0x60, 0x80, 0x04, 0x07, 0x06, 0x39,
                    0xe0, 0x80, 0x04, 0x04, 0x37, 0x80, 0x90, 0xe4,
                    0x06, 0x9c, 0xa0, 0x23, 0x60, 0x06, 0x25, 0x80,
                ]],
                dts: 14400,
                pts: 14400,
            },
        ]; "issue mediamtx/3094 (non-zero IDR POC)"
    )]
    #[test_case(
        &[
            Sample{
                nalus: &[
                    // SPS.
                    &[
                        0x27, 0x64, 0x00, 0x28, 0xac, 0x56, 0x50, 0x1e,
                        0x00, 0x89, 0xf9, 0x66, 0xa0, 0x20, 0x20, 0x20,
                        0x40,
                    ],
                    // PPS.
                    &[
                        0x28, 0xee, 0x3c, 0xb0
                    ],
                    // IDR.
                    &[
                        0x65, 0xb8, 0x20, 0x1f, 0xde, 0x08, 0xe5, 0x4c,
                        0xff, 0x82, 0xcc, 0x1e, 0x9b, 0x50, 0xdb, 0xb3,
                        0x15, 0xf2, 0xac, 0x66,
                    ],
                    &[
                        0x0c, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff,
                    ],
                ],
                dts: 0,
                pts: 0,
            },
            Sample{
                nalus: &[
                    &[
                        0x41, 0xe1, 0x10, 0x7f, 0xcd, 0xf4, 0xe3, 0x3d,
                        0x20, 0x01, 0x62, 0x49, 0x60, 0x00, 0x00, 0x03,
                        0x00, 0x00, 0x03, 0x00,
                    ],
                    &[
                        0x0c, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff,
                    ],
                ],
                dts: 6000,
                pts: 12000,
            },
            Sample{
                nalus: &[
                    &[
                        0x41, 0xa8, 0x82, 0x87, 0xff, 0xee, 0x4d, 0x5c,
                        0x1a, 0x30, 0x00, 0x00, 0x03, 0x00, 0x00, 0x03,
                        0x00, 0x00, 0x03, 0x00,
                    ],
                    &[
                        0x0c, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff,
                    ],
                ],
                dts: 6090,
                pts: 6000,
            },
            Sample{
                nalus: &[
                    &[
                        0x01, 0xa8, 0xc1, 0x88, 0x8f, 0xeb, 0xea, 0x6b,
                        0x80, 0x00, 0x00, 0x03, 0x00, 0x00, 0x03, 0x00,
                        0x00, 0x03, 0x00, 0x00,
                    ],
                    &[
                        0x0c, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff,
                    ],
                ],
                dts: 6180,
                pts: 3000,
            },
            Sample{
                nalus: &[
                    &[
                        0x01, 0xa8, 0xc3, 0x88, 0x8f, 0xf5, 0x4b, 0xa1,
                        0xc0, 0x00, 0x00, 0x03, 0x00, 0x00, 0x03, 0x00,
                        0x00, 0x03, 0x00, 0x00,
                    ],
                    &[
                        0x0c, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff,
                    ],
                ],
                dts: 7590,
                pts: 9000,
            },
            Sample{
                nalus: &[
                    &[
                        0x41, 0xe3, 0x21, 0xa2, 0x3f, 0xcd, 0x95, 0x8a,
                        0xc0, 0x19, 0xa0, 0x00, 0x00, 0x03, 0x00, 0x00,
                        0x03, 0x00, 0x00, 0x03,
                    ],
                    &[
                        0x0c, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                        0xff, 0xff, 0xff, 0xff,
                    ],
                ],
                dts: 10325,
                pts: 24000,
            },
        ]; "issue mediamtx/4892 (poc increment = 1 after reordered frames)"
    )]
    #[test_case(
        &[
            Sample{
                nalus: &[
                    // SPS.
                    &[
						0x27, 0x64, 0x00, 0x28, 0xac, 0x1b, 0x1a, 0x80,
						0x78, 0x02, 0x25, 0xe5, 0x40,
                    ],
                    // PPS.
                    &[
						0x28, 0xee, 0x04, 0x62, 0xc0,
                    ],
                    // IDR.
                    &[

						0x25, 0xb8, 0x00, 0x00, 0x32, 0x00, 0x00, 0x3f,
						0xba, 0x12, 0xe0, 0x6f, 0xff, 0x0d, 0x7f, 0x39,
						0x49, 0x90, 0x23, 0x0c,
                    ],
                ],
                dts: 0,
                pts: 0,
            },
            Sample{
                nalus: &[&[
                    0x21, 0xe0, 0x00, 0x20, 0x00, 0x82, 0x23, 0x03,
                    0x3d, 0xd8, 0x10, 0xa1, 0x2a, 0x8b, 0x33, 0x53,
                    0xd2, 0x79, 0x18, 0x1d,
                ]],
                dts: 5400,
                pts: 10800,
            },
            Sample{
                nalus: &[&[
                    0x21, 0xe0, 0x00, 0x40, 0x01, 0x02, 0x6f, 0x0a,
                    0x14, 0x6a, 0x38, 0x00, 0x00, 0x03, 0x00, 0x00,
                    0x19, 0x9d, 0x46, 0xe2,
                ]],
                dts: 90000,
                pts: 90000,
            },
            Sample{
                nalus: &[&[
                    0x21, 0xe0, 0x00, 0x60, 0x01, 0x82, 0xbf, 0x05,
                    0x43, 0x10, 0x00, 0x00, 0x03, 0x00, 0x00, 0x0a,
                    0x03, 0x56, 0x41, 0xfe,
                ]],
                dts: 100800,
                pts: 100800,
            },
        ]; "issue mediamtx/4617 (poc increment = 4)"
    )]

    fn test_dts_extractor(sequence: &[Sample]) {
        let sps = sequence[0].nalus[0];

        let mut extractor = H264DtsExtractor::new();
        let sequence = sequence.into_iter().map(|v| v.to_owned());
        for sample in sequence {
            let nals: Vec<u8> = sample
                .nalus
                .iter()
                .flat_map(|nal| {
                    let len: [u8; 4] = (nal.len() as u32).to_be_bytes();
                    [&len, *nal].concat()
                })
                .collect();

            let dts = extractor.extract(&sps, &nals, sample.pts).unwrap();
            assert_eq!(sample.dts, dts);
        }
    }
}
