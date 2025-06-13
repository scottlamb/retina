// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

// https://github.com/bluenviron/mediacommon/blob/051b50768b457dc33b59bc727b6148855bbbbb88/pkg/codecs/h264/dts_extractor.go

use h264_reader::{
    nal::{
        sps::{FrameMbsFlags, PicOrderCntType, SeqParameterSet},
        NalHeader, NalHeaderError, UnitType,
    },
    rbsp::{BitRead, BitReaderError, ByteReader},
};
use std::ops::{AddAssign, Mul};
use thiserror::Error;

pub(crate) struct NalUnitIter<'a> {
    remaining: &'a [u8],
}

impl<'a> NalUnitIter<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Self { remaining: data }
    }
}

impl<'a> Iterator for NalUnitIter<'a> {
    type Item = NalRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining.is_empty() {
            return None;
        }

        let (nal_len, remaining) = self.remaining.split_at(4);
        let nal_len = u32::from_be_bytes(nal_len.try_into().expect("u32 should be 4 bytes"));
        let (nalu, remaining) = remaining.split_at(
            nal_len
                .try_into()
                .expect("usize should be convertible from u32"),
        );
        self.remaining = remaining;

        Some(NalRef(nalu))
    }
}

pub(crate) struct NalRef<'a>(&'a [u8]);

#[derive(Debug, Error)]
pub(crate) enum DtsExtractorError {
    #[error("first call must be IDR")]
    FirstCallNotIDR,

    #[error("{0}")]
    FromInt(#[from] std::num::TryFromIntError),

    #[error("too many reordered frames ({0})")]
    TooManyReorderedFrames(i64),

    #[error("access unit doesn't contain an IDR or non-IDR NALU")]
    NoIdrOrNonIdr,

    #[error("pic_order_cnt_type = 1 is not supported yet")]
    PicOrderCntType1Unsupported,

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
pub(crate) struct DtsExtractor {
    prev_dts: Option<i64>,
    expected_poc: u32,
    reordered_frames: i64,
    pause_dts: i64,
    poc_increment: PocIncrement,
}

impl Default for DtsExtractor {
    fn default() -> Self {
        Self::new()
    }
}

const MAX_REORDERED_FRAMES: i64 = 10;

impl DtsExtractor {
    pub fn new() -> Self {
        Self {
            prev_dts: None,
            expected_poc: 0,
            reordered_frames: 0,
            pause_dts: 0,
            poc_increment: PocIncrement::Two,
        }
    }

    // Extracts the DTS of an access unit. The first call must be an IDR.
    pub fn extract(
        &mut self,
        sps: &SeqParameterSet,
        au: NalUnitIter,
        pts: i64,
    ) -> Result<i64, DtsExtractorError> {
        use DtsExtractorError::*;

        let (dts, skip_checks) = self.extract_inner(sps, au, pts)?;
        if !skip_checks && dts > pts {
            return Err(DtsGreaterThanPts(dts, pts));
        }
        if let Some(prev_dts) = self.prev_dts {
            if dts < prev_dts {
                return Err(DtsNotIncreasing(prev_dts, dts));
            }
        }
        self.prev_dts = Some(dts);
        Ok(dts)
    }

    fn extract_inner(
        &mut self,
        sps: &SeqParameterSet,
        au: NalUnitIter,
        pts: i64,
    ) -> Result<(i64, bool), DtsExtractorError> {
        use DtsExtractorError::*;

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
            non_zero_nal_ref_id_found = non_zero_nal_ref_id_found || ((nalu.0[0] & 0x60) > 0);
            match get_unit_type(nalu.0)? {
                UnitType::SliceLayerWithoutPartitioningNonIdr => non_idr = Some(nalu),
                UnitType::SliceLayerWithoutPartitioningIdr => idr = Some(nalu),
                UnitType::SeqParameterSet => {
                    // Reset state.
                    self.reordered_frames = 0;
                    self.poc_increment = PocIncrement::Two;
                }
                _ => {}
            }
        }

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

        let FrameMbsFlags::Frames = sps.frame_mbs_flags else {
            return Ok((pts, false));
        };

        // Implicit processing of PicOrderCountType 0.
        if let Some(idr) = idr {
            self.pause_dts = 0;

            self.expected_poc = get_picture_order_count(
                idr,
                sps.log2_max_frame_num_minus4,
                log2_max_pic_order_cnt_lsb_minus4,
                true,
            )?;

            let Some(prev_dts) = self.prev_dts else {
                return Ok((pts, false));
            };
            if self.reordered_frames == 0 {
                return Ok((pts, false));
            }

            let dts = prev_dts + (pts - prev_dts) / (self.reordered_frames + 1);
            return Ok((dts, false));
        }

        let Some(prev_dts) = self.prev_dts else {
            return Err(FirstCallNotIDR);
        };
        if let Some(non_idr) = non_idr {
            self.expected_poc += u32::from(self.poc_increment);
            self.expected_poc &= (1 << (log2_max_pic_order_cnt_lsb_minus4 + 4)) - 1;

            if self.pause_dts > 0 {
                self.pause_dts -= 1;
                return Ok((prev_dts + 90, true));
            }

            let poc = get_picture_order_count(
                non_idr,
                sps.log2_max_frame_num_minus4,
                log2_max_pic_order_cnt_lsb_minus4,
                false,
            )?;

            let poc_is_odd = (poc % 2) != 0;
            if matches!(self.poc_increment, PocIncrement::Two) && poc_is_odd {
                self.poc_increment = PocIncrement::One;
                self.expected_poc /= 2;
            }

            let mut poc_diff = i64::from(get_picture_order_count_diff(
                poc,
                self.expected_poc,
                log2_max_pic_order_cnt_lsb_minus4,
            )?);
            if let PocIncrement::Two = self.poc_increment {
                poc_diff /= 2;
            };
            let limit = -(self.reordered_frames + 1);

            // This happens when there are B-frames immediately following an IDR frame.
            if poc_diff < limit {
                let increase = limit - poc_diff;
                if (self.reordered_frames + increase) > MAX_REORDERED_FRAMES {
                    return Err(TooManyReorderedFrames(self.reordered_frames + increase));
                }

                self.reordered_frames += increase;
                self.pause_dts = increase;
                return Ok((prev_dts + 90, true));
            }

            if poc_diff == limit {
                return Ok((pts, false));
            }

            if poc_diff > self.reordered_frames {
                let increase = poc_diff - self.reordered_frames;
                if (self.reordered_frames + increase) > MAX_REORDERED_FRAMES {
                    return Err(TooManyReorderedFrames(self.reordered_frames + increase));
                }

                self.reordered_frames += increase;
                self.pause_dts = increase - 1;
                return Ok((prev_dts + 90, false));
            }

            let dts_diff = pts - prev_dts;
            let dts = prev_dts + dts_diff / (poc_diff + self.reordered_frames + 1);
            return Ok((dts, false));
        }

        if !non_zero_nal_ref_id_found {
            return Ok((prev_dts, false));
        }

        Err(NoIdrOrNonIdr)
    }
}

fn get_picture_order_count_diff(
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
    nal: NalRef,
    log2_max_frame_num_minus4: u8,
    log2_max_pic_order_cnt_lsb_minus4: u8,
    idr: bool,
) -> Result<u32, DtsExtractorError> {
    use DtsExtractorError::BitReader;
    let mut r = h264_reader::rbsp::BitReader::new(ByteReader::new(nal.0));
    r.read_ue("first_mb_in_slice").map_err(BitReader)?;
    r.read_ue("slice type").map_err(BitReader)?;
    r.read_ue("pic_parameter_set_id").map_err(BitReader)?;
    r.read_u32((log2_max_frame_num_minus4 + 4).into(), "frame_num")
        .map_err(BitReader)?;

    if idr {
        r.read_ue("idr_pic_id").map_err(BitReader)?;
    }

    let pic_order_cnt_lsb: u32 = r
        .read_u32(
            (log2_max_pic_order_cnt_lsb_minus4 + 4).into(),
            "pic_order_cnt_lsb",
        )
        .map_err(DtsExtractorError::BitReader)?;

    Ok(pic_order_cnt_lsb)
}

fn get_unit_type(nal: &[u8]) -> Result<UnitType, DtsExtractorError> {
    use DtsExtractorError::*;
    Ok(NalHeader::new(*nal.first().ok_or(NoHeader)?)
        .map_err(ParseNalHeader)?
        .nal_unit_type())
}

#[derive(Copy, Clone, Debug)]
enum PocIncrement {
    One,
    Two,
}

impl From<PocIncrement> for u32 {
    fn from(value: PocIncrement) -> Self {
        match value {
            PocIncrement::One => 1,
            PocIncrement::Two => 2,
        }
    }
}

impl AddAssign<PocIncrement> for u32 {
    fn add_assign(&mut self, rhs: PocIncrement) {
        match rhs {
            PocIncrement::One => *self += 1,
            PocIncrement::Two => *self += 2,
        };
    }
}

impl Mul<PocIncrement> for i64 {
    type Output = i64;

    fn mul(self, rhs: PocIncrement) -> Self::Output {
        match rhs {
            PocIncrement::One => self,
            PocIncrement::Two => self * 2,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use h264_reader::rbsp::BitReader;
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
                dts: 3333333,
                pts: 3333333,
            },
            Sample{
                nalus: &[&[0x41, 0x9a, 0x21, 0x6c, 0x45, 0xff]],
                dts: 3666666,
                pts: 3666666,
            },
            Sample{
                nalus: &[&[0x41, 0x9a, 0x42, 0x3c, 0x21, 0x93]],
                dts: 4000000,
                pts: 4000000,
            },
            Sample{
                nalus: &[&[0x41, 0x9a, 0x63, 0x49, 0xe1, 0x0f]],
                dts: 4333333,
                pts: 4333333,
            },
            Sample{
                nalus: &[&[0x41, 0x9a, 0x86, 0x49, 0xe1, 0x0f]],
                dts: 4333423,
                pts: 5333333,
            },
            Sample{
                nalus: &[&[0x41, 0x9e, 0xa5, 0x42, 0x7f, 0xf9]],
                dts: 4333513,
                pts: 5000000,
            },
            Sample{
                nalus: &[&[0x01, 0x9e, 0xc4, 0x69, 0x13, 0xff]],
                dts: 4666666,
                pts: 4666666,
            },
            Sample{
                nalus: &[&[0x41, 0x9a, 0xc8, 0x4b, 0xa8, 0x42]],
                dts: 4999999,
                pts: 6000000,
            },
            Sample{
                nalus: &[
                    // IDR
                    &[0x65, 0x88, 0x84, 0x00, 0x33, 0xff],
                ],
                dts: 5333332,
                pts: 5999999,
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
                dts: 85000,
                pts: 85000,
            },
            Sample{
                nalus: &[&[0x21, 0xe1, 0x05, 0xc7, 0x38, 0xbf]],
                dts: 86666,
                pts: 86666,
            },
            Sample{
                nalus: &[&[0x21, 0xe2, 0x09, 0xa1, 0xce, 0x0b]],
                dts: 88333,
                pts: 88333,
            },
            Sample{
                nalus: &[&[0x21, 0xe3, 0x0d, 0xb1, 0xce, 0x02]],
                dts: 90000,
                pts: 90000,
            },
            Sample{
                nalus: &[&[0x21, 0xe4, 0x11, 0x90, 0x73, 0x80]],
                dts: 91666,
                pts: 91666,
            },
            Sample{
                nalus: &[&[0x21, 0xe5, 0x19, 0x0e, 0x70, 0x01]],
                dts: 91756,
                pts: 95000,
            },
            Sample{
                nalus: &[&[0x01, 0xa9, 0x85, 0x7c, 0x93, 0xff]],
                dts: 93333,
                pts: 93333,
            },
            Sample{
                nalus: &[&[0x21, 0xe6, 0x1d, 0x0e, 0x70, 0x01]],
                dts: 94999,
                pts: 96666,
            },
            Sample{
                nalus: &[&[0x21, 0xe7, 0x21, 0x0e, 0x70, 0x01]],
                dts: 96666,
                pts: 98333,
            },
            Sample{
                nalus: &[&[0x21, 0xe8, 0x25, 0x0e, 0x70, 0x01]],
                dts: 98333,
                pts: 100000,
            },
            Sample{
                nalus: &[&[0x21, 0xe9, 0x29, 0x0e, 0x70, 0x01]],
                dts: 99999,
                pts: 101666,
            },
            Sample{
                nalus: &[&[0x21, 0xea, 0x31, 0x0e, 0x70, 0x01]],
                dts: 101666,
                pts: 105000,
            },
            Sample{
                nalus: &[&[0x01, 0xaa, 0xcb, 0x7c, 0x93, 0xff]],
                dts: 103333,
                pts: 103333,
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
                dts: 61,
                pts: 61,
            },
            Sample{
                nalus: &[&[0x61, 0xe0, 0x20, 0x00, 0x39, 0x37]],
                dts: 101,
                pts: 101,
            },
            Sample{
                nalus: &[&[0x61, 0xe0, 0x40, 0x00, 0x59, 0x37]],
                dts: 141,
                pts: 141,
            },
            Sample{
                nalus: &[&[0x61, 0xe0, 0x60, 0x00, 0x79, 0x37]],
                dts: 181,
                pts: 181,
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
                dts: 1916000,
                pts: 1916000,
            },
            Sample{
                // b-frame.
                nalus: &[&[0x41, 0x9e, 0x3, 0xe4, 0x3f, 0x0, 0x0, 0x3, 0x0, 0x0]],
                dts: 1916090,
                pts: 1883000,
            },
            Sample{
                // b-frame.
                nalus: &[&[0x1, 0x9e, 0x5, 0xd4, 0x7f, 0x0, 0x0, 0x3, 0x0, 0x0]],
                dts: 1916180,
                pts: 1867000,
            },
            Sample{
                // p-frame.
                nalus: &[&[0x1, 0x9e, 0x5, 0xf4, 0x7f, 0x0, 0x0, 0x3, 0x0, 0x0]],
                dts: 1916270,
                pts: 1899000,
            },
            Sample{
                // p-frame.
                nalus: &[&[0x1, 0x9e, 0x5, 0xf4, 0x7f, 0x0, 0x0, 0x3, 0x0, 0x0]],
                dts: 1916360,
                pts: 1983000,
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
                dts: 40000,
                pts: 40000,
            },
            Sample{
                nalus: &[
                    &[0x6, 0x1, 0x2, 0xc, 0x24, 0x80], // SEIMore actions.
                    &[0x41, 0x9a, 0x1c, 0x3a, 0xf, 0xfa, 0x55, 0xc2, 0x55, 0xea], // non-IDR.
                ],
                dts: 80000,
                pts: 80000,
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
                dts: 40000,
                pts: 40000,
            },
        ]; "Log2MaxPicOrderCntLsbMinus4 = 12"
    )]
    #[test_case(
        &[
            Sample{
                nalus: &[
                    &[0x67, 0x42, 0x80, 0x28, 0x8c, 0x8d, 0x40, 0x5a, 0x09, 0x22],
                    &[0x68, 0xce, 0x3c, 0x80],
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
                dts: 120000,
                pts: 120000,
            },
            Sample{
                nalus: &[&[
						0x41, 0xe0, 0x00, 0xa5, 0x13, 0x00, 0xce, 0xf0,
						0x2c, 0x70, 0x20, 0x01, 0x43, 0xc0, 0x8b, 0xc3,
						0x01, 0x99, 0x60, 0x80, 0x04, 0x07, 0x06, 0x39,
						0xe0, 0x80, 0x04, 0x04, 0x37, 0x80, 0x90, 0xe4,
						0x06, 0x9c, 0xa0, 0x23, 0x60, 0x06, 0x25, 0x80,
                ]],
                dts: 160000,
                pts: 160000,
            },
        ]; "issue mediamtx/3094 (non-zero IDR POC)"
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
                dts: 40000,
                pts: 40000,
            },
            Sample{
                // SEI.
                nalus: &[&[0x6, 0x1, 0x2, 0x8, 0x14, 0x80]],
                dts: 40000,
                pts: 80000,
            },
        ]; "issue mediamtx/3614 Only SEI received"
    )]
    fn test_dts_extractor(sequence: &[Sample]) {
        let sps_rbsp = h264_reader::rbsp::decode_nal(&sequence[0].nalus[0]).unwrap();
        let sps = SeqParameterSet::from_bits(BitReader::new(&*sps_rbsp)).unwrap();

        let mut extractor = DtsExtractor::new();
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

            let dts = extractor
                .extract(&sps, NalUnitIter::new(&nals), sample.pts)
                .unwrap();
            assert_eq!(sample.dts, dts);
        }
    }
}
