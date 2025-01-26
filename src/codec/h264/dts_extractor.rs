// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

// https://github.com/bluenviron/gortsplib/blob/f0540b4eee760583b2d94f022674b0f3b0f8c8b0/pkg/codecs/h264/dts_extractor.go

use h264_reader::{
    nal::{
        sps::{FrameMbsFlags, PicOrderCntType, SeqParameterSet},
        NalHeader, NalHeaderError, UnitType,
    },
    rbsp::{BitRead, BitReader, BitReaderError, ByteReader},
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

    #[error("frame_mbs_only_flag = 0 is not supported")]
    FrameMbsNotSupported,

    #[error("POC not found")]
    PocNotFound,

    #[error("invalid POC")]
    PocInvalid,

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
    initialized: Option<Initialized>,
}

#[derive(Debug)]
struct Initialized {
    prev_dts: i64,
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

impl DtsExtractor {
    pub fn new() -> Self {
        Self { initialized: None }
    }

    // Extracts the DTS of a access unit. The first call must be an IDR.
    pub fn extract(
        &mut self,
        sps: &SeqParameterSet,
        is_random_access_point: bool,
        au: NalUnitIter,
        pts: i64,
    ) -> Result<i64, DtsExtractorError> {
        use DtsExtractorError::*;
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
            PicOrderCntType::TypeTwo => return Ok(pts),
        };

        if let Some(init) = &mut self.initialized {
            let dts = init.extract_inner(
                is_random_access_point,
                au,
                pts,
                sps.log2_max_frame_num_minus4,
                &sps.frame_mbs_flags,
                log2_max_pic_order_cnt_lsb_minus4,
            )?;
            if dts > pts {
                return Err(DtsGreaterThanPts(dts, pts));
            }
            if dts <= init.prev_dts {
                return Err(DtsNotIncreasing(init.prev_dts, dts));
            }
            init.prev_dts = dts;
            Ok(dts)
        } else {
            // First call.
            if !is_random_access_point {
                return Err(FirstCallNotIDR);
            }
            let dts = pts;
            self.initialized = Some(Initialized {
                prev_dts: dts,
                poc_increment: PocIncrement::Two,
                expected_poc: 0,
                reordered_frames: 0,
                pause_dts: 0,
            });
            Ok(dts)
        }
    }
}

impl Initialized {
    fn extract_inner(
        &mut self,
        is_random_access_point: bool,
        au: NalUnitIter,
        pts: i64,
        log2_max_frame_num_minus4: u8,
        frame_mbs_flags: &FrameMbsFlags,
        log2_max_pic_order_cnt_lsb_minus4: u8,
    ) -> Result<i64, DtsExtractorError> {
        if is_random_access_point {
            self.expected_poc = 0;
            self.reordered_frames = 0;
            self.pause_dts = 0;
            self.poc_increment = PocIncrement::Two;
            return Ok(pts);
        }

        self.expected_poc += self.poc_increment;
        self.expected_poc &= (1 << (log2_max_pic_order_cnt_lsb_minus4 + 4)) - 1;

        if self.pause_dts > 0 {
            self.pause_dts -= 1;
            return Ok(self.prev_dts + 1);
        }

        let poc = find_picture_order_count(
            au,
            log2_max_frame_num_minus4,
            frame_mbs_flags,
            log2_max_pic_order_cnt_lsb_minus4,
        )?;

        let poc_is_odd = (poc % 2) != 0;
        if matches!(self.poc_increment, PocIncrement::Two) && poc_is_odd {
            self.poc_increment = PocIncrement::One;
            self.expected_poc /= 2;
        }

        let poc_diff = i64::from(get_picture_order_count_diff(
            poc,
            self.expected_poc,
            log2_max_pic_order_cnt_lsb_minus4,
        )?);
        let poc_diff = poc_diff + self.reordered_frames * self.poc_increment;

        if poc_diff < 0 {
            return Err(DtsExtractorError::PocInvalid);
        }

        if poc_diff == 0 {
            return Ok(pts);
        }

        let reordered_frames = {
            match self.poc_increment {
                PocIncrement::One => poc_diff - self.reordered_frames,
                PocIncrement::Two => (poc_diff - self.reordered_frames * 2) / 2,
            }
        };

        if reordered_frames > self.reordered_frames {
            self.pause_dts = reordered_frames - self.reordered_frames - 1;
            self.reordered_frames = reordered_frames;
            return Ok(self.prev_dts + 1);
        }

        let dts_diff = pts - self.prev_dts;
        let dts_inc = match self.poc_increment {
            PocIncrement::One => dts_diff / (poc_diff + 1),
            PocIncrement::Two => dts_diff * 2 / (poc_diff + 2),
        };
        Ok(self.prev_dts + dts_inc)
    }
}

fn get_picture_order_count_diff(
    poc1: u32,
    poc2: u32,
    log2_max_pic_order_cnt_lsb_minus4: u8,
) -> Result<i32, std::num::TryFromIntError> {
    let cnt = log2_max_pic_order_cnt_lsb_minus4;
    let diff = i32::try_from(poc1)? - i32::try_from(poc2)?;
    Ok(if diff < -((1 << (cnt + 3)) - 1) {
        diff + (1 << (cnt + 4))
    } else if diff > ((1 << (cnt + 3)) - 1) {
        diff - (1 << (cnt + 4))
    } else {
        diff
    })
}

// Find the Picture Order Count from a `SliceLayerWithoutPartitioningNonIdr` nalu.
fn find_picture_order_count(
    au: NalUnitIter,
    log2_max_frame_num_minus4: u8,
    frame_mbs_flags: &FrameMbsFlags,
    log2_max_pic_order_cnt_lsb_minus4: u8,
) -> Result<u32, DtsExtractorError> {
    for nalu in au {
        if get_unit_type(nalu.0)? == UnitType::SliceLayerWithoutPartitioningNonIdr {
            let poc = get_picture_order_count(
                nalu,
                log2_max_frame_num_minus4,
                frame_mbs_flags,
                log2_max_pic_order_cnt_lsb_minus4,
            )?;
            return Ok(poc);
        }
    }
    Err(DtsExtractorError::PocNotFound)
}

// Read the Picture Order Count in a `SliceLayerWithoutPartitioningNonIdr` nalu.
fn get_picture_order_count(
    nal: NalRef,
    log2_max_frame_num_minus4: u8,
    frame_mbs_flags: &FrameMbsFlags,
    log2_max_pic_order_cnt_lsb_minus4: u8,
) -> Result<u32, DtsExtractorError> {
    let mut r = BitReader::new(ByteReader::new(nal.0));
    r.read_ue("first_mb_in_slice")
        .map_err(DtsExtractorError::BitReader)?;
    r.read_ue("slice type")
        .map_err(DtsExtractorError::BitReader)?;
    r.read_ue("pic_parameter_set_id")
        .map_err(DtsExtractorError::BitReader)?;
    r.read_u32((log2_max_frame_num_minus4 + 4).into(), "frame_num")
        .map_err(DtsExtractorError::BitReader)?;

    //if !sps.FrameMbsOnlyFlag {
    //	return 0, fmt.Errorf("frame_mbs_only_flag = 0 is not supported")
    //}
    let FrameMbsFlags::Frames = frame_mbs_flags else {
        return Err(DtsExtractorError::FrameMbsNotSupported);
    };

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

    struct SequenceSample<'a> {
        nalus: &'a [&'a [u8]],
        dts: i64,
        pts: i64,
    }

    #[test_case(
        &[
            0x67, 0x64, 0x00, 0x28, 0xac, 0xd9, 0x40, 0x78,
            0x02, 0x27, 0xe5, 0x84, 0x00, 0x00, 0x03, 0x00,
            0x04, 0x00, 0x00, 0x03, 0x00, 0xf0, 0x3c, 0x60,
            0xc6, 0x58,
        ],
        &[
            SequenceSample{
                nalus: &[
                    // IDR
                    &[0x65, 0x88, 0x84, 0x00, 0x33, 0xff],
                ],
                dts: 3333333,
                pts: 3333333,
            },
            SequenceSample{
                nalus: &[&[0x41, 0x9a, 0x21, 0x6c, 0x45, 0xff]],
                dts: 3336666,
                pts: 3336666,
            },
            SequenceSample{
                nalus: &[&[0x41, 0x9a, 0x42, 0x3c, 0x21, 0x93]],
                dts: 3340000,
                pts: 3340000,
            },
            SequenceSample{
                nalus: &[&[0x41, 0x9a, 0x63, 0x49, 0xe1, 0x0f]],
                dts: 3343333,
                pts: 3343333,
            },
            SequenceSample{
                nalus: &[&[0x41, 0x9a, 0x86, 0x49, 0xe1, 0x0f]],
                dts: 3343334,
                pts: 3353333,
            },
            SequenceSample{
                nalus: &[&[0x41, 0x9e, 0xa5, 0x42, 0x7f, 0xf9]],
                dts: 3343335,
                pts: 3350000,
            },
            SequenceSample{
                nalus: &[&[0x01, 0x9e, 0xc4, 0x69, 0x13, 0xff]],
                dts: 3346666,
                pts: 3346666,
            },
            SequenceSample{
                nalus: &[&[0x41, 0x9a, 0xc8, 0x4b, 0xa8, 0x42]],
                dts: 3349999,
                pts: 3360000,
            },
        ]; "with timing info"
    )]
    #[test_case(
        &[
            0x27, 0x64, 0x00, 0x20, 0xac, 0x52, 0x18, 0x0f,
            0x01, 0x17, 0xef, 0xff, 0x00, 0x01, 0x00, 0x01,
            0x6a, 0x02, 0x02, 0x03, 0x6d, 0x85, 0x6b, 0xde,
            0xf8, 0x08,
        ],
        &[
            SequenceSample{
                nalus: &[
                    // IDR
                    &[ 0x25, 0xb8, 0x08, 0x02, 0x1f, 0xff],
                ],
                dts: 85000,
                pts: 85000,
            },
            SequenceSample{
                nalus: &[&[0x21, 0xe1, 0x05, 0xc7, 0x38, 0xbf]],
                dts: 86666,
                pts: 86666,
            },
            SequenceSample{
                nalus: &[&[0x21, 0xe2, 0x09, 0xa1, 0xce, 0x0b]],
                dts: 88333,
                pts: 88333,
            },
            SequenceSample{
                nalus: &[&[0x21, 0xe3, 0x0d, 0xb1, 0xce, 0x02]],
                dts: 90000,
                pts: 90000,
            },
            SequenceSample{
                nalus: &[&[0x21, 0xe4, 0x11, 0x90, 0x73, 0x80]],
                dts: 91666,
                pts: 91666,
            },
            SequenceSample{
                nalus: &[&[0x21, 0xe5, 0x19, 0x0e, 0x70, 0x01]],
                dts: 91667,
                pts: 95000,
            },
            SequenceSample{
                nalus: &[&[0x01, 0xa9, 0x85, 0x7c, 0x93, 0xff]],
                dts: 93333,
                pts: 93333,
            },
            SequenceSample{
                nalus: &[&[0x21, 0xe6, 0x1d, 0x0e, 0x70, 0x01]],
                dts: 94999,
                pts: 96666,
            },
            SequenceSample{
                nalus: &[&[0x21, 0xe7, 0x21, 0x0e, 0x70, 0x01]],
                dts: 96666,
                pts: 98333,
            },
            SequenceSample{
                nalus: &[&[0x21, 0xe8, 0x25, 0x0e, 0x70, 0x01]],
                dts: 98333,
                pts: 100000,
            },
            SequenceSample{
                nalus: &[&[0x21, 0xe9, 0x29, 0x0e, 0x70, 0x01]],
                dts: 99999,
                pts: 101666,
            },
            SequenceSample{
                nalus: &[&[0x21, 0xea, 0x31, 0x0e, 0x70, 0x01]],
                dts: 101666,
                pts: 105000,
            },
            SequenceSample{
                nalus: &[&[0x01, 0xaa, 0xcb, 0x7c, 0x93, 0xff]],
                dts: 103333,
                pts: 103333,
            },
        ]; "no timing info"
    )]
    #[test_case(
        &[
            0x67, 0x64, 0x00, 0x2a, 0xac, 0x2c, 0x6a, 0x81,
            0xe0, 0x08, 0x9f, 0x96, 0x6e, 0x02, 0x02, 0x02,
            0x80, 0x00, 0x03, 0x84, 0x00, 0x00, 0xaf, 0xc8,
            0x02,
        ],
        &[
            SequenceSample{
                nalus: &[
                    // IDR.
                    &[ 0x65, 0xb8, 0x00, 0x00, 0x0b, 0xc8,],
                ],
                dts: 61,
                pts: 61,
            },
            SequenceSample{
                nalus: &[&[0x61, 0xe0, 0x20, 0x00, 0x39, 0x37]],
                dts: 101,
                pts: 101,
            },
            SequenceSample{
                nalus: &[&[0x61, 0xe0, 0x40, 0x00, 0x59, 0x37]],
                dts: 141,
                pts: 141,
            },
            SequenceSample{
                nalus: &[&[0x61, 0xe0, 0x60, 0x00, 0x79, 0x37]],
                dts: 181,
                pts: 181,
            },
        ]; "poc increment = 1"
    )]
    fn test_dts_extractor(sps: &[u8], sequence: &[SequenceSample]) {
        let sps_rbsp = h264_reader::rbsp::decode_nal(&sps).unwrap();
        let sps = SeqParameterSet::from_bits(BitReader::new(&*sps_rbsp)).unwrap();

        let mut extractor = DtsExtractor::new();
        for sample in sequence {
            let mut is_random_access_point = false;
            for nalu in sample.nalus {
                if get_unit_type(nalu).unwrap() == UnitType::SliceLayerWithoutPartitioningIdr {
                    is_random_access_point = true;
                    break;
                }
            }

            let nals: Vec<u8> = sample
                .nalus
                .iter()
                .flat_map(|nal| {
                    let len: [u8; 4] = (nal.len() as u32).to_be_bytes();
                    [&len, *nal].concat()
                })
                .collect();

            let dts = extractor
                .extract(
                    &sps,
                    is_random_access_point,
                    NalUnitIter::new(&nals),
                    sample.pts,
                )
                .unwrap();
            assert_eq!(sample.dts, dts);
        }
    }
}
