// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Common logic between H.264 and H.265.

// Some helpers are used by only one codec, so are dead when the other is disabled.
#![cfg_attr(not(all(feature = "h264", feature = "h265")), allow(dead_code))]

use crate::buf::{BufRange, Mark, MarkBuf};
use crate::codec::{Position, VideoData, VideoHandler};
use crate::inputs::Input as _;
use std::borrow::Cow;

#[cfg(feature = "unstable-send")]
pub(crate) mod packetizer;

mod analyzer;
#[cfg(not(feature = "unstable-codec-analyzer"))]
pub(crate) use analyzer::NalAnalyzer;
#[cfg(feature = "unstable-codec-analyzer")]
#[cfg_attr(docsrs, doc(cfg(feature = "unstable-codec-analyzer")))]
pub use analyzer::NalAnalyzer;

/// H.264 or H.265, for code shared between them.
#[derive(Copy, Clone, Debug)]
pub(crate) enum Codec {
    #[cfg(feature = "h264")]
    H264,
    #[cfg(feature = "h265")]
    H265,
}

impl Codec {
    const fn num_sets(self) -> usize {
        match self {
            #[cfg(feature = "h264")]
            Codec::H264 => 2,
            #[cfg(feature = "h265")]
            Codec::H265 => 3,
        }
    }

    /// Returns the index of a parameter set NAL unit, in the order
    /// [`Codec::parameters`] expects, or `None` if `nal` isn't a parameter set.
    fn set_index(self, nal: &[u8]) -> Option<usize> {
        match self {
            #[cfg(feature = "h264")]
            Codec::H264 => match nal.first()? & 0b1_1111 {
                7 => Some(0),
                8 => Some(1),
                _ => None,
            },
            #[cfg(feature = "h265")]
            Codec::H265 => match nal.get(..2)?[0] >> 1 & 0b11_1111 {
                32 => Some(0),
                33 => Some(1),
                34 => Some(2),
                _ => None,
            },
        }
    }

    fn parameters(
        self,
        sets: &[&[u8]],
    ) -> Result<crate::codec::VideoParameters, crate::codec::Error> {
        match self {
            #[cfg(feature = "h264")]
            Codec::H264 => crate::codec::h264::parameters_from_sets(sets),
            #[cfg(feature = "h265")]
            Codec::H265 => crate::codec::h265::parameters_from_sets(sets),
        }
    }

    /// Returns parameters for the given parameter sets, in any order.
    ///
    /// Currently requires exactly one of each type.
    pub(crate) fn parameters_from_unordered_sets<'s>(
        self,
        sets: impl IntoIterator<Item = &'s [u8]>,
    ) -> Result<crate::codec::VideoParameters, crate::codec::Error> {
        use crate::codec::Error;
        let mut ordered: [Option<&[u8]>; 3] = [None; 3];
        for set in sets {
            let hex = crate::hex::LimitedHex::new(set, 64);
            let Some(i) = self.set_index(set) else {
                return Err(Error::invalid(format!("not a parameter set: {hex}")));
            };
            if ordered[i].replace(set).is_some() {
                return Err(Error::unsupported(format!(
                    "multiple parameter sets of the same type are currently unsupported: {hex}"
                )));
            }
        }
        let ordered = &ordered[..self.num_sets()];
        let Some(sets) = ordered.iter().copied().collect::<Option<Vec<_>>>() else {
            return Err(Error::invalid(format!(
                "expected {}",
                match self {
                    #[cfg(feature = "h264")]
                    Codec::H264 => "an SPS and a PPS",
                    #[cfg(feature = "h265")]
                    Codec::H265 => "a VPS, an SPS, and a PPS",
                }
            )));
        };
        self.parameters(&sets)
    }
}

/// Annex B start code with the `zero_byte` prefix, as added by [`Framing::AnnexB`].
///
/// The `zero_byte` is mandatory before parameter sets (SPS, PPS, VPS) and before the first NAL
/// unit of each access unit (H.264 Annex B section B.1.2; H.265 has equivalent language).
/// We use the 4-byte form everywhere for simplicity.
pub const ANNEX_B_START_CODE: [u8; 4] = [0, 0, 0, 1];

/// How to frame H.26x NAL units in output (packet format and extra data format).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub enum Framing {
    /// AVCC/HCC style: NALs use 4-byte big-endian length prefix, extra data in `AvcDecoderConfigurationRecord` or `HevcDecoderConfigurationRecord`. Default.
    #[default]
    FourByteLength,

    /// Annex B start codes (`00 00 00 01`) for both packet data and extra data.
    AnnexB,
}

/// Iterates over the NAL units of framed H.264 or H.265 data, as produced
/// with [`Framing`].
///
/// Each item is a NAL unit's start (that of its start code, including any
/// `zero_byte`, or its length prefix) and the range of its body (header
/// included). Annex B NAL units which are empty are skipped, as are leading
/// zero bytes and `trailing_zero_8bits`.
///
/// The data is validated by [`NalUnits::new`], so iteration can't fail.
#[cfg(any(feature = "unstable-send", test))]
#[derive(Clone, Debug)]
pub(crate) struct NalUnits<'a> {
    framing: Framing,
    data: &'a [u8],

    /// For Annex B, the position of the next 3-byte start code, if any; for
    /// a 4-byte length, the position of the next length prefix.
    pos: Option<usize>,
}

/// Finds Annex B start codes; built once, as building takes a little work.
#[cfg(any(feature = "unstable-send", test))]
static START_CODE_FINDER: std::sync::OnceLock<memchr::memmem::Finder<'static>> =
    std::sync::OnceLock::new();

/// Returns the position of the next 3-byte Annex B start code at or after `from`.
#[cfg(any(feature = "unstable-send", test))]
fn find_start_code(data: &[u8], from: usize) -> Option<usize> {
    START_CODE_FINDER
        .get_or_init(|| memchr::memmem::Finder::new(&[0, 0, 1]))
        .find(&data[from..])
        .map(|p| from + p)
}

#[cfg(any(feature = "unstable-send", test))]
impl<'a> NalUnits<'a> {
    /// Validates `data` and returns an iterator over its NAL units.
    ///
    /// Returns an error if Annex B data doesn't begin with a start code (after
    /// any zero bytes), or 4-byte length data has a truncated or empty NAL
    /// unit.
    pub(crate) fn new(framing: Framing, data: &'a [u8]) -> Result<Self, String> {
        let pos = match framing {
            Framing::AnnexB => {
                let pos = find_start_code(data, 0);
                if !data[..pos.unwrap_or(data.len())].iter().all(|&b| b == 0) {
                    return Err("Annex B data doesn't begin with a start code".into());
                }
                pos
            }
            Framing::FourByteLength => {
                let mut rest = data;
                while !rest.is_empty() {
                    let Some((len, after)) = rest.split_first_chunk::<4>() else {
                        return Err("truncated NAL length".into());
                    };
                    let len = crate::to_usize(u32::from_be_bytes(*len));
                    if len == 0 {
                        return Err("empty NAL".into());
                    }
                    let Some(after) = after.get(len..) else {
                        return Err(format!(
                            "NAL length {len} exceeds remaining {} bytes",
                            after.len()
                        ));
                    };
                    rest = after;
                }
                (!data.is_empty()).then_some(0)
            }
        };
        Ok(Self { framing, data, pos })
    }
}

#[cfg(any(feature = "unstable-send", test))]
impl Iterator for NalUnits<'_> {
    type Item = (usize, std::ops::Range<usize>);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let p = self.pos?;
            match self.framing {
                Framing::AnnexB => {
                    let body_start = p + 3;
                    self.pos = find_start_code(self.data, body_start);
                    let mut end = self.pos.unwrap_or(self.data.len());
                    while end > body_start && self.data[end - 1] == 0 {
                        end -= 1; // trailing_zero_8bits or the next start code's zero_byte.
                    }
                    if end == body_start {
                        continue; // an empty NAL unit.
                    }
                    let start = if p > 0 && self.data[p - 1] == 0 {
                        p - 1
                    } else {
                        p
                    };
                    return Some((start, body_start..end));
                }
                Framing::FourByteLength => {
                    // `new` validated the lengths.
                    let len = u32::from_be_bytes(self.data[p..p + 4].try_into().unwrap());
                    let body = p + 4..p + 4 + crate::to_usize(len);
                    self.pos = (body.end < self.data.len()).then_some(body.end);
                    return Some((p, body));
                }
            }
        }
    }
}

#[cfg(any(feature = "unstable-send", test))]
impl std::iter::FusedIterator for NalUnits<'_> {}

/// Returns the given parameter set NALs, each preceded by [`ANNEX_B_START_CODE`].
pub(super) fn annex_b_parameter_sets(nals: &[&[u8]]) -> bytes::Bytes {
    let mut buf = Vec::with_capacity(nals.iter().map(|n| 4 + n.len()).sum());
    for nal in nals {
        buf.extend_from_slice(&ANNEX_B_START_CODE);
        buf.extend_from_slice(nal);
    }
    buf.into()
}

/// Returns true if the given VCL NAL body begins a picture.
///
/// This checks the first bit after the NAL header: H.264's `first_mb_in_slice`
/// is 0 iff its exp-Golomb encoding is a single `1` bit, and H.265's
/// `first_slice_segment_in_pic_flag` is that bit. `pieces` are the NAL's body
/// (excluding the header).
pub(super) fn starts_picture(pieces: &[BufRange], buf: &MarkBuf) -> bool {
    pieces
        .iter()
        .find(|p| p.len > 0)
        .is_some_and(|p| buf.split(p.pos, 1).slices().0[0] & 0x80 != 0)
}

/// A NAL unit header, as stored by the H.264 and H.265 depacketizers.
pub(super) trait NalHeader: Copy + std::fmt::Debug {
    /// The header's raw bytes: 1 for H.264, 2 for H.265.
    type Bytes: AsRef<[u8]>;

    fn bytes(self) -> Self::Bytes;

    /// Returns true for parameter sets and filler data, which are stripped
    /// from frame data.
    ///
    /// Parameter sets are instead reflected in the stream's parameters and
    /// optionally prepended to frames; see [`super::ParameterSetInsertion`].
    /// Filler data (as sent by some constant bitrate cameras) has no effect on
    /// decoding, so it's simply dropped. The analyzers don't even store it.
    fn is_stripped(self) -> bool;

    /// Returns true for filler data.
    fn is_filler(self) -> bool;
}

#[cfg(feature = "h264")]
impl NalHeader for h264_reader::nal::NalHeader {
    type Bytes = [u8; 1];

    #[inline]
    fn bytes(self) -> [u8; 1] {
        [u8::from(self)]
    }

    #[inline]
    fn is_stripped(self) -> bool {
        use h264_reader::nal::UnitType;
        matches!(
            self.nal_unit_type(),
            UnitType::SeqParameterSet | UnitType::PicParameterSet | UnitType::FillerData
        )
    }

    #[inline]
    fn is_filler(self) -> bool {
        self.nal_unit_type() == h264_reader::nal::UnitType::FillerData
    }
}

/// A complete NAL unit within an access unit, as stored by the depacketizers.
///
/// The NAL's body is stored as a range of pieces in a separate vector.
#[derive(Debug)]
pub(super) struct Nal<H> {
    pub(super) hdr: H,

    /// The length of the pieces vector as this NAL finishes.
    pub(super) next_piece_idx: u32,

    /// The total length of this NAL, including the header bytes.
    pub(super) len: u32,
}

/// Tracks progress delivering an access unit's NALs via [`Handler::data`].
///
/// Indices refer to the depacketizer's NAL and piece vectors; see
/// [`Delivery::cleared`].
#[derive(Debug, Default)]
pub(super) struct Delivery {
    /// The number of NALs fully delivered.
    nals: u32,

    /// The number of pieces delivered (or skipped as belonging to parameter sets).
    pieces: u32,

    /// True iff a first chunk has been delivered for the in-progress NAL.
    in_progress_started: bool,
}

impl Delivery {
    /// Delivers all not-yet-delivered data: completed NALs, then the
    /// in-progress NAL's pieces so far, if any.
    pub(super) fn deliver<H: NalHeader, Ctx>(
        &mut self,
        nals: &[Nal<H>],
        pieces: &[BufRange],
        in_progress: Option<H>,
        buf: &MarkBuf,
        handler: &mut impl VideoHandler<Ctx>,
    ) {
        let mut piece_idx = crate::to_usize(self.pieces);
        for nal in &nals[crate::to_usize(self.nals)..] {
            let next_piece_idx = crate::to_usize(nal.next_piece_idx);
            if !nal.hdr.is_stripped() {
                let hdr = nal.hdr.bytes();
                let first = !self.in_progress_started;
                deliver(
                    handler,
                    if first { hdr.as_ref() } else { &[] },
                    &pieces[piece_idx..next_piece_idx],
                    buf,
                    first,
                    true,
                );
            }
            self.in_progress_started = false;
            piece_idx = next_piece_idx;
        }
        self.nals = u32::try_from(nals.len()).expect("NAL count fits in u32");
        if let Some(hdr) = in_progress
            && !hdr.is_stripped()
            && (!self.in_progress_started || piece_idx < pieces.len())
        {
            let bytes = hdr.bytes();
            let first = !self.in_progress_started;
            deliver(
                handler,
                if first { bytes.as_ref() } else { &[] },
                &pieces[piece_idx..],
                buf,
                first,
                false,
            );
            self.in_progress_started = true;
            piece_idx = pieces.len();
        }
        self.pieces = u32::try_from(piece_idx).expect("piece count fits in u32");
    }

    /// Returns true if all `pieces_len` pieces have been consumed, so the
    /// depacketizer no longer needs them.
    #[inline]
    pub(super) fn caught_up(&self, pieces_len: usize) -> bool {
        crate::to_usize(self.pieces) == pieces_len
    }

    /// Notes that the depacketizer has cleared its NAL and piece vectors.
    #[inline]
    pub(super) fn cleared(&mut self) {
        self.nals = 0;
        self.pieces = 0;
    }
}

/// Returns the length of the frame [`visit_frame`] would produce.
pub(super) fn frame_len<H: NalHeader>(nals: &[Nal<H>], params: &[&[u8]]) -> usize {
    let mut len = 0;
    for p in params {
        len += 4 + p.len();
    }
    for nal in nals {
        if !nal.hdr.is_stripped() {
            len += 4 + crate::to_usize(nal.len);
        }
    }
    len
}

/// Visits an access unit's data with the given framing.
///
/// `params` are parameter set NALs to prepend. Parameter sets within `nals`
/// are skipped, as is filler (though the analyzers don't store it).
pub(super) fn visit_frame<H: NalHeader>(
    nals: &[Nal<H>],
    pieces: &[BufRange],
    buf: &MarkBuf,
    params: &[&[u8]],
    framing: Framing,
    visitor: &mut impl FnMut(&[u8]),
) {
    for param_nal in params {
        let prefix = match framing {
            Framing::FourByteLength => (param_nal.len() as u32).to_be_bytes(),
            Framing::AnnexB => ANNEX_B_START_CODE,
        };
        visitor(&prefix);
        visitor(param_nal);
    }
    let mut piece_idx = 0;
    for nal in nals {
        let next_piece_idx = crate::to_usize(nal.next_piece_idx);
        if !nal.hdr.is_stripped() {
            let prefix = match framing {
                Framing::FourByteLength => nal.len.to_be_bytes(),
                Framing::AnnexB => ANNEX_B_START_CODE,
            };
            visitor(&prefix);
            let hdr = nal.hdr.bytes();
            visitor(hdr.as_ref());
            let mut actual_len = hdr.as_ref().len();
            for piece in &pieces[piece_idx..next_piece_idx] {
                let (s1, s2) = buf.split(piece.pos, crate::to_usize(piece.len)).slices();
                visitor(s1);
                if !s2.is_empty() {
                    visitor(s2);
                }
                actual_len += crate::to_usize(piece.len);
            }
            debug_assert_eq!(crate::to_usize(nal.len), actual_len);
        }
        piece_idx = next_piece_idx;
    }
}

/// Delivers part or all of a NAL unit to [`Handler::data`].
///
/// `header` holds the NAL header bytes if this is the NAL's first chunk and
/// is empty otherwise. `first` and `last` say whether the chunk begins
/// and/or ends the NAL.
///
/// Collects slices on the stack, splitting into several [`Data`] events if
/// there are too many pieces to fit.
pub(super) fn deliver<Ctx>(
    handler: &mut impl VideoHandler<Ctx>,
    header: &[u8],
    pieces: &[BufRange],
    buf: &MarkBuf,
    mut first: bool,
    last: bool,
) {
    const MAX_SLICES: usize = 8;
    let mut slices: [&[u8]; MAX_SLICES] = [&[]; MAX_SLICES];
    let mut n = 0;
    if !header.is_empty() {
        debug_assert!(first);
        slices[0] = header;
        n = 1;
    }
    for piece in pieces {
        if n + 2 > MAX_SLICES {
            handler.data(&VideoData {
                position: Position::new(first, false),
                data: &slices[..n],
            });
            first = false;
            n = 0;
        }
        let (s1, s2) = buf.split(piece.pos, crate::to_usize(piece.len)).slices();
        slices[n] = s1;
        n += 1;
        if !s2.is_empty() {
            slices[n] = s2;
            n += 1;
        }
    }
    handler.data(&VideoData {
        position: Position::new(first, last),
        data: &slices[..n],
    });
}

/// Where an RBSP parsed via [`TolerantBitReader`] ended.
#[derive(Debug, Default)]
pub(super) struct RbspEnd {
    /// True iff there was data other than zero bits after the `rbsp_stop_one_bit`,
    /// or the bit where the parse ended wasn't a `1` (so there was no
    /// `rbsp_stop_one_bit` there).
    pub(super) has_extra_trailing_data: bool,

    /// The bit position within the RBSP of the `rbsp_stop_one_bit`, as of a
    /// successful `finish_rbsp` call which found one where the parse ended.
    pub(super) stop_bit_pos: Option<u64>,
}

/// `h264_reader::rbsp::BitRead` impl that *notes* extra trailing data rather than failing on it.
///
/// Some (Reolink) cameras appear to have a stray extra byte at the end. Follow the lead of most
/// other RTSP implementations in tolerating this.
///
/// It also counts the bits read, so that [`canonical_len`] can strip the trailing data.
#[derive(Debug)]
pub(super) struct TolerantBitReader<'a, R> {
    inner: R,

    /// The number of bits consumed so far.
    pos: u64,
    end: &'a mut RbspEnd,
}

impl<'a, R> TolerantBitReader<'a, R> {
    pub(super) fn new(inner: R, end: &'a mut RbspEnd) -> Self {
        Self { inner, pos: 0, end }
    }

    #[inline]
    fn advance<T>(&mut self, r: T, bits: impl FnOnce(&T) -> u64) -> T {
        self.pos += bits(&r);
        r
    }
}

/// Returns the bit length of the Exp-Golomb code for `v`.
#[inline]
fn ue_bits(v: u32) -> u64 {
    2 * u64::from((u64::from(v) + 1).ilog2()) + 1
}

impl<R: h264_reader::rbsp::BitRead> h264_reader::rbsp::BitRead for TolerantBitReader<'_, R> {
    fn read_ue(&mut self, name: &'static str) -> Result<u32, h264_reader::rbsp::BitReaderError> {
        let r = self.inner.read_ue(name);
        self.advance(r, |r| r.as_ref().map_or(0, |&v| ue_bits(v)))
    }

    fn read_se(&mut self, name: &'static str) -> Result<i32, h264_reader::rbsp::BitReaderError> {
        let r = self.inner.read_se(name);
        self.advance(r, |r| {
            r.as_ref().map_or(0, |&v| {
                // Inverse of the mapping in H.264 section 9.1.1, Table 9-3.
                let v = i64::from(v);
                let k = if v > 0 { 2 * v - 1 } else { -2 * v };
                ue_bits(u32::try_from(k).expect("se(v) maps from a u32 ue(v)"))
            })
        })
    }

    fn read_bit(&mut self, name: &'static str) -> Result<bool, h264_reader::rbsp::BitReaderError> {
        let r = self.inner.read_bit(name);
        self.advance(r, |r| u64::from(r.is_ok()))
    }

    fn skip(
        &mut self,
        bit_count: u32,
        name: &'static str,
    ) -> Result<(), h264_reader::rbsp::BitReaderError> {
        let r = self.inner.skip(bit_count, name);
        self.advance(r, |r| if r.is_ok() { u64::from(bit_count) } else { 0 })
    }

    fn read<const BITS: u32, I: h264_reader::rbsp::Integer>(
        &mut self,
        name: &'static str,
    ) -> Result<I, h264_reader::rbsp::BitReaderError> {
        let r = self.inner.read::<BITS, I>(name);
        self.advance(r, |r| if r.is_ok() { u64::from(BITS) } else { 0 })
    }

    fn read_var<I: h264_reader::rbsp::Integer>(
        &mut self,
        bit_count: u32,
        name: &'static str,
    ) -> Result<I, h264_reader::rbsp::BitReaderError> {
        let r = self.inner.read_var(bit_count, name);
        self.advance(r, |r| if r.is_ok() { u64::from(bit_count) } else { 0 })
    }

    fn read_to<V: h264_reader::rbsp::Primitive>(
        &mut self,
        name: &'static str,
    ) -> Result<V, h264_reader::rbsp::BitReaderError> {
        let r = self.inner.read_to(name);
        self.advance(r, |r| {
            if r.is_ok() {
                crate::to_u64(std::mem::size_of::<V>() * 8)
            } else {
                0
            }
        })
    }

    fn byte_aligned(&self) -> bool {
        self.inner.byte_aligned()
    }

    fn has_more_rbsp_data(
        &mut self,
        name: &'static str,
    ) -> Result<bool, h264_reader::rbsp::BitReaderError> {
        self.inner.has_more_rbsp_data(name)
    }

    fn finish_rbsp(mut self) -> Result<(), h264_reader::rbsp::BitReaderError> {
        use h264_reader::rbsp::BitReaderError;

        // Read the `rbsp_stop_one_bit` here rather than via `inner.finish_rbsp`,
        // which reports `RemainingData` both for data after it and for its
        // absence. Only the former is the stray trailing data tolerated below.
        if !self.inner.read_bit("rbsp_stop_one_bit")? {
            // The parse ended at a `0` bit, so either the parameter set is
            // malformed or it has syntax the parse doesn't understand.
            // Tolerate this as trailing data, but there's no stop bit position
            // for `canonical_nal` to truncate after.
            self.end.has_extra_trailing_data = true;
            return Ok(());
        }

        // Only zero bits should follow. `inner.finish_rbsp` expects to read
        // the stop bit first, so it reports a clean end as an EOF error, and
        // any further `1` bit as success or `RemainingData`.
        match self.inner.finish_rbsp() {
            Err(BitReaderError::ReaderError(_, e))
                if e.kind() == std::io::ErrorKind::UnexpectedEof => {}
            Ok(()) | Err(BitReaderError::RemainingData) => {
                self.end.has_extra_trailing_data = true;
            }
            Err(e) => return Err(e),
        }
        self.end.stop_bit_pos = Some(self.pos);
        Ok(())
    }

    fn finish_sei_payload(self) -> Result<(), h264_reader::rbsp::BitReaderError> {
        self.inner.finish_sei_payload()
    }
}

/// Returns the canonical form of a parameter set NAL parsed via [`TolerantBitReader`]: one that
/// ends with the byte holding its `rbsp_stop_one_bit`, with the bits after that zeroed.
///
/// This strips trailing data, including zero bytes, which some cameras vary from one repetition
/// of a parameter set to the next. `hdr_len` is the NAL header's length, which isn't part of
/// the RBSP. Returns `nal` unchanged if `end` has no stop bit position (see
/// [`RbspEnd::stop_bit_pos`]) or doesn't describe a stop bit within `nal` (a bug).
///
/// The result must only be used for parameter sets whose syntax has no `more_rbsp_data()`
/// lookahead, which trailing data would affect. See [`set_matches`].
pub(super) fn canonical_nal<'n>(nal: &'n [u8], hdr_len: usize, end: &RbspEnd) -> Cow<'n, [u8]> {
    let Some(pos) = end.stop_bit_pos else {
        // There's no stop bit where the parse ended (see `RbspEnd::stop_bit_pos`),
        // or `finish_rbsp` wasn't called (a bug).
        debug_assert!(end.has_extra_trailing_data, "no stop bit position");
        return Cow::Borrowed(nal);
    };
    let Ok(rbsp_byte) = usize::try_from(pos / 8) else {
        return Cow::Borrowed(nal);
    };
    let stop_bit = 0x80u8 >> (pos % 8);

    // Find `rbsp_byte` within `nal`, skipping `emulation_prevention_three_byte`s as
    // `h264_reader::rbsp::ByteReader` does.
    let mut zeros = 0;
    let mut i_rbsp = 0;
    let mut off = None;
    for (i, &b) in nal.iter().enumerate().skip(hdr_len) {
        if zeros >= 2 && b == 0x03 {
            zeros = 0;
            continue;
        }
        if i_rbsp == rbsp_byte {
            off = Some(i);
            break;
        }
        i_rbsp += 1;
        zeros = if b == 0 { zeros + 1 } else { 0 };
    }
    let Some(off) = off.filter(|&off| nal[off] & stop_bit != 0) else {
        debug_assert!(false, "stop bit {pos} not found in {nal:02x?}");
        return Cow::Borrowed(nal);
    };

    // Keep the bits up to and including the stop bit.
    let last = nal[off] & !(stop_bit - 1);
    debug_assert!(
        end.has_extra_trailing_data
            || (last == nal[off] && nal[off + 1..].iter().all(|&b| b == 0 || b == 3)),
        "stop bit {pos} is followed by data in {nal:02x?}, yet no trailing data was reported",
    );
    if off + 1 == nal.len() && last == nal[off] {
        return Cow::Borrowed(nal);
    }
    let mut canonical = nal[..=off].to_vec();
    canonical[off] = last;
    Cow::Owned(canonical)
}

/// Returns true iff the parameter set NAL given in `chunks` is equivalent to `stored`.
///
/// If `tolerant`, NALs are equivalent iff they're identical through `stored`'s
/// last `1` bit, whatever follows. As `stored` was successfully parsed, its
/// `rbsp_stop_one_bit` is at or before that bit. If the NALs' syntax has no
/// `more_rbsp_data()` lookahead, a parse of the `chunks` NAL reads the same
/// bits and stops at the same stop bit, ignoring trailing data. For a
/// [`canonical_nal`], this is exact: other NALs match iff their canonical forms
/// are identical. Otherwise, it's conservative.
///
/// If not `tolerant`, NALs are equivalent iff they're identical.
pub(super) fn set_matches<'c>(
    stored: &[u8],
    tolerant: bool,
    chunks: impl IntoIterator<Item = &'c [u8]>,
) -> bool {
    let (mut prefix, last) = match tolerant
        .then(|| stored.iter().rposition(|&b| b != 0))
        .flatten()
    {
        Some(i) => (&stored[..i], Some(stored[i])),
        None => (stored, None),
    };
    for mut chunk in chunks {
        let n = prefix.len().min(chunk.len());
        if chunk[..n] != prefix[..n] {
            return false;
        }
        prefix = &prefix[n..];
        chunk = &chunk[n..];
        if !prefix.is_empty() {
            continue; // chunk exhausted.
        }
        match (last, chunk.first()) {
            (_, None) => {}
            (None, Some(_)) => return false,
            (Some(last), Some(&b)) => {
                // Compare the bits up to and including `last`'s lowest `1`.
                let mask = !((last & last.wrapping_neg()) - 1);
                return b & mask == last;
            }
        }
    }
    prefix.is_empty() && last.is_none()
}

/// [`std::io::BufRead`] over a NAL's pieces within a [`MarkBuf`], without copying.
///
/// Wrap in [`h264_reader::rbsp::ByteReader`] to read the RBSP. The pieces
/// exclude the NAL header, so use `ByteReader::without_skip`.
#[derive(Clone)]
pub(super) struct PiecesReader<'a> {
    buf: &'a MarkBuf,
    pieces: &'a [BufRange],
    cur: &'a [u8],

    /// The second half of the current piece, if it wraps around the ring buffer.
    next: &'a [u8],
}

impl<'a> PiecesReader<'a> {
    pub(super) fn new(buf: &'a MarkBuf, pieces: &'a [BufRange]) -> Self {
        Self {
            buf,
            pieces,
            cur: &[],
            next: &[],
        }
    }
}

impl std::io::Read for PiecesReader<'_> {
    fn read(&mut self, out: &mut [u8]) -> std::io::Result<usize> {
        use std::io::BufRead as _;
        let chunk = self.fill_buf()?;
        let amt = std::cmp::min(out.len(), chunk.len());
        out[..amt].copy_from_slice(&chunk[..amt]);
        self.consume(amt);
        Ok(amt)
    }
}

impl std::io::BufRead for PiecesReader<'_> {
    fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
        // Skip empty slices; an empty return means EOF.
        while self.cur.is_empty() {
            if !self.next.is_empty() {
                self.cur = std::mem::take(&mut self.next);
            } else if let Some((piece, rest)) = self.pieces.split_first() {
                (self.cur, self.next) = self
                    .buf
                    .split(piece.pos, crate::to_usize(piece.len))
                    .slices();
                self.pieces = rest;
            } else {
                break;
            }
        }
        Ok(self.cur)
    }

    fn consume(&mut self, amt: usize) {
        self.cur = &self.cur[amt..];
    }
}

pub(crate) trait U8Array: Default + Copy + AsMut<[u8]> {
    const LEN: usize;
}

impl<const N: usize> U8Array for [u8; N]
where
    Self: Default,
{
    const LEN: usize = N;
}

/// Push-through scanner for H.26x Annex B-separated NAL units within a `MarkBuf`.
///
/// Neither H.264 nor H.265 packetizations are supposed to contain Annex B separators.
/// Some H.264 cameras send them anyway, and we accept them in "single", aggregated,
/// and fragmented payloads. This may become necessary for H.265 as well.
///
/// Also ignores trailing zero bytes in NAL bodies.
///
/// Parameterized by the NAL header array type.
#[derive(Debug)]
pub(super) enum AnnexBScanner<A: U8Array> {
    /// Between NAL bodies (or before the first one).
    ///
    /// `cur` contains `bytes_read` bytes of the NAL header: it may be 0, 1, or
    /// (in the case of H.265) 2. Note the `AnnexBScanner` is created with a full
    /// header when starting a fragmentation unit.
    Pre {
        cur: A,
        bytes_read: u8,
    },

    Mid(Mid),
}

impl<A: U8Array> AnnexBScanner<A> {
    /// Returns the position the scanner has pinned for deferred data, if any.
    ///
    /// The analyzer must be pinned at or before this before the data is
    /// supplied to it; see [`pin`].
    pub(super) fn pinned_pos(&self) -> Option<u64> {
        match self {
            AnnexBScanner::Mid(Mid {
                deferred: Some(d), ..
            }) => Some(d.mark.pos()),
            _ => None,
        }
    }

    /// Returns true if the buffer has discarded deferred data.
    pub(super) fn is_evicted(&self) -> bool {
        matches!(
            self,
            AnnexBScanner::Mid(Mid {
                deferred: Some(d),
                ..
            }) if d.mark.is_revoked()
        )
    }
}

impl<A: U8Array> Default for AnnexBScanner<A> {
    fn default() -> Self {
        Self::Pre {
            cur: A::default(),
            bytes_read: 0,
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct Mid {
    /// True after `00 00 00`, which may be followed only by more zeros and `01`.
    seen_three_zeros: bool,

    /// Zeros which ended a prior `scan`'s data, not yet known to be NAL content
    /// rather than the start of an Annex B separator.
    deferred: Option<Deferred>,
}

/// One or two zero bytes from a prior `scan`, held back from the analyzer.
///
/// This is the only data the scanner holds across calls, so it pins it with
/// its own mark, at the `pin_pos` of the packet the first zero came from.
/// That also covers any zero from a later packet. It's rare: only a
/// fragmentation unit ending in `00` gets here.
#[derive(Debug)]
struct Deferred {
    /// The positions of the zeros; only the first `n` are valid.
    zeros: [u64; 2],
    n: u8,
    mark: Mark,
}

impl Deferred {
    /// Supplies the zeros to the analyzer, as they've turned out to be NAL content.
    #[cold]
    fn flush<Ctx>(self, buf: &MarkBuf, analyzer: &mut impl NalAnalyzer<Ctx>) -> Result<(), String> {
        let zeros = &self.zeros[..usize::from(self.n)];
        if let &[a, b] = zeros
            && b == a + 1
        {
            return extend(analyzer, buf, a, b + 1);
        }
        for &z in zeros {
            extend(analyzer, buf, z, z + 1)?;
        }
        Ok(())
    }
}

/// Supplies `[start, end)` to the NAL unit in progress, if non-empty.
#[inline]
fn extend<Ctx>(
    analyzer: &mut impl NalAnalyzer<Ctx>,
    buf: &MarkBuf,
    start: u64,
    end: u64,
) -> Result<(), String> {
    if end == start {
        return Ok(());
    }
    analyzer
        .extend_nal(
            buf,
            start,
            usize::try_from(end - start).expect("len fits in usize"),
        )
        .map_err(|e| e.to_string())
}

impl<A: U8Array> AnnexBScanner<A> {
    /// Scans `[pos, pos + len)` within `buf`, supplying NAL units to `analyzer`.
    ///
    /// `end` means the enclosing payload is ending (in other words, this is
    /// not a start or middle of a fragmentation unit).
    ///
    /// Each run of NAL content within the data is supplied as one piece. Only
    /// zero bytes ending the data are held back, until a later call says
    /// whether they're NAL content or the start of a separator. They're
    /// pinned from `pin_pos`, as in [`crate::rtp::ReceivedPacketRef::with_pin_pos`].
    pub(super) fn scan<Ctx>(
        &mut self,
        buf: &MarkBuf,
        mut pos: u64,
        len: usize,
        end: bool,
        pin_pos: u64,
        analyzer: &mut impl NalAnalyzer<Ctx>,
    ) -> Result<(), String> {
        let mut data = buf.split(pos, len);

        // Loop over all NALs in the buffer.
        'nal: loop {
            let mid = match self {
                AnnexBScanner::Pre { cur, bytes_read } => {
                    while usize::from(*bytes_read) < A::LEN {
                        if let Some(next) = data.peek_byte() {
                            cur.as_mut()[usize::from(*bytes_read)] = next;
                            data.advance(1);
                            pos += 1;
                            *bytes_read += 1;
                        } else if end && *bytes_read > 0 {
                            return Err("incomplete NAL header at end of payload".into());
                        } else {
                            return Ok(());
                        }
                    }
                    analyzer
                        .start_nal(cur.as_mut(), buf, pos, 0)
                        .map_err(|e| e.to_string())?;
                    *self = AnnexBScanner::Mid(Default::default());
                    match self {
                        AnnexBScanner::Mid(mid) => mid,
                        _ => unreachable!(),
                    }
                }
                AnnexBScanner::Mid(mid) => mid,
            };

            // `[run_start, pos)` is NAL content not yet supplied, except for
            // its last `zeros` bytes, which may begin a separator.
            let mut run_start = pos;
            let mut zeros: u8 = 0;
            while let Some(b) = data.peek_byte() {
                if mid.seen_three_zeros {
                    match b {
                        0 => {} // additional zero padding before 01.
                        1 => {
                            // 00 00 00+ 01: start code complete.
                            data.advance(1);
                            pos += 1;
                            analyzer.finish_nal().map_err(|e| e.to_string())?;
                            *self = Self::default();
                            continue 'nal;
                        }
                        _ => return Err(format!("invalid sequence 00 00 00 {b:02x}")),
                    }
                    data.advance(1);
                    pos += 1;
                    run_start = pos;
                    continue;
                }
                let pending = zeros + mid.deferred.as_ref().map_or(0, |d| d.n);
                match b {
                    0 if pending < 2 => {
                        zeros += 1;
                        data.advance(1);
                        pos += 1;
                        continue;
                    }
                    0 => {
                        // 00 00 00: the NAL has ended, with trailing zeros or
                        // the start of a 4-byte start code.
                        extend(analyzer, buf, run_start, pos - u64::from(zeros))?;
                        mid.deferred = None;
                        mid.seen_three_zeros = true;
                        zeros = 0;
                        data.advance(1);
                        pos += 1;
                        run_start = pos;
                        continue;
                    }
                    1 if pending == 2 => {
                        // 00 00 01: start code complete.
                        extend(analyzer, buf, run_start, pos - u64::from(zeros))?;
                        mid.deferred = None;
                        data.advance(1);
                        pos += 1;
                        analyzer.finish_nal().map_err(|e| e.to_string())?;
                        *self = Self::default();
                        continue 'nal;
                    }
                    2 if pending == 2 => return Err("invalid sequence 00 00 02".into()),
                    _ => {}
                }

                // `b` is NAL content, so the pending zeros are too.
                if let Some(d) = mid.deferred.take() {
                    d.flush(buf, analyzer)?;
                }
                zeros = 0;
                let skip = data.find_byte(0).unwrap_or(data.len());
                data.advance(skip);
                pos += crate::to_u64(skip);
            }

            extend(analyzer, buf, run_start, pos - u64::from(zeros))?;
            if end {
                // Any pending zeros are trailing zeros.
                analyzer.finish_nal().map_err(|e| e.to_string())?;
                *self = Self::default();
            } else if zeros > 0 {
                let first = pos - u64::from(zeros);
                let d = mid.deferred.get_or_insert_with(|| Deferred {
                    zeros: [0; 2],
                    n: 0,
                    mark: buf.add_mark_at(pin_pos),
                });
                for z in first..pos {
                    d.zeros[usize::from(d.n)] = z;
                    d.n += 1;
                }
            }
            return Ok(());
        }
    }
}

/// Panics unless `[pos, pos + len)` is within `buf`'s parsed data.
pub(super) fn check_range(buf: &MarkBuf, pos: u64, len: usize) {
    assert!(
        pos.checked_add(crate::to_u64(len))
            .is_some_and(|end| end <= buf.unparsed()),
        "NAL data at [{pos}, +{len}) must end by unparsed position {}",
        buf.unparsed()
    );
}

/// Ensures `mark` pins `buf` from `pos` onward, for data at `pos`.
///
/// An analyzer pins the first data it's given and relies on later data being
/// after it in the buffer, which holds when the transport supplies data in
/// the order it read it. The RTP layer, whose packets may be reordered,
/// pins in advance via [`pin_at`] instead.
///
/// Panics if data is supplied before the existing mark, if `mark` belongs to
/// a different buffer, or as [`MarkBuf::add_mark_at`] does.
#[inline]
pub(super) fn pin(mark: &mut Option<Mark>, buf: &MarkBuf, pos: u64) {
    match mark {
        None => *mark = Some(buf.add_mark_at(pos)),
        Some(m) => {
            assert!(
                m.belongs_to(buf),
                "analyzer holding data from one MarkBuf was supplied data from another"
            );
            assert!(
                pos >= m.pos(),
                "NAL data at {pos} supplied after data at {}; data must be supplied in buffer order",
                m.pos(),
            );
        }
    }
}

/// Ensures `mark` pins `buf` from `pos` onward, before the RTP layer supplies
/// a packet's data.
///
/// `pos` is the packet's [`crate::rtp::ReceivedPacketRef::with_pin_pos`]
/// (or earlier), which is at or before the data of this and every later
/// packet. An existing mark is at or before it: pin positions never decrease.
///
/// Panics if `mark` belongs to a different buffer, or as
/// [`MarkBuf::add_mark_at`] does.
#[inline]
pub(super) fn pin_at(mark: &mut Option<Mark>, buf: &MarkBuf, pos: u64) {
    match mark {
        None => *mark = Some(buf.add_mark_at(pos)),
        Some(m) => assert!(
            m.belongs_to(buf),
            "analyzer holding data from one MarkBuf was supplied data from another"
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nals(framing: Framing, data: &[u8]) -> Result<Vec<(usize, &[u8])>, String> {
        Ok(NalUnits::new(framing, data)?
            .map(|(start, body)| (start, &data[body]))
            .collect())
    }

    #[test]
    fn annex_b_nal_units() {
        // Leading zeros, 4- and 3-byte start codes, an empty NAL unit, and
        // trailing zeros.
        let data =
            b"\x00\x00\x00\x00\x01\x65a\x00\x00\x01\x41bc\x00\x00\x00\x01\x00\x00\x01\x41d\x00\x00";
        assert_eq!(
            nals(Framing::AnnexB, data).unwrap(),
            [(1, &b"\x65a"[..]), (7, b"\x41bc"), (17, b"\x41d")]
        );
        assert_eq!(nals(Framing::AnnexB, b"").unwrap(), []);
        assert_eq!(nals(Framing::AnnexB, b"\x00\x00").unwrap(), []);
        assert!(nals(Framing::AnnexB, b"\x65a\x00\x00\x01\x41b").is_err());
    }

    #[test]
    fn four_byte_length_nal_units() {
        let data = b"\x00\x00\x00\x02\x65a\x00\x00\x00\x03\x41bc";
        assert_eq!(
            nals(Framing::FourByteLength, data).unwrap(),
            [(0, &b"\x65a"[..]), (6, b"\x41bc")]
        );
        assert_eq!(nals(Framing::FourByteLength, b"").unwrap(), []);
        assert!(nals(Framing::FourByteLength, b"\x00\x00\x00").is_err()); // truncated length.
        assert!(nals(Framing::FourByteLength, b"\x00\x00\x00\x02\x65").is_err()); // truncated body.
        assert!(nals(Framing::FourByteLength, b"\x00\x00\x00\x00").is_err()); // empty.
    }

    /// Collects frame data, streaming.
    #[cfg(feature = "h264")]
    #[derive(Default)]
    struct Data(Vec<u8>, Option<crate::codec::Accumulate>);

    #[cfg(feature = "h264")]
    impl crate::codec::VideoHandler<()> for Data {
        fn frame_start(
            &mut self,
            _: &mut crate::codec::VideoFrameStart<'_, ()>,
        ) -> crate::codec::Accumulate {
            self.1.unwrap_or(crate::codec::Accumulate::No)
        }

        fn data(&mut self, data: &VideoData<'_>) {
            for d in data.data {
                self.0.extend_from_slice(d);
            }
        }
    }

    /// Zeros ending a fragment stay pinned by the scanner after the analyzer
    /// has delivered and released everything before them, and are supplied
    /// once the next fragment shows they're NAL content.
    #[cfg(feature = "h264")]
    #[test]
    fn annex_b_scanner_deferred_zeros() {
        use crate::codec::h264::Analyzer;
        let ts = crate::Timestamp::new(0, std::num::NonZeroU32::new(90_000).unwrap(), 0).unwrap();
        let append = |buf: &mut MarkBuf, data: &[u8]| {
            let pos = buf.end();
            buf.extend(data);
            buf.advance_unparsed(buf.end());
            pos
        };
        let mut buf = MarkBuf::new(16);
        let mut a = Analyzer::new();
        let mut h = Data::default();
        a.start_au(ts, ());
        let mut scanner = AnnexBScanner::Pre {
            cur: [0x65],
            bytes_read: 1,
        };
        let pos = append(&mut buf, b"\x88ab\x00\x00");
        scanner.scan(&buf, pos, 5, false, pos, &mut a).unwrap();
        a.stream(&buf, &mut h);
        assert_eq!(h.0, b"\x65\x88ab");
        assert!(!a.has_mark(), "the analyzer released what it delivered");
        assert!(!scanner.is_evicted());

        // Reclaim space, as further input would.
        append(&mut buf, &[0xff; 64]);
        let pos = append(&mut buf, b"\x03cd");
        scanner.scan(&buf, pos, 3, true, pos, &mut a).unwrap();
        a.stream(&buf, &mut h);
        assert_eq!(h.0, b"\x65\x88ab\x00\x00\x03cd");

        // The scanner's mark can be revoked like any other.
        let mut scanner = AnnexBScanner::Pre {
            cur: [0x41],
            bytes_read: 1,
        };
        a.finish_au(&buf, &(), &mut h);
        a.start_au(ts, ());
        let pos = append(&mut buf, b"\x9a\x00");
        scanner.scan(&buf, pos, 2, false, pos, &mut a).unwrap();
        buf.set_max_retained(8);
        append(&mut buf, &[0xff; 64]);
        append(&mut buf, &[0xff; 64]); // reclaims before appending.
        assert!(scanner.is_evicted());
    }

    /// Deferred zeros from fragments supplied out of buffer order (as via
    /// `rtp::Receiver`'s reordering) all stay pinned, given each fragment's `pin_pos`.
    /// Pins the analyzer before each fragment as the H.264 depacketizer does.
    #[cfg(feature = "h264")]
    #[test]
    fn annex_b_scanner_deferred_zeros_out_of_order() {
        use crate::codec::Accumulate;
        use crate::codec::h264::Analyzer;
        for accumulate in [Accumulate::No, Accumulate::Yes] {
            let ts =
                crate::Timestamp::new(0, std::num::NonZeroU32::new(90_000).unwrap(), 0).unwrap();
            let append = |buf: &mut MarkBuf, data: &[u8]| {
                let pos = buf.end();
                buf.extend(data);
                buf.advance_unparsed(buf.end());
                pos
            };
            let mut buf = MarkBuf::new(16);
            let mut a = Analyzer::new();
            let mut h = Data(Vec::new(), Some(accumulate));
            a.start_au(ts, ());
            let mut scanner = AnnexBScanner::Pre {
                cur: [0x65],
                bytes_read: 1,
            };
            let mut scan = |a: &mut Analyzer<()>, buf: &MarkBuf, pos, len, end, pin_pos| {
                a.pin_at(buf, scanner.pinned_pos().unwrap_or(pin_pos));
                scanner.scan(buf, pos, len, end, pin_pos, a).unwrap();
            };

            // The second fragment arrived (and was buffered) before the
            // first, so the first's pin position is the second's.
            // The reorderer holds it meanwhile.
            let pos2 = append(&mut buf, b"\x00");
            let held = buf.add_mark_at(pos2);
            let pos1 = append(&mut buf, b"\x88ab\x00");
            scan(&mut a, &buf, pos1, 4, false, pos2);
            a.stream(&buf, &mut h);
            assert_eq!(a.has_mark(), accumulate == Accumulate::Yes);
            scan(&mut a, &buf, pos2, 1, false, pos2);
            drop(held);
            append(&mut buf, &[0xff; 64]); // reclaims space.
            let pos3 = append(&mut buf, b"\x03cd");
            scan(&mut a, &buf, pos3, 3, true, pos3);
            a.stream(&buf, &mut h);
            assert_eq!(h.0, b"\x65\x88ab\x00\x00\x03cd", "{accumulate:?}");
        }
    }

    /// Analyzers pin the first data they're given, and require later data to
    /// follow it in the buffer.
    #[test]
    fn pin_order() {
        let mut buf = MarkBuf::new(16);
        buf.extend(b"0123456789");
        buf.advance_unparsed(10);
        let mut mark = None;
        pin(&mut mark, &buf, 4);
        pin(&mut mark, &buf, 4);
        pin(&mut mark, &buf, 8);
        assert_eq!(mark.as_ref().map(Mark::pos), Some(4));
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| pin(&mut mark, &buf, 3)));
        assert!(r.is_err(), "out-of-order data should panic");

        // `pin_at` pins in advance, after which earlier data is fine.
        let mut mark = None;
        pin_at(&mut mark, &buf, 2);
        pin(&mut mark, &buf, 6);
        pin(&mut mark, &buf, 2);
        pin_at(&mut mark, &buf, 5); // already pinned earlier.
        assert_eq!(mark.as_ref().map(Mark::pos), Some(2));

        // Data from another buffer panics.
        let mut other = MarkBuf::new(16);
        other.extend(b"x");
        other.advance_unparsed(1);
        let r =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| pin(&mut mark, &other, 0)));
        assert!(r.is_err(), "data from another buffer should panic");
    }

    /// Tests [`PiecesReader`] with a piece that wraps around the ring buffer
    /// and an `emulation_prevention_three_byte` split across pieces.
    #[cfg(any(feature = "h264", feature = "h265"))]
    #[test]
    fn pieces_reader_wrap() {
        use std::io::Read as _;
        let mut buf = MarkBuf::new(8);
        assert_eq!(buf.capacity(), 8);
        buf.extend(b"junkjk");
        buf.advance_unparsed(6);
        buf.extend(b"\x01\x00\x00\x03\x01\x02\x03\x04"); // reclaims; occupies [6, 14).
        buf.advance_unparsed(14);
        assert_eq!(
            buf.split(6, 3).slices(),
            (&b"\x01\x00"[..], &b"\x00"[..]),
            "first piece should wrap"
        );
        let pieces = [BufRange { pos: 6, len: 3 }, BufRange { pos: 9, len: 5 }];
        let mut rbsp = Vec::new();
        h264_reader::rbsp::ByteReader::without_skip(PiecesReader::new(&buf, &pieces))
            .read_to_end(&mut rbsp)
            .unwrap();
        assert_eq!(rbsp, b"\x01\x00\x00\x01\x02\x03\x04");
    }

    #[test]
    fn ue_bits() {
        for (v, bits) in [
            (0, 1),
            (1, 3),
            (2, 3),
            (3, 5),
            (6, 5),
            (7, 7),
            (u32::MAX - 1, 63),
        ] {
            assert_eq!(super::ue_bits(v), bits, "v={v}");
        }
    }

    /// `TolerantBitReader` counts the bits each kind of read consumes, so
    /// `canonical_nal` can find the stop bit, despite trailing data.
    #[test]
    fn tolerant_bit_reader_canonical() {
        use h264_reader::rbsp::BitRead as _;

        // ue(0)=1, ue(3)=00100, se(-2)=00101, se(1)=010, u(4)=1010, a skipped bit (1),
        // u(8) via `read_to`=0xad, then the stop bit at position 27, then garbage.
        let nal = b"\x67\x90\xaa\xb5\xb7\x55";
        let mut end = RbspEnd::default();
        let mut r = TolerantBitReader::new(
            h264_reader::rbsp::BitReader::new(h264_reader::rbsp::ByteReader::without_skip(
                &nal[1..],
            )),
            &mut end,
        );
        assert_eq!(r.read_ue("a").unwrap(), 0);
        assert_eq!(r.read_ue("b").unwrap(), 3);
        assert_eq!(r.read_se("c").unwrap(), -2);
        assert_eq!(r.read_se("d").unwrap(), 1);
        assert_eq!(r.read::<4, u8>("e").unwrap(), 0b1010);
        r.skip(1, "f").unwrap();
        assert_eq!(r.read_to::<u8>("g").unwrap(), 0xad);
        r.finish_rbsp().unwrap();
        assert!(end.has_extra_trailing_data);
        assert_eq!(end.stop_bit_pos, Some(27));
        assert_eq!(&*canonical_nal(nal, 1, &end), b"\x67\x90\xaa\xb5\xb0");

        // Canonical already: borrowed. Trailing zero bytes: stripped, though
        // they aren't reported as trailing data.
        let end = RbspEnd {
            has_extra_trailing_data: false,
            stop_bit_pos: Some(27),
        };
        let canonical = canonical_nal(b"\x67\x90\xaa\xb5\xb0", 1, &end);
        assert!(matches!(canonical, Cow::Borrowed(_)));
        assert_eq!(
            &*canonical_nal(b"\x67\x90\xaa\xb5\xb0\x00\x00", 1, &end),
            b"\x67\x90\xaa\xb5\xb0"
        );
    }

    /// `TolerantBitReader::finish_rbsp` distinguishes a clean end, data after
    /// the stop bit, and a missing stop bit.
    #[test]
    fn tolerant_bit_reader_finish() {
        use h264_reader::rbsp::BitRead as _;
        let finish = |nal: &[u8]| {
            let mut end = RbspEnd::default();
            let mut r = TolerantBitReader::new(
                h264_reader::rbsp::BitReader::new(h264_reader::rbsp::ByteReader::without_skip(
                    &nal[1..],
                )),
                &mut end,
            );
            assert_eq!(r.read_ue("a").unwrap(), 0);
            r.finish_rbsp().unwrap();
            (end.has_extra_trailing_data, end.stop_bit_pos)
        };

        // ue(0), then the stop bit.
        assert_eq!(finish(b"\x67\xc0"), (false, Some(1)));
        assert_eq!(finish(b"\x67\xc0\x00"), (false, Some(1)));

        // ue(0), then the stop bit, then garbage.
        assert_eq!(finish(b"\x67\xc1"), (true, Some(1)));
        assert_eq!(finish(b"\x67\xc0\x01"), (true, Some(1)));

        // ue(0), then a 0 where the stop bit should be. This is tolerated, but
        // there's no stop bit for `canonical_nal` to truncate after.
        let nal = b"\x67\x90";
        assert_eq!(finish(nal), (true, None));
        let end = RbspEnd {
            has_extra_trailing_data: true,
            stop_bit_pos: None,
        };
        assert!(matches!(canonical_nal(nal, 1, &end), Cow::Borrowed(n) if n == nal));
    }

    /// `canonical_nal` maps the RBSP stop bit position to the NAL, past
    /// `emulation_prevention_three_byte`s.
    #[test]
    fn canonical_nal_emulation_prevention() {
        // RBSP: 00 00 01 80 ff; the stop bit is at position 24.
        let end = RbspEnd {
            has_extra_trailing_data: true,
            stop_bit_pos: Some(24),
        };
        assert_eq!(
            &*canonical_nal(b"\x42\x01\x00\x00\x03\x01\x80\xff", 2, &end),
            b"\x42\x01\x00\x00\x03\x01\x80"
        );
    }

    #[test]
    fn set_matches() {
        let stored = b"\x67\x90\xaa\xa0";
        let tolerant = |chunks: &[&[u8]]| super::set_matches(stored, true, chunks.iter().copied());
        let exact = |chunks: &[&[u8]]| super::set_matches(stored, false, chunks.iter().copied());
        for (chunks, want_tolerant, want_exact) in [
            (&[&b"\x67\x90\xaa\xa0"[..]][..], true, true),
            (&[b"\x67", b"\x90\xaa", b"", b"\xa0"], true, true),
            (&[b"\x67\x90\xaa\xa7\x55"], true, false),
            (&[b"\x67\x90", b"\xaa", b"\xbf"], true, false),
            (&[b"\x67\x90\xaa\xa0\x00"], true, false),
            (&[b"\x67\x90\xaa"], false, false),
            (&[b"\x67\x90\xaa", b""], false, false),
            (&[b"\x67\x90\xaa\x80"], false, false), // stop bit moved.
            (&[b"\x67\x90\xaa\xc0"], false, false), // bit before stop bit changed.
            (&[b"\x67\x90\xab\xa0"], false, false),
            (&[b"\x68\x90\xaa\xa0"], false, false),
        ] {
            assert_eq!(tolerant(chunks), want_tolerant, "tolerant {chunks:02x?}");
            assert_eq!(exact(chunks), want_exact, "exact {chunks:02x?}");
        }

        // Trailing zero bytes in the stored set don't matter when tolerant.
        assert!(super::set_matches(
            b"\x67\x90\xaa\xa0\x00",
            true,
            [&b"\x67\x90\xaa\xa1"[..]]
        ));
    }
}
