// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Common logic between H.264 and H.265.

// Some helpers are used by only one codec, so are dead when the other is disabled.
#![cfg_attr(not(all(feature = "h264", feature = "h265")), allow(dead_code))]

use crate::buf::{BufRange, Mark, MarkBuf};
use crate::codec::{Position, VideoData, VideoHandler};
use crate::inputs::Input as _;

#[cfg(feature = "unstable-send")]
pub(crate) mod packetizer;

mod analyzer;
pub(crate) use analyzer::NalAnalyzer;

/// Annex B start code with the `zero_byte` prefix, as added by [`Framing::AnnexB`].
///
/// The `zero_byte` is mandatory before parameter sets (SPS, PPS, VPS) and before the first NAL
/// unit of each access unit (H.264 Annex B section B.1.2; H.265 has equivalent language).
/// We use the 4-byte form everywhere for simplicity.
pub const ANNEX_B_START_CODE: [u8; 4] = [0, 0, 0, 1];

/// How to frame H.26x NAL units in output (packet format and extra data format).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
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
#[derive(Clone, Debug)]
pub(crate) struct NalUnits<'a> {
    framing: Framing,
    data: &'a [u8],

    /// For Annex B, the position of the next 3-byte start code, if any; for
    /// a 4-byte length, the position of the next length prefix.
    pos: Option<usize>,
}

/// Finds Annex B start codes; built once, as building takes a little work.
static START_CODE_FINDER: std::sync::OnceLock<memchr::memmem::Finder<'static>> =
    std::sync::OnceLock::new();

/// Returns the position of the next 3-byte Annex B start code at or after `from`.
fn find_start_code(data: &[u8], from: usize) -> Option<usize> {
    START_CODE_FINDER
        .get_or_init(|| memchr::memmem::Finder::new(&[0, 0, 1]))
        .find(&data[from..])
        .map(|p| from + p)
}

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

    /// Returns true for parameter sets, which are stripped from frame data.
    ///
    /// These are instead reflected in the stream's parameters and optionally
    /// prepended to frames; see [`super::ParameterSetInsertion`].
    fn is_parameter_set(self) -> bool;
}

#[cfg(feature = "h264")]
impl NalHeader for h264_reader::nal::NalHeader {
    type Bytes = [u8; 1];

    #[inline]
    fn bytes(self) -> [u8; 1] {
        [u8::from(self)]
    }

    #[inline]
    fn is_parameter_set(self) -> bool {
        use h264_reader::nal::UnitType;
        matches!(
            self.nal_unit_type(),
            UnitType::SeqParameterSet | UnitType::PicParameterSet
        )
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
            if !nal.hdr.is_parameter_set() {
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
            && !hdr.is_parameter_set()
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
        if !nal.hdr.is_parameter_set() {
            len += 4 + crate::to_usize(nal.len);
        }
    }
    len
}

/// Visits an access unit's data with the given framing.
///
/// `params` are parameter set NALs to prepend. Parameter sets within `nals`
/// are skipped.
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
        if !nal.hdr.is_parameter_set() {
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

/// `h264_reader::rbsp::BitRead` impl that *notes* extra trailing data rather than failing on it.
///
/// Some (Reolink) cameras appear to have a stray extra byte at the end. Follow the lead of most
/// other RTSP implementations in tolerating this.
#[derive(Debug)]
pub(super) struct TolerantBitReader<'a, R> {
    pub(super) inner: R,
    pub(super) has_extra_trailing_data: &'a mut bool,
}

impl<R: h264_reader::rbsp::BitRead> h264_reader::rbsp::BitRead for TolerantBitReader<'_, R> {
    fn read_ue(&mut self, name: &'static str) -> Result<u32, h264_reader::rbsp::BitReaderError> {
        self.inner.read_ue(name)
    }

    fn read_se(&mut self, name: &'static str) -> Result<i32, h264_reader::rbsp::BitReaderError> {
        self.inner.read_se(name)
    }

    fn read_bit(&mut self, name: &'static str) -> Result<bool, h264_reader::rbsp::BitReaderError> {
        self.inner.read_bit(name)
    }

    fn skip(
        &mut self,
        bit_count: u32,
        name: &'static str,
    ) -> Result<(), h264_reader::rbsp::BitReaderError> {
        self.inner.skip(bit_count, name)
    }

    fn read<const BITS: u32, I: h264_reader::rbsp::Integer>(
        &mut self,
        name: &'static str,
    ) -> Result<I, h264_reader::rbsp::BitReaderError> {
        self.inner.read::<BITS, I>(name)
    }

    fn read_var<I: h264_reader::rbsp::Integer>(
        &mut self,
        bit_count: u32,
        name: &'static str,
    ) -> Result<I, h264_reader::rbsp::BitReaderError> {
        self.inner.read_var(bit_count, name)
    }

    fn read_to<V: h264_reader::rbsp::Primitive>(
        &mut self,
        name: &'static str,
    ) -> Result<V, h264_reader::rbsp::BitReaderError> {
        self.inner.read_to(name)
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

    fn finish_rbsp(self) -> Result<(), h264_reader::rbsp::BitReaderError> {
        match self.inner.finish_rbsp() {
            Ok(()) => Ok(()),
            Err(h264_reader::rbsp::BitReaderError::RemainingData) => {
                *self.has_extra_trailing_data = true;
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    fn finish_sei_payload(self) -> Result<(), h264_reader::rbsp::BitReaderError> {
        self.inner.finish_sei_payload()
    }
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
/// its own mark, at the first zero. That also covers any zero from a later
/// packet. It's rare: only a
/// fragmentation unit ending in `00` gets here.
#[derive(Debug)]
struct Deferred {
    /// The positions of the zeros; only the first `n` are valid.
    zeros: [u64; 2],
    n: u8,

    /// Held only to pin the zeros.
    _mark: Mark,
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
    analyzer.extend_nal(
        buf,
        start,
        usize::try_from(end - start).expect("len fits in usize"),
    )
}

impl<A: U8Array> AnnexBScanner<A> {
    /// Scans `[pos, pos + len)` within `buf`, supplying NAL units to `analyzer`.
    ///
    /// `end` means the enclosing payload is ending (in other words, this is
    /// not a start or middle of a fragmentation unit).
    ///
    /// Each run of NAL content within the data is supplied as one piece. Only
    /// zero bytes ending the data are held back, until a later call says
    /// whether they're NAL content or the start of a separator.
    pub(super) fn scan<Ctx>(
        &mut self,
        buf: &MarkBuf,
        mut pos: u64,
        len: usize,
        end: bool,
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
                    analyzer.start_nal(cur.as_mut(), buf, pos, 0)?;
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
                            analyzer.finish_nal()?;
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
                        analyzer.finish_nal()?;
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
                analyzer.finish_nal()?;
                *self = Self::default();
            } else if zeros > 0 {
                let first = pos - u64::from(zeros);
                let d = mid.deferred.get_or_insert_with(|| Deferred {
                    zeros: [0; 2],
                    n: 0,
                    _mark: buf.add_mark_at(first),
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
/// the order it read it.
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
        scanner.scan(&buf, pos, 5, false, &mut a).unwrap();
        a.stream_with(&buf, &mut h);
        assert_eq!(h.0, b"\x65\x88ab");
        assert!(!a.has_mark(), "the analyzer released what it delivered");

        // Reclaim space, as further input would.
        append(&mut buf, &[0xff; 64]);
        let pos = append(&mut buf, b"\x03cd");
        scanner.scan(&buf, pos, 3, true, &mut a).unwrap();
        a.stream_with(&buf, &mut h);
        assert_eq!(h.0, b"\x65\x88ab\x00\x00\x03cd");
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
}
