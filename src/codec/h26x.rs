// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Common logic between H.264 and H.265.

// Some helpers are used by only one codec, so are dead when the other is disabled.
#![cfg_attr(not(all(feature = "h264", feature = "h265")), allow(dead_code))]

use crate::buf::{BufRange, MarkBuf};
use crate::codec::{UnitPosition, VideoData, VideoHandler};
use crate::inputs::{Input as _, Split};

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

/// Returns the given parameter set NALs, each preceded by [`ANNEX_B_START_CODE`].
pub(super) fn annex_b_parameter_sets(nals: &[&[u8]]) -> bytes::Bytes {
    let mut buf = Vec::with_capacity(nals.iter().map(|n| 4 + n.len()).sum());
    for nal in nals {
        buf.extend_from_slice(&ANNEX_B_START_CODE);
        buf.extend_from_slice(nal);
    }
    buf.into()
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
                let (s1, s2) = buf.split(piece.pos, usize::from(piece.len)).slices();
                visitor(s1);
                if !s2.is_empty() {
                    visitor(s2);
                }
                actual_len += usize::from(piece.len);
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
                position: UnitPosition::new(first, false),
                data: &slices[..n],
            });
            first = false;
            n = 0;
        }
        let (s1, s2) = buf.split(piece.pos, usize::from(piece.len)).slices();
        slices[n] = s1;
        n += 1;
        if !s2.is_empty() {
            slices[n] = s2;
            n += 1;
        }
    }
    handler.data(&VideoData {
        position: UnitPosition::new(first, last),
        data: &slices[..n],
    });
}

/// `h264_reader::rbsp::BitRead` impl that *notes* extra trailing data rather than failing on it.
///
/// Some (Reolink) cameras appear to have a stray extra byte at the end. Follow the lead of most
/// other RTSP implementations in tolerating this.
#[cfg(any(feature = "h264", feature = "h265"))]
#[derive(Debug)]
pub(super) struct TolerantBitReader<'a, R> {
    pub(super) inner: R,
    pub(super) has_extra_trailing_data: &'a mut bool,
}

#[cfg(any(feature = "h264", feature = "h265"))]
impl<R: h264_reader::rbsp::BitRead> h264_reader::rbsp::BitRead for TolerantBitReader<'_, R> {
    fn read_ue(&mut self, name: &'static str) -> Result<u32, h264_reader::rbsp::BitReaderError> {
        self.inner.read_ue(name)
    }

    fn read_se(&mut self, name: &'static str) -> Result<i32, h264_reader::rbsp::BitReaderError> {
        self.inner.read_se(name)
    }

    fn read_bool(&mut self, name: &'static str) -> Result<bool, h264_reader::rbsp::BitReaderError> {
        self.inner.read_bool(name)
    }

    fn skip(
        &mut self,
        bit_count: u32,
        name: &'static str,
    ) -> Result<(), h264_reader::rbsp::BitReaderError> {
        self.inner.skip(bit_count, name)
    }

    fn read<U: h264_reader::rbsp::Numeric>(
        &mut self,
        bit_count: u32,
        name: &'static str,
    ) -> Result<U, h264_reader::rbsp::BitReaderError> {
        self.inner.read(bit_count, name)
    }

    fn read_to<V: h264_reader::rbsp::Primitive>(
        &mut self,
        name: &'static str,
    ) -> Result<V, h264_reader::rbsp::BitReaderError> {
        self.inner.read_to(name)
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

pub(crate) trait U8Array: Default + Copy + AsMut<[u8]> {
    const LEN: usize;
}

impl<const N: usize> U8Array for [u8; N]
where
    Self: Default,
{
    const LEN: usize = N;
}

/// Logic for handling NAL units and bodies.
///
/// The scanner calls methods in this order per NAL:
/// 1. [`start`](Self::start) — exactly once, with the NAL header bytes.
/// 2. [`piece`](Self::piece) — zero or more times, each with a non-empty [`BufRange`].
/// 3. [`end`](Self::end) — exactly once.
pub(crate) trait NalHandler {
    /// An array sized to hold a header: 1 byte for H.264, 2 bytes for H.265.
    type HeaderArray: U8Array;

    /// Called when a new NAL begins. `header` contains the raw header bytes.
    fn start(&mut self, header: Self::HeaderArray) -> Result<(), String>;

    /// Called with a non-empty piece of NAL body data from the ring buffer.
    fn piece(&mut self, piece: BufRange) -> Result<(), String>;

    /// Called when the current NAL ends.
    fn end(&mut self) -> Result<(), String>;
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
    /// Returns true if the scanner holds positions of data not yet passed to
    /// [`NalHandler::piece`], which must stay in the buffer.
    pub(super) fn has_deferred(&self) -> bool {
        matches!(
            self,
            AnnexBScanner::Mid(Mid {
                deferred: Some(_),
                ..
            })
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
    seen_three_zeros: bool,
    deferred: Option<Deferred>,
}

/// Data from a prior `scan` which has been deferred because it's not yet known if its
/// (1 or 2) ending zeros are part of an Annex B separator. Either:
#[derive(Debug)]
struct Deferred {
    // `start_pos` is the beginning of a chunk of `body_len` known non-separator bytes followed by a zero.
    start_pos: u64,
    body_len: u16,

    // An optional second zero, which may or may not immediately follow the first.
    second_zero_pos: Option<u64>,
}

impl Deferred {
    #[cold]
    fn flush(self, including_zeros: bool, handler: &mut impl NalHandler) -> Result<(), String> {
        if !including_zeros {
            if self.body_len > 0 {
                handler.piece(BufRange {
                    pos: self.start_pos,
                    len: self.body_len,
                })?;
            }
            return Ok(());
        }
        if self.second_zero_pos == Some(self.start_pos + u64::from(self.body_len) + 1) {
            return handler.piece(BufRange {
                pos: self.start_pos,
                len: self.body_len + 2,
            });
        }
        handler.piece(BufRange {
            pos: self.start_pos,
            len: self.body_len + 1,
        })?;
        if let Some(pos) = self.second_zero_pos {
            handler.piece(BufRange { pos, len: 1 })?;
        }
        Ok(())
    }
}

impl<A: U8Array> AnnexBScanner<A> {
    /// Scans the bytes represented within `data`, which start at buffer position `pos`.
    /// `end` means the enclosing payload is ending (in other words, this is not
    /// a start or middle of a fragmentation unit). Sends pieces on to
    /// `handler`.
    pub(super) fn scan<H: NalHandler<HeaderArray = A>>(
        &mut self,
        mut pos: u64,
        mut data: Split,
        end: bool,
        handler: &mut H,
    ) -> Result<(), String> {
        debug_assert!(data.len() <= usize::from(u16::MAX));

        // Loop over all NALs in the buffer.
        'nal: loop {
            let mid = match self {
                AnnexBScanner::Pre { cur, bytes_read } => {
                    let header_len = A::LEN;
                    while usize::from(*bytes_read) < header_len {
                        if let Some(next) = data.peek_byte() {
                            cur.as_mut()[*bytes_read as usize] = next;
                            data.advance(1);
                            pos += 1;
                            *bytes_read += 1;
                        } else if end && *bytes_read > 0 {
                            return Err("incomplete NAL header at end of payload".into());
                        } else {
                            return Ok(());
                        }
                    }
                    handler.start(*cur)?;
                    *self = AnnexBScanner::Mid(Default::default());
                    match self {
                        AnnexBScanner::Mid(mid) => mid,
                        _ => unreachable!(),
                    }
                }
                AnnexBScanner::Mid(mid) => mid,
            };

            let mut cur_pos = pos;
            let mut cur = data;

            // Process (part of) the NAL body; `data`, `pos`, and `mid.deferred` are consistent.
            'body_byte: while let Some(next_byte) = cur.peek_byte() {
                if mid.seen_three_zeros {
                    match next_byte {
                        0 => {
                            // Additional zero padding before 01.
                            cur.advance(1);
                            cur_pos += 1;
                            continue 'body_byte;
                        }
                        1 => {
                            // 00 00 00+ 01 — start code complete.
                            mid.seen_three_zeros = false;
                            handler.end()?;
                            cur.advance(1);
                            cur_pos += 1;
                            data = cur;
                            pos = cur_pos;
                            *self = Self::default();
                            continue 'nal;
                        }
                        _ => {
                            return Err(format!("invalid sequence 00 00 00 {next_byte:02x}"));
                        }
                    }
                }

                if let Some(mut deferred) = mid.deferred.take() {
                    match next_byte {
                        0 if deferred.second_zero_pos.is_none() => {
                            // This might not be immediately after the previous
                            // zero in the buffer, but it is logically after it
                            // in the resulting NAL body.
                            deferred.second_zero_pos = Some(cur_pos);
                            mid.deferred = Some(deferred);
                            cur.advance(1);
                            cur_pos += 1;
                            continue 'body_byte;
                        }
                        0 => {
                            deferred.flush(false, handler)?;
                            mid.seen_three_zeros = true;
                            cur.advance(1);
                            cur_pos += 1;
                            data = cur;
                            pos = cur_pos;
                            continue 'body_byte;
                        }
                        1 if deferred.second_zero_pos.is_some() => {
                            deferred.flush(false, handler)?;
                            handler.end()?;
                            cur.advance(1);
                            pos = cur_pos + 1;
                            data = cur;
                            *self = Self::default();
                            continue 'nal;
                        }
                        2 if deferred.second_zero_pos.is_some() => {
                            return Err("invalid sequence 00 00 02".into());
                        }
                        _ => {
                            if deferred.start_pos == pos {
                                // take deferred, do nothing; the zeros are part of the contiguous region.
                            } else if deferred.second_zero_pos.is_some_and(|p| p == pos) {
                                deferred.second_zero_pos.take();
                                deferred.flush(true, handler)?;
                            } else {
                                // Deferred is from a prior region; flush it
                                // including its zeros (confirmed non-separator).
                                deferred.flush(true, handler)?;
                            }
                        }
                    }
                }
                debug_assert!(mid.deferred.is_none());
                match cur.find_byte(0) {
                    Some(j) => {
                        debug_assert!(mid.deferred.is_none());
                        mid.deferred = Some(Deferred {
                            start_pos: pos,
                            body_len: (cur_pos + crate::to_u64(j) - pos) as u16,
                            second_zero_pos: None,
                        });
                        cur.advance(j + 1);
                        cur_pos += crate::to_u64(j + 1);
                    }
                    None => {
                        let len = data.len();
                        if !data.is_empty() {
                            handler.piece(BufRange {
                                pos,
                                len: len as u16,
                            })?;
                        }
                        break 'body_byte;
                    }
                }
            }

            if end {
                if let Some(deferred) = mid.deferred.take() {
                    deferred.flush(false, handler)?;
                }
                handler.end()?;
                *self = Self::default();
            }
            return Ok(());
        }
    }
}
