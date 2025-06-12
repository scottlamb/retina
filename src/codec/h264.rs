// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [H.264](https://www.itu.int/rec/T-REC-H.264-201906-I/en)-encoded video,
//! with RTP encoding as in [RFC 6184](https://tools.ietf.org/html/rfc6184).

pub mod dts_extractor;

use std::{convert::TryFrom, fmt::Write};

use super::VideoFrame;
use crate::{
    codec::{
        h264::dts_extractor::{DtsExtractor, NalUnitIter},
        h26x::TolerantBitReader,
    },
    rtp::{ReceivedPacket, ReceivedPacketBuilder},
    Error, Timestamp, VideoTimestamp,
};
use base64::Engine as _;
use bytes::{Buf, BufMut, Bytes, BytesMut};
use h264_reader::nal::{sps::SeqParameterSet, NalHeader, UnitType};
use log::{debug, log_enabled, trace};

/// A [super::Depacketizer] implementation which finds access unit boundaries
/// and produces unfragmented NAL units as specified in [RFC
/// 6184](https://tools.ietf.org/html/rfc6184).
///
/// This inspects the contents of the NAL units only minimally, and largely for
/// logging. In particular, it doesn't completely enforce verify compliance with
/// H.264 section 7.4.1.2.3 "Order of NAL units and coded pictures and
/// association to access units". For compatibility with some broken cameras
/// that change timestamps mid-AU, it does extend AUs if they end with parameter
/// sets. See `can_end_au`.
///
/// Currently expects that the stream starts at an access unit boundary unless
/// packet loss is indicated.
///
/// # Annex B handling
///
/// Some servers erroneously include Annex B byte streams where a single NAL
/// unit is expected. This means they use Annex B "start codes" (`00 00 01`
/// sequences, which are not allowed within a NAL) to separate NALs. This
/// depacketizer allows Annex B byte streams in the following places
/// where a single NAL would otherwise be expected:
///
/// *  "Single NAL Packet Units"
/// *  a single NAL unit within a "STAP-A" aggregation packet
/// *  the entirety of a FU-A fragmented NAL unit. (This permissively allows
///    the Annex B separator to be split between fragments.)
///
/// Annex B byte streams also allow additional `00` bytes before an optional
/// after a NAL unit, referred to as `trailing_zero_8bits` respectively; this
/// code discards those. Notably, section H.264 section 7.4.1 says
/// "The last byte of the NAL unit shall not be equal to 0x00."
///
/// Currently, `00 00 01` is not understand as the very start of payload; the
/// first byte is expected to be a NAL header.
///
/// Finally, it errors on the sequence `00 00 02`, which is not allowed in
/// a single NAL or on an Annex B byte stream.
#[derive(Debug)]
pub(crate) struct Depacketizer {
    input_state: DepacketizerInputState,

    /// A complete video frame ready for pull.
    pending: Option<VideoFrame>,

    parameters: Option<InternalParameters>,

    /// In state `PreMark`, pieces of NALs, excluding their header bytes.
    /// Kept around (empty) in other states to re-use the backing allocation.
    /// Each piece must be non-empty.
    pieces: Vec<Bytes>,

    /// In state `PreMark`, an entry for each NAL.
    /// Kept around (empty) in other states to re-use the backing allocation.
    nals: Vec<Nal>,

    dts_extractor: Option<DtsExtractor>,
}

#[derive(Debug)]
struct Nal {
    hdr: h264_reader::nal::NalHeader,

    /// The length of `Depacketizer::pieces` as this NAL finishes.
    next_piece_idx: u32,

    /// The total length of this NAL, including the header byte.
    len: u32,
}

/// An access unit that is currently being accumulated during `PreMark` state.
#[derive(Debug)]
struct AccessUnit {
    start_ctx: crate::PacketContext,
    end_ctx: crate::PacketContext,
    timestamp: Timestamp,
    stream_id: usize,

    /// FU-A fragmentation unit state, if any.
    fu_a: Option<FuA>,

    /// RTP packets lost as this access unit was starting.
    loss: u16,

    same_ts_as_prev: bool,
}

#[derive(Debug)]
struct FuA {
    initial_nal_header: h264_reader::nal::NalHeader,
    cur_nal: Option<CurFuANal>,
}

#[derive(Debug)]
struct CurFuANal {
    hdr: h264_reader::nal::NalHeader,
    trailing_zeros: usize, // 0, 1, or 2

    /// The bytes of data already added to `pieces`. This excludes the `hdr`
    /// byte and `trailing_zeros`.
    pieces_bytes: usize,
}

#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
enum DepacketizerInputState {
    /// Not yet processing an access unit.
    New,

    /// Ignoring the remainder of an access unit because of interior packet loss.
    Loss {
        timestamp: crate::Timestamp,
        pkts: u16,
    },

    /// Currently processing an access unit.
    /// This will be flushed after a marked packet or when receiving a later timestamp.
    PreMark(AccessUnit),

    /// Finished processing the given packet. It's an error to receive the same timestamp again.
    PostMark {
        timestamp: crate::Timestamp,
        loss: u16,
    },
}

/// Processes an Annex B stream within `data`.
///
/// Calls `nal_fn` on each non-empty NAL within the stream. Errors on invalid Annex B sequences.
fn process_annex_b<F: FnMut(Bytes) -> Result<(), String>>(
    mut data: Bytes,
    mut nal_fn: F,
) -> Result<(), String> {
    let mut i = 0;
    let mut trailing_zeros = 0;
    while i < data.len() {
        debug_assert!(trailing_zeros <= i);
        if trailing_zeros == 0 {
            // fast-path; go all SIMD.
            match memchr::memchr(0, &data[i..]) {
                Some(pos) => {
                    i += pos + 1;
                    trailing_zeros = 1;
                }
                None => {
                    trailing_zeros = 0;
                    break;
                }
            }
        } else if trailing_zeros >= 2 && data[i] == 2 {
            return Err("forbidden sequence 00 00 02 in NAL".into());
        } else if trailing_zeros >= 2 && data[i] == 1 {
            if i > trailing_zeros {
                let piece = data.split_to(i - trailing_zeros);
                nal_fn(piece)?;
            }
            data.advance(trailing_zeros + 1);
            i = 0;
            trailing_zeros = 0;
        } else if data[i] == 0 {
            trailing_zeros += 1;
            i += 1;
        } else if trailing_zeros >= 3 {
            return Err("forbidden sequence 00 00 00 in NAL".into());
        } else {
            trailing_zeros = 0;
            i += 1;
        }
    }
    if trailing_zeros > 0 {
        data.truncate(data.len() - trailing_zeros);
    }
    if !data.is_empty() {
        nal_fn(data)?;
    }
    Ok(())
}

impl Depacketizer {
    pub(super) fn new(
        clock_rate: u32,
        format_specific_params: Option<&str>,
    ) -> Result<Self, String> {
        if clock_rate != 90_000 {
            return Err(format!(
                "invalid H.264 clock rate {clock_rate}; must always be 90000"
            ));
        }

        let parameters = match format_specific_params {
            None => None,
            Some(fp) => match InternalParameters::parse_format_specific_params(fp) {
                Ok(p) => Some(p),
                Err(e) => {
                    log::warn!("Ignoring bad H.264 format-specific-params {:?}: {}", fp, e);
                    None
                }
            },
        };
        Ok(Depacketizer {
            input_state: DepacketizerInputState::New,
            pending: None,
            pieces: Vec::new(),
            nals: Vec::new(),
            parameters,
            dts_extractor: None,
        })
    }

    pub(super) fn parameters(&self) -> Option<super::ParametersRef<'_>> {
        self.parameters
            .as_ref()
            .map(|p| super::ParametersRef::Video(&p.generic_parameters))
    }

    pub(super) fn push(&mut self, pkt: ReceivedPacket) -> Result<(), String> {
        // Push shouldn't be called until pull is exhausted.
        if let Some(p) = self.pending.as_ref() {
            panic!("push with data already pending: {p:?}");
        }

        let mut access_unit =
            match std::mem::replace(&mut self.input_state, DepacketizerInputState::New) {
                DepacketizerInputState::New => {
                    debug_assert!(self.nals.is_empty());
                    debug_assert!(self.pieces.is_empty());
                    AccessUnit::start(&pkt, 0, false)
                }
                DepacketizerInputState::PreMark(mut access_unit) => {
                    let loss = pkt.loss();
                    if loss > 0 {
                        self.nals.clear();
                        self.pieces.clear();
                        if access_unit.timestamp.pts == pkt.timestamp().pts {
                            // Loss within this access unit. Ignore until mark or new timestamp.
                            self.input_state = if pkt.mark() {
                                DepacketizerInputState::PostMark {
                                    timestamp: pkt.timestamp(),
                                    loss,
                                }
                            } else {
                                self.pieces.clear();
                                self.nals.clear();
                                DepacketizerInputState::Loss {
                                    timestamp: pkt.timestamp(),
                                    pkts: loss,
                                }
                            };
                            return Ok(());
                        }
                        // A suffix of a previous access unit was lost; discard it.
                        // A prefix of the new one may have been lost; try parsing.
                        AccessUnit::start(&pkt, 0, false)
                    } else if access_unit.timestamp.pts != pkt.timestamp().pts {
                        if access_unit.fu_a.is_some() {
                            return Err(format!(
                                "Timestamp changed from {} to {} in the middle of a fragmented NAL",
                                access_unit.timestamp,
                                pkt.timestamp()
                            ));
                        }
                        match self.nals.last() {
                            Some(n) if can_end_au(n.hdr.nal_unit_type()) => {
                                access_unit.end_ctx = *pkt.ctx();
                                self.pending =
                                    Some(self.finalize_access_unit(access_unit, "ts change")?);
                                AccessUnit::start(&pkt, 0, false)
                            }
                            Some(n) => {
                                log::debug!(
                                    "Bogus mid-access unit timestamp change after {:?}",
                                    n.hdr
                                );
                                access_unit.timestamp.pts = pkt.timestamp().pts;
                                access_unit
                            }
                            None => {
                                access_unit.timestamp.pts = pkt.timestamp().pts;
                                access_unit
                            }
                        }
                    } else {
                        access_unit
                    }
                }
                DepacketizerInputState::PostMark {
                    timestamp: state_ts,
                    loss,
                } => {
                    debug_assert!(self.nals.is_empty());
                    debug_assert!(self.pieces.is_empty());
                    AccessUnit::start(&pkt, loss, state_ts.pts == pkt.timestamp().pts)
                }
                DepacketizerInputState::Loss {
                    timestamp,
                    mut pkts,
                } => {
                    debug_assert!(self.nals.is_empty());
                    debug_assert!(self.pieces.is_empty());
                    if pkt.timestamp().pts == timestamp.pts {
                        pkts += pkt.loss();
                        self.input_state = DepacketizerInputState::Loss { timestamp, pkts };
                        return Ok(());
                    }
                    AccessUnit::start(&pkt, pkts, false)
                }
            };

        let ctx = *pkt.ctx();
        let mark = pkt.mark();
        let loss = pkt.loss();
        let timestamp = pkt.timestamp();
        let mut data = pkt.into_payload_bytes();
        // https://tools.ietf.org/html/rfc6184#section-5.2
        let Some(&nal_header) = data.first() else {
            return Err("Empty NAL".into());
        };
        if (nal_header >> 7) != 0 {
            return Err(format!("NAL header {nal_header:02x} has F bit set"));
        }
        match nal_header & 0b11111 {
            1..=23 => {
                if access_unit.fu_a.is_some() {
                    return Err(format!(
                        "Non-fragmented NAL {nal_header:02x} while FU-A fragment in progress"
                    ));
                }
                process_annex_b(data, |nal| self.add_single_nal(nal))?;
            }
            24 => {
                // STAP-A. https://tools.ietf.org/html/rfc6184#section-5.7.1
                data.advance(1);
                if access_unit.fu_a.is_some() {
                    return Err("STAP-A NAL while FU-A fragment in progress".into());
                }
                loop {
                    if data.remaining() < 3 {
                        return Err(format!(
                            "STAP-A has {} remaining bytes; expecting 2-byte length, non-empty NAL",
                            data.remaining()
                        ));
                    }
                    let len = data.get_u16();
                    if len == 0 {
                        return Err("zero length in STAP-A".into());
                    }
                    match data.remaining().cmp(&(usize::from(len))) {
                        std::cmp::Ordering::Less => {
                            return Err(format!(
                                "STAP-A too short: {} bytes remaining, expecting hdr + {}-byte NAL",
                                data.remaining(),
                                len
                            ))
                        }
                        std::cmp::Ordering::Equal => {
                            process_annex_b(data, |nal| self.add_single_nal(nal))?;
                            break;
                        }
                        std::cmp::Ordering::Greater => {
                            process_annex_b(data.split_to(usize::from(len)), |nal| {
                                self.add_single_nal(nal)
                            })?;
                        }
                    }
                }
            }
            25..=27 | 29 => {
                return Err(format!(
                    "unimplemented/unexpected interleaved mode NAL ({nal_header:02x})",
                ))
            }
            28 => {
                // FU-A. https://tools.ietf.org/html/rfc6184#section-5.8
                if data.len() < 3 {
                    // NAL + FU-A headers take 2 byte; need at least 3 bytes to make progress.
                    return Err(format!("FU-A len {} too short", data.len()));
                }
                let fu_header = data[1];
                let start = (fu_header & 0b10000000) != 0;
                let end = (fu_header & 0b01000000) != 0;
                let _reserved = (fu_header & 0b00100000) != 0;
                let nal_header =
                    NalHeader::new((nal_header & 0b011100000) | (fu_header & 0b00011111))
                        .expect("NalHeader is valid");
                data.advance(2);
                if start && end {
                    return Err(format!("Invalid FU-A header {fu_header:02x}"));
                }
                if !end && mark {
                    return Err("FU-A pkt with MARK && !END".into());
                }
                match (start, access_unit.fu_a.take()) {
                    (true, Some(_)) => {
                        return Err("FU-A with start bit while frag in progress".into())
                    }
                    (true, None) => {
                        let mut cur_nal = Some(CurFuANal {
                            hdr: nal_header,
                            trailing_zeros: 0,
                            pieces_bytes: 0,
                        });
                        self.add_fu_a(&mut cur_nal, data)?;
                        access_unit.fu_a = Some(FuA {
                            initial_nal_header: nal_header,
                            cur_nal,
                        });
                    }
                    (false, Some(mut fu_a)) => {
                        if nal_header != fu_a.initial_nal_header {
                            return Err(format!(
                                "FU-A has inconsistent NAL type: {:?} then {:?}",
                                fu_a.initial_nal_header, nal_header,
                            ));
                        }
                        self.add_fu_a(&mut fu_a.cur_nal, data)?;
                        if end {
                            if let Some(cur_nal) = fu_a.cur_nal {
                                self.nals.push(Nal {
                                    hdr: cur_nal.hdr,
                                    next_piece_idx: u32::try_from(self.pieces.len())
                                        .map_err(|_| "more than u32::MAX pieces!")?,
                                    len: u32::try_from(cur_nal.pieces_bytes + 1)
                                        .map_err(|_| "excessively long FU-A NAL")?,
                                });
                            }
                        } else if mark {
                            return Err("FU-A has MARK and no END".into());
                        } else {
                            access_unit.fu_a = Some(fu_a);
                        }
                    }
                    (false, None) => {
                        if loss > 0 {
                            self.pieces.clear();
                            self.nals.clear();
                            self.input_state = DepacketizerInputState::Loss {
                                timestamp,
                                pkts: loss,
                            };
                            return Ok(());
                        }
                        return Err("FU-A has start bit unset while no frag in progress".into());
                    }
                }
            }
            _ => return Err(format!("bad nal header {nal_header:02x}")),
        }
        self.input_state = if mark {
            match self.nals.last() {
                Some(n) if can_end_au(n.hdr.nal_unit_type()) => {
                    access_unit.end_ctx = ctx;
                    self.pending = Some(self.finalize_access_unit(access_unit, "mark")?);
                    DepacketizerInputState::PostMark { timestamp, loss: 0 }
                }
                Some(n) => {
                    log::debug!("Bogus mid-access unit mark on {:?}", n.hdr);
                    access_unit.timestamp.pts = timestamp.pts;
                    DepacketizerInputState::PreMark(access_unit)
                }
                None => DepacketizerInputState::PreMark(access_unit),
            }
        } else {
            DepacketizerInputState::PreMark(access_unit)
        };
        Ok(())
    }

    pub(super) fn pull(&mut self) -> Option<super::CodecItem> {
        self.pending.take().map(super::CodecItem::VideoFrame)
    }

    /// Adds an unfragmented NAL which does not contain any Annex B separators.
    fn add_single_nal(&mut self, mut data: Bytes) -> Result<(), String> {
        let len = u32::try_from(data.len()).expect("data len < u16::MAX");
        let hdr = data.get_u8();
        let hdr = NalHeader::new(hdr).map_err(|_| format!("bad NAL header {hdr:02x}"))?;
        if !data.is_empty() {
            self.pieces.push(data);
        }
        self.nals.push(Nal {
            hdr,
            next_piece_idx: u32::try_from(self.pieces.len())
                .map_err(|_| "more than u32::MAX pieces!")?,
            len,
        });
        Ok(())
    }

    /// Adds a FU-A packet, which may contain Annex B separators.
    ///
    /// This is essentially a specialized version of `process_annex_b` and
    /// `add_single_nal` due to extra complexity of FU-A packets:
    ///
    /// * It is resumable, and the end-of-packet handling is done by the caller.
    /// * The (first) NAL header is passed in by the caller after parsing from
    ///   a couple bytes.
    fn add_fu_a(&mut self, cur_nal: &mut Option<CurFuANal>, mut data: Bytes) -> Result<(), String> {
        'outer: loop {
            let c = match cur_nal {
                Some(c) => c,
                None => {
                    let Ok(hdr_byte) = data.try_get_u8() else {
                        return Ok(());
                    };
                    let hdr = NalHeader::new(hdr_byte)
                        .map_err(|_| format!("bad NAL header {hdr_byte:02x}"))?;
                    cur_nal.insert(CurFuANal {
                        hdr,
                        trailing_zeros: 0,
                        pieces_bytes: 0,
                    })
                }
            };
            let mut cur_pos = 0;
            while cur_pos < data.len() {
                if c.trailing_zeros == 0 {
                    // fast-path; go all SIMD.
                    match memchr::memchr(0, &data[cur_pos..]) {
                        Some(pos) => {
                            cur_pos += pos + 1;
                            c.trailing_zeros = 1;
                        }
                        None => {
                            c.trailing_zeros = 0;
                            break;
                        }
                    }
                } else if c.trailing_zeros >= 2 && data[cur_pos] == 2 {
                    return Err("forbidden sequence 00 00 02 in NAL".into());
                } else if c.trailing_zeros >= 2 && data[cur_pos] == 1 {
                    let mut piece = data.split_to(cur_pos + 1);
                    if piece.len() > c.trailing_zeros + 1 {
                        piece.truncate(piece.len() - c.trailing_zeros - 1);
                        c.pieces_bytes += piece.len();
                        self.pieces.push(piece);
                    }
                    self.nals.push(Nal {
                        hdr: c.hdr,
                        next_piece_idx: u32::try_from(self.pieces.len())
                            .map_err(|_| "more than u32::MAX pieces!")?,
                        len: u32::try_from(c.pieces_bytes + 1)
                            .map_err(|_| "excessively long FU-A NAL")?,
                    });
                    *cur_nal = None;
                    continue 'outer;
                } else if data[cur_pos] == 0 {
                    c.trailing_zeros += 1;
                    cur_pos += 1;
                } else if c.trailing_zeros > 2 {
                    return Err("forbidden sequence 00 00 00 in NAL".into());
                } else {
                    if cur_pos < c.trailing_zeros {
                        // The previous chunks' (1 or 2) trailing zeros were
                        // part of the NAL but have not yet been included. We've
                        // thrown away the reference to those chunks, but we can
                        // insert equivalent zero bytes here.
                        let prev_chunk_zeros = c.trailing_zeros - cur_pos;
                        c.pieces_bytes += prev_chunk_zeros;
                        self.pieces
                            .push(Bytes::from_static(&[0; 2][..prev_chunk_zeros]));
                    }
                    c.trailing_zeros = 0;
                    cur_pos += 1;
                }
            }
            if data.len() > c.trailing_zeros {
                data.truncate(data.len() - c.trailing_zeros);
                c.pieces_bytes += data.len();
                self.pieces.push(data);
            }
            return Ok(());
        }
    }

    /// Logs information about each access unit.
    /// Currently, "bad" access units (violating certain specification rules)
    /// are logged at debug priority, and others are logged at trace priority.
    fn log_access_unit(&self, au: &AccessUnit, reason: &str) {
        let mut errs = String::new();
        if au.same_ts_as_prev {
            errs.push_str("\n* same timestamp as previous access unit");
        }
        validate_order(&self.nals, &mut errs);
        if !errs.is_empty() {
            let mut nals = String::new();
            for (i, nal) in self.nals.iter().enumerate() {
                let _ = write!(&mut nals, "\n  {}: {:?}", i, nal.hdr);
            }
            debug!(
                "bad access unit (ended by {}) at ts {}\nerrors are:{}\nNALs are:{}",
                reason, au.timestamp, errs, nals
            );
        } else if log_enabled!(log::Level::Trace) {
            let mut nals = String::new();
            for (i, nal) in self.nals.iter().enumerate() {
                let _ = write!(&mut nals, "\n  {}: {:?}", i, nal.hdr);
            }
            trace!(
                "access unit (ended by {}) at ts {}; NALS are:{}",
                reason,
                au.timestamp,
                nals
            );
        }
    }

    fn finalize_access_unit(&mut self, au: AccessUnit, reason: &str) -> Result<VideoFrame, String> {
        let mut piece_idx = 0;
        let mut retained_len = 0usize;
        let mut is_random_access_point = true;
        let mut is_disposable = true;
        let mut new_sps = None;
        let mut new_pps = None;

        if log_enabled!(log::Level::Debug) {
            self.log_access_unit(&au, reason);
        }
        for nal in &self.nals {
            let next_piece_idx = crate::to_usize(nal.next_piece_idx);
            let nal_pieces = &self.pieces[piece_idx..next_piece_idx];
            match nal.hdr.nal_unit_type() {
                UnitType::SeqParameterSet => {
                    if self
                        .parameters
                        .as_ref()
                        .map(|p| !nal_matches(&p.sps_nal[..], nal.hdr, nal_pieces))
                        .unwrap_or(true)
                    {
                        new_sps = Some(to_bytes(nal.hdr, nal.len, nal_pieces));
                    }
                }
                UnitType::PicParameterSet => {
                    if self
                        .parameters
                        .as_ref()
                        .map(|p| !nal_matches(&p.pps_nal[..], nal.hdr, nal_pieces))
                        .unwrap_or(true)
                    {
                        new_pps = Some(to_bytes(nal.hdr, nal.len, nal_pieces));
                    }
                }
                UnitType::SliceDataPartitionALayer
                | UnitType::SliceDataPartitionBLayer
                | UnitType::SliceDataPartitionCLayer
                | UnitType::SliceLayerWithoutPartitioningNonIdr => is_random_access_point = false,
                _ => {}
            }
            if nal.hdr.nal_ref_idc() != 0 {
                is_disposable = false;
            }
            // TODO: support optionally filtering non-VUI NALs.
            retained_len += 4usize + crate::to_usize(nal.len);
            piece_idx = next_piece_idx;
        }
        let mut data = Vec::with_capacity(retained_len);
        piece_idx = 0;
        for nal in &self.nals {
            let next_piece_idx = crate::to_usize(nal.next_piece_idx);
            let nal_pieces = &self.pieces[piece_idx..next_piece_idx];
            data.extend_from_slice(&nal.len.to_be_bytes()[..]);
            data.push(nal.hdr.into());
            let mut actual_len = 1;
            for piece in nal_pieces {
                debug_assert!(!piece.is_empty());
                data.extend_from_slice(&piece[..]);
                actual_len += piece.len();
            }
            debug_assert_eq!(crate::to_usize(nal.len), actual_len);
            piece_idx = next_piece_idx;
        }
        debug_assert_eq!(retained_len, data.len());
        self.nals.clear();
        self.pieces.clear();

        let has_new_parameters = match (
            new_sps.as_deref(),
            new_pps.as_deref(),
            self.parameters.as_ref(),
        ) {
            (Some(sps_nal), Some(pps_nal), old_ip) => {
                // TODO: could map this to a RtpPacketError more accurately.
                let seen_extra_trailing_data =
                    old_ip.map(|o| o.seen_extra_trailing_data).unwrap_or(false);
                self.parameters = Some(InternalParameters::parse_sps_and_pps(
                    sps_nal,
                    pps_nal,
                    seen_extra_trailing_data,
                )?);
                true
            }
            (Some(_), None, Some(old_ip)) | (None, Some(_), Some(old_ip)) => {
                let sps_nal = new_sps.as_deref().unwrap_or(&old_ip.sps_nal);
                let pps_nal = new_pps.as_deref().unwrap_or(&old_ip.pps_nal);
                // TODO: as above, could map this to a RtpPacketError more accurately.
                self.parameters = Some(InternalParameters::parse_sps_and_pps(
                    sps_nal,
                    pps_nal,
                    old_ip.seen_extra_trailing_data,
                )?);
                true
            }
            _ => false,
        };

        let mut dts = au.timestamp.pts;
        if let Some(parameters) = &self.parameters {
            // Skip samples silently until we find one with an IDR.
            if self.dts_extractor.is_none() && is_random_access_point {
                self.dts_extractor = Some(DtsExtractor::new());
            }

            // If first sync sample has been received.
            if let Some(dts_extractor) = &mut self.dts_extractor {
                let pts = au.timestamp.timestamp();
                dts = dts_extractor
                    .extract(&parameters.sps, NalUnitIter::new(&data), pts)
                    .map_err(|e| e.to_string())?;
            };
        }

        let timestamp = VideoTimestamp {
            timestamp: Timestamp {
                pts: au.timestamp.pts,
                clock_rate: au.timestamp.clock_rate,
                start: au.timestamp.start,
            },
            dts: Some(dts),
        };

        Ok(VideoFrame {
            has_new_parameters,
            loss: au.loss,
            start_ctx: au.start_ctx,
            end_ctx: au.end_ctx,
            timestamp,
            stream_id: au.stream_id,
            is_random_access_point,
            is_disposable,
            data,
        })
    }
}

/// Returns true if we allow the given NAL unit type to end an access unit.
///
/// We specifically prohibit this for the SPS and PPS. Reolink cameras sometimes
/// incorrectly set the RTP marker bit and/or change the timestamp after these.
fn can_end_au(nal_unit_type: UnitType) -> bool {
    // H.264 section 7.4.1.2.3 Order of NAL units and coded pictures and
    // association to access units says "Sequence parameter set NAL units or
    // picture parameter set NAL units may be present in an access unit, but
    // cannot follow the last VCL NAL unit of the primary coded picture within
    // the access unit, as this condition would specify the start of a new
    // access unit."
    nal_unit_type != UnitType::SeqParameterSet && nal_unit_type != UnitType::PicParameterSet
}

impl AccessUnit {
    fn start(
        pkt: &crate::rtp::ReceivedPacket,
        additional_loss: u16,
        same_ts_as_prev: bool,
    ) -> Self {
        AccessUnit {
            start_ctx: *pkt.ctx(),
            end_ctx: *pkt.ctx(),
            timestamp: pkt.timestamp,
            stream_id: pkt.stream_id(),
            fu_a: None,

            // TODO: overflow?
            loss: pkt.loss() + additional_loss,
            same_ts_as_prev,
        }
    }
}

/// Checks NAL unit type ordering against rules of H.264 section 7.4.1.2.3.
///
/// This doesn't precisely check every rule there but enough to diagnose some
/// problems.
fn validate_order(nals: &[Nal], errs: &mut String) {
    let mut seen_vcl = false;
    for (i, nal) in nals.iter().enumerate() {
        match nal.hdr.nal_unit_type() {
            /* 1 */ UnitType::SliceLayerWithoutPartitioningNonIdr |
            /* 2 */ UnitType::SliceDataPartitionALayer |
            /* 3 */ UnitType::SliceDataPartitionBLayer |
            /* 4 */ UnitType::SliceDataPartitionCLayer |
            /* 5 */ UnitType::SliceLayerWithoutPartitioningIdr => {
                seen_vcl = true;
            }
            /* 6 */ UnitType::SEI => {
                if seen_vcl {
                    errs.push_str("\n* SEI after VCL");
                }
            }
            /* 9 */ UnitType::AccessUnitDelimiter => {
                if i != 0 {
                    let _ = write!(errs, "\n* access unit delimiter must be first in AU; was preceded by {:?}",
                                nals[i-1].hdr);
                }
            }
            /* 10 */ UnitType::EndOfSeq => {
                if !seen_vcl {
                    errs.push_str("\n* end of sequence without VCL");
                }
            }
            /* 11 */ UnitType::EndOfStream => {
                if i != nals.len() - 1 {
                    errs.push_str("\n* end of stream NAL isn't last");
                }
            }
            _ => {}
        }
    }
    if !seen_vcl {
        errs.push_str("\n* missing VCL");
    }
}

#[derive(Clone, Debug)]
struct InternalParameters {
    generic_parameters: super::VideoParameters,
    sps: SeqParameterSet,

    /// The (single) SPS NAL.
    sps_nal: Bytes,

    /// The (single) PPS NAL.
    pps_nal: Bytes,

    seen_extra_trailing_data: bool,
}

impl InternalParameters {
    /// Parses metadata from the `format-specific-params` of a SDP `fmtp` media attribute.
    fn parse_format_specific_params(format_specific_params: &str) -> Result<Self, String> {
        let mut sprop_parameter_sets = None;
        for p in format_specific_params.split(';') {
            match p.trim().split_once('=') {
                Some(("sprop-parameter-sets", value)) => sprop_parameter_sets = Some(value),
                None => return Err("key without value".into()),
                _ => (),
            }
        }
        let sprop_parameter_sets = sprop_parameter_sets
            .ok_or_else(|| "no sprop-parameter-sets in H.264 format-specific-params".to_string())?;

        let mut sps_nal = None;
        let mut pps_nal = None;

        let mut nal_fn = |nal: Bytes| -> Result<(), String> {
            let hex = crate::hex::LimitedHex::new(&nal, 256);

            let Some(&header) = nal.first() else {
                return Ok(()); // shouldn't happen by `process_annex_b` guarantee but whatever.
            };
            let header = h264_reader::nal::NalHeader::new(header)
                .map_err(|_| format!("bad sprop-parameter-sets: bad header in NAL: {hex}"))?;
            match header.nal_unit_type() {
                UnitType::SeqParameterSet => {
                    if sps_nal.is_some() {
                        return Err("multiple SPSs are currently unsupported".into());
                    }
                    sps_nal = Some(nal);
                }
                UnitType::PicParameterSet => {
                    if pps_nal.is_some() {
                        return Err("multiple PPSs are currently unsupported".into());
                    }
                    pps_nal = Some(nal);
                }
                _ => {
                    return Err(format!(
                        "bad sprop-parameter-sets: unexpected non-SPS/PPS NAL: {hex}"
                    ));
                }
            }
            Ok(())
        };

        for part in sprop_parameter_sets.split(',') {
            // Each part is supposed to be a single NAL. But some cameras at least have an Annex B
            // start code as a prefix or suffix. It's not *vital* to support this given that such
            // cameras generally repeat the parameters in-band, but it's nice to
            // get the parameters as early as possible. And we already have the `process_annex_b`
            // logic sitting around to support cameras that use Annex B
            // sequences within RTP payloads.
            let part = base64::engine::general_purpose::STANDARD
                .decode(part)
                .map_err(|_| {
                    format!("bad sprop-parameter-sets: invalid base64 encoding in NAL: {part}")
                })?;
            process_annex_b(Bytes::from(part), &mut nal_fn)?;
        }
        let sps_nal = sps_nal.ok_or_else(|| "bad sprop-parameter-sets: no sps".to_string())?;
        let pps_nal = pps_nal.ok_or_else(|| "bad sprop-parameter-sets: no pps".to_string())?;
        Self::parse_sps_and_pps(&sps_nal, &pps_nal, false)
    }

    fn parse_sps_and_pps(
        sps_nal: &[u8],
        pps_nal: &[u8],
        mut seen_extra_trailing_data: bool,
    ) -> Result<InternalParameters, String> {
        let sps_rbsp = h264_reader::rbsp::decode_nal(sps_nal).map_err(|_| "bad sps")?;
        if sps_rbsp.len() < 5 {
            return Err("bad sps".into());
        }
        let rfc6381_codec = format!(
            "avc1.{:02X}{:02X}{:02X}",
            sps_rbsp[0], sps_rbsp[1], sps_rbsp[2]
        );

        let mut sps_has_extra_trailing_data = false;
        let sps_hex = crate::hex::LimitedHex::new(sps_nal, 256);
        let sps = h264_reader::nal::sps::SeqParameterSet::from_bits(TolerantBitReader {
            inner: h264_reader::rbsp::BitReader::new(&*sps_rbsp),
            has_extra_trailing_data: &mut sps_has_extra_trailing_data,
        })
        .map_err(|e| format!("Bad SPS {sps_hex}: {e:?}"))?;
        debug!("SPS {sps_hex}: {:#?}", &sps);
        if sps_has_extra_trailing_data && !seen_extra_trailing_data {
            log::warn!("Ignoring trailing data in SPS {sps_hex}; will not log about trailing data again for this stream.");
            seen_extra_trailing_data = true;
        }

        let pixel_dimensions = sps
            .pixel_dimensions()
            .map_err(|e| format!("SPS has invalid pixel dimensions: {e:?}"))?;
        let e = |_| {
            format!(
                "SPS has invalid pixel dimensions: {}x{} is too large",
                pixel_dimensions.0, pixel_dimensions.1
            )
        };
        let pixel_dimensions = (
            u16::try_from(pixel_dimensions.0).map_err(e)?,
            u16::try_from(pixel_dimensions.1).map_err(e)?,
        );

        // Create the AVCDecoderConfiguration, ISO/IEC 14496-15 section 5.2.4.1.
        // The beginning of the AVCDecoderConfiguration takes a few values from
        // the SPS (ISO/IEC 14496-10 section 7.3.2.1.1).
        let mut avc_decoder_config = BytesMut::with_capacity(11 + sps_nal.len() + pps_nal.len());
        avc_decoder_config.put_u8(1); // configurationVersion
        avc_decoder_config.extend(&sps_rbsp[0..=2]); // profile_idc . AVCProfileIndication
                                                     // ...misc bits... . profile_compatibility
                                                     // level_idc . AVCLevelIndication

        // Hardcode lengthSizeMinusOne to 3, matching TransformSampleData's 4-byte
        // lengths.
        avc_decoder_config.put_u8(0xff);

        // Only support one SPS and PPS.
        // ffmpeg's ff_isom_write_avcc has the same limitation, so it's probably
        // fine. This next byte is a reserved 0b111 + a 5-bit # of SPSs (1).
        avc_decoder_config.put_u8(0xe1);
        avc_decoder_config.extend(
            &u16::try_from(sps_nal.len())
                .map_err(|_| format!("SPS NAL is {} bytes long; must fit in u16", sps_nal.len()))?
                .to_be_bytes()[..],
        );
        let sps_nal_start = avc_decoder_config.len();
        avc_decoder_config.extend_from_slice(sps_nal);
        let sps_nal_end = avc_decoder_config.len();
        avc_decoder_config.put_u8(1); // # of PPSs.
        avc_decoder_config.extend(
            &u16::try_from(pps_nal.len())
                .map_err(|_| format!("PPS NAL is {} bytes long; must fit in u16", pps_nal.len()))?
                .to_be_bytes()[..],
        );
        let pps_nal_start = avc_decoder_config.len();
        avc_decoder_config.extend_from_slice(pps_nal);
        let pps_nal_end = avc_decoder_config.len();
        assert_eq!(avc_decoder_config.len(), 11 + sps_nal.len() + pps_nal.len());

        let (pixel_aspect_ratio, frame_rate);
        match sps.vui_parameters {
            Some(ref vui) => {
                pixel_aspect_ratio = vui
                    .aspect_ratio_info
                    .as_ref()
                    .and_then(|a| a.clone().get())
                    .map(|(h, v)| (u32::from(h), (u32::from(v))));

                // TODO: study H.264, (E-34). This quick'n'dirty calculation isn't always right.
                frame_rate = vui.timing_info.as_ref().and_then(|t| {
                    t.num_units_in_tick
                        .checked_mul(2)
                        .map(|doubled| (doubled, t.time_scale))
                });
            }
            None => {
                pixel_aspect_ratio = None;
                frame_rate = None;
            }
        }
        let avc_decoder_config = avc_decoder_config.freeze();
        let sps_nal = avc_decoder_config.slice(sps_nal_start..sps_nal_end);
        let pps_nal = avc_decoder_config.slice(pps_nal_start..pps_nal_end);

        Ok(InternalParameters {
            generic_parameters: super::VideoParameters {
                rfc6381_codec,
                pixel_dimensions,
                pixel_aspect_ratio,
                frame_rate,
                extra_data: avc_decoder_config,
                codec: super::VideoParametersCodec::H264,
            },
            sps,
            sps_nal,
            pps_nal,
            seen_extra_trailing_data,
        })
    }
}

/// Returns true iff the bytes of `nal` equal the bytes of `[hdr, ..data]`.
fn nal_matches(nal: &[u8], hdr: NalHeader, pieces: &[Bytes]) -> bool {
    if nal.first() != Some(&u8::from(hdr)) {
        return false;
    }
    let mut nal_pos = 1;
    for piece in pieces {
        let new_pos = nal_pos + piece.len();
        if nal.len() < new_pos {
            return false;
        }
        if piece[..] != nal[nal_pos..new_pos] {
            return false;
        }
        nal_pos = new_pos;
    }
    nal_pos == nal.len()
}

/// Saves the given NAL to a contiguous `Bytes`.
fn to_bytes(hdr: NalHeader, len: u32, pieces: &[Bytes]) -> Bytes {
    let len = crate::to_usize(len);
    let mut out = Vec::with_capacity(len);
    out.push(hdr.into());
    for piece in pieces {
        out.extend_from_slice(&piece[..]);
    }
    debug_assert_eq!(len, out.len());
    out.into()
}

/// A simple packetizer, currently only for testing/benchmarking. Unstable.
///
/// Only uses plain NALs and FU-As, never STAP-A.
/// Expects data to be NALs separated by 4-byte prefixes.
#[doc(hidden)]
pub struct Packetizer {
    max_payload_size: u16,
    next_sequence_number: u16,
    stream_id: usize,
    ssrc: u32,
    payload_type: u8,
    state: PacketizerState,
}

impl Packetizer {
    pub fn new(
        max_payload_size: u16,
        stream_id: usize,
        initial_sequence_number: u16,
        payload_type: u8,
        ssrc: u32,
    ) -> Result<Self, String> {
        if max_payload_size < 3 {
            // minimum size to make progress with FU-A packets.
            return Err("max_payload_size must be > 3".into());
        }
        Ok(Self {
            max_payload_size,
            stream_id,
            next_sequence_number: initial_sequence_number,
            ssrc,
            payload_type,
            state: PacketizerState::Idle,
        })
    }

    pub fn push(&mut self, timestamp: Timestamp, data: Bytes) -> Result<(), Error> {
        assert!(matches!(self.state, PacketizerState::Idle));
        self.state = PacketizerState::HaveData { timestamp, data };
        Ok(())
    }

    // TODO: better error type?
    pub fn pull(&mut self) -> Result<Option<ReceivedPacket>, String> {
        let max_payload_size = usize::from(self.max_payload_size);
        match std::mem::replace(&mut self.state, PacketizerState::Idle) {
            PacketizerState::Idle => Ok(None),
            PacketizerState::HaveData {
                timestamp,
                mut data,
            } => {
                if data.len() < 5 {
                    return Err(format!(
                        "have only {} bytes; expected 4-byte length + non-empty NAL",
                        data.len()
                    ));
                }
                let len = data.get_u32();
                let usize_len = crate::to_usize(len);
                if data.len() < usize_len || len == 0 {
                    return Err(format!(
                        "bad length of {} bytes; expected [1, {}]",
                        len,
                        data.len()
                    ));
                }
                let sequence_number = self.next_sequence_number;
                self.next_sequence_number = self.next_sequence_number.wrapping_add(1);
                let hdr = NalHeader::new(data[0]).map_err(|_| "F bit in NAL header".to_owned())?;
                if matches!(hdr.nal_unit_type(), UnitType::Unspecified(_)) {
                    // This can clash with fragmentation/aggregation NAL types.
                    return Err(format!("bad NAL header {hdr:?}"));
                }
                if usize_len > max_payload_size {
                    // start a FU-A.
                    data.advance(1);
                    let fu_indicator = (hdr.nal_ref_idc() << 5) | 28;
                    let fu_header = 0b1000_0000 | hdr.nal_unit_type().id(); // START bit set.
                    let payload = [fu_indicator, fu_header]
                        .into_iter()
                        .chain(data[..max_payload_size - 2].iter().copied());
                    // TODO: ctx and channel_id are placeholders.
                    let pkt = ReceivedPacketBuilder {
                        ctx: crate::PacketContext::dummy(),
                        stream_id: self.stream_id,
                        timestamp,
                        ssrc: self.ssrc,
                        sequence_number,
                        loss: 0,
                        mark: false,
                        payload_type: self.payload_type,
                    }
                    .build(payload)?;
                    data.advance(max_payload_size - 2);
                    self.state = PacketizerState::InFragment {
                        timestamp,
                        hdr,
                        left: len + 1 - u32::from(self.max_payload_size),
                        data,
                    };
                    return Ok(Some(pkt));
                }

                // Send a plain NAL packet. (TODO: consider using STAP-A.)
                let mark;
                if data.len() == usize_len {
                    mark = true;
                } else {
                    self.state = PacketizerState::HaveData {
                        timestamp,
                        data: data.split_off(usize_len),
                    };
                    mark = false;
                }
                Ok(Some(
                    ReceivedPacketBuilder {
                        ctx: crate::PacketContext::dummy(),
                        stream_id: self.stream_id,
                        timestamp,
                        ssrc: self.ssrc,
                        sequence_number,
                        loss: 0,
                        mark,
                        payload_type: self.payload_type,
                    }
                    .build(data)?,
                ))
            }
            PacketizerState::InFragment {
                timestamp,
                hdr,
                left,
                mut data,
            } => {
                let sequence_number = self.next_sequence_number;
                self.next_sequence_number = self.next_sequence_number.wrapping_add(1);
                let mut payload;
                let mark;
                if left > u32::from(self.max_payload_size) - 2 {
                    mark = false;
                    payload = Vec::with_capacity(max_payload_size);
                    let fu_indicator = (hdr.nal_ref_idc() << 5) | 28;
                    let fu_header = hdr.nal_unit_type().id(); // neither START nor END bits set.
                    payload.extend_from_slice(&[fu_indicator, fu_header]);
                    payload.extend_from_slice(&data[..max_payload_size - 2]);
                    data.advance(max_payload_size - 2);
                    self.state = PacketizerState::InFragment {
                        timestamp,
                        hdr,
                        left: left + 2 - u32::from(self.max_payload_size),
                        data,
                    };
                } else {
                    let usize_left = crate::to_usize(left);
                    payload = Vec::with_capacity(usize_left + 2);
                    let fu_indicator = (hdr.nal_ref_idc() << 5) | 28;
                    let fu_header = 0b0100_0000 | hdr.nal_unit_type().id(); // END bit set.
                    payload.extend_from_slice(&[fu_indicator, fu_header]);
                    payload.extend_from_slice(&data[..usize_left]);
                    if data.len() == usize_left {
                        mark = true;
                        self.state = PacketizerState::Idle;
                    } else {
                        mark = false;
                        data.advance(usize_left);
                        self.state = PacketizerState::HaveData { timestamp, data };
                    }
                }
                // TODO: placeholders.
                Ok(Some(
                    ReceivedPacketBuilder {
                        ctx: crate::PacketContext::dummy(),
                        stream_id: self.stream_id,
                        timestamp,
                        ssrc: self.ssrc,
                        sequence_number,
                        loss: 0,
                        mark,
                        payload_type: self.payload_type,
                    }
                    .build(payload)?,
                ))
            }
        }
    }
}

enum PacketizerState {
    Idle,

    /// Have NALs to send; not in the middle of a fragmented packet.
    HaveData {
        timestamp: Timestamp,

        /// Positioned before the length of a NAL.
        data: Bytes,
    },
    InFragment {
        timestamp: Timestamp,
        hdr: NalHeader,

        /// The number of non-header payload bytes to send in this NAL.
        left: u32,

        /// Positioned at the next non-header payload byte of this NAL.
        data: Bytes,
    },
}

#[cfg(test)]
mod tests {
    use super::process_annex_b;
    use crate::{
        codec::CodecItem,
        rtp::ReceivedPacketBuilder,
        testutil::{assert_eq_hex, assert_eq_hexes, init_logging},
        Timestamp, VideoTimestamp,
    };
    use bytes::Bytes;
    use pretty_assertions::assert_eq;
    use std::num::NonZeroU32;

    /*
     * This test requires
     * 1.  a hacked version of the "mp4" crate to fix a couple bugs
     * 2.  a copy of a .mp4 or .mov file
     * so it's disabled.
    #[test]
    fn roundtrip_using_mp4() {
        use crate::Timestamp;
        use pretty_hex::PrettyHex;
        use std::convert::TryFrom;
        crate::testutil::init_logging();
        let mut p = super::Packetizer::new(1400, 0, 0).unwrap();
        let mut d = super::Depacketizer::new(
            90_000,
            Some("packetization-mode=1;sprop-parameter-sets=J01AHqkYGwe83gDUBAQG2wrXvfAQ,KN4JXGM4"))
            .unwrap();
        let mut f = mp4::read_mp4(std::fs::File::open("src/codec/testdata/big_buck_bunny_480p_h264.mov").unwrap()).unwrap();
        let h264_track = f.tracks().iter().find_map(|t| {
            if matches!(t.media_type(), Ok(mp4::MediaType::H264)) {
                log::info!("sps: {:?}", t.sequence_parameter_set().unwrap().hex_dump());
                log::info!("pps: {:?}", t.picture_parameter_set().unwrap().hex_dump());
                Some(t.track_id())
            } else {
                None
            }
        }).unwrap();
        let samples = f.sample_count(h264_track).unwrap();
        for i in 1..=samples {
            let sample = f.read_sample(h264_track, i).unwrap().unwrap();
            //log::info!("packetizing {:#?}", sample.bytes.hex_dump());
            log::info!("\n\npacketizing frame");
            let mut frame = None;
            p.push(Timestamp::new(i64::try_from(sample.start_time).unwrap(), NonZeroU32::new(90_000).unwrap(), 0).unwrap(), sample.bytes.clone()).unwrap();
            while let Some(pkt) = p.pull().unwrap() {
                assert!(frame.is_none());
                d.push(pkt).unwrap();
                assert!(frame.is_none());
                loop {
                    if let Some(f) = d.pull().unwrap() {
                        assert!(frame.is_none());
                        frame = Some(match f {
                            CodecItem::VideoFrame(f) => f,
                            _ => panic!(),
                        });
                    } else {
                        break;
                    }
                }
            }
            assert_eq_hex!(frame.unwrap().data(), &sample.bytes);
        }
    }
     */

    #[test]
    fn depacketize() {
        init_logging();
        let mut d = super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA")).unwrap();
        let timestamp = crate::Timestamp {
            pts: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(
            ReceivedPacketBuilder {
                // plain SEI packet.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(b"\x06plain".iter().copied())
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // STAP-A packet.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x18\x00\x09\x06stap-a 1\x00\x09\x06stap-a 2")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // FU-A packet, start.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x7c\x86fu-a start, ")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // FU-A packet, middle.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 3,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x7c\x06fu-a middle, ")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // FU-A packet, end.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 4,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x7c\x46fu-a end")
            .unwrap(),
        )
        .unwrap();
        let frame = match d.pull() {
            Some(CodecItem::VideoFrame(frame)) => frame,
            _ => panic!(),
        };
        assert_eq_hex!(
            frame.data(),
            b"\x00\x00\x00\x06\x06plain\
                     \x00\x00\x00\x09\x06stap-a 1\
                     \x00\x00\x00\x09\x06stap-a 2\
                     \x00\x00\x00\x22\x66fu-a start, fu-a middle, fu-a end"
        );
    }

    /// Test depacketizing when reserved bit is set on FU-A header.
    /// Longse CMSEKL800 on
    /// firmware KL8_1ND_BVD0L1A0T0Q0_A00038268_V2.0.10.241016_R2
    /// has been found to set this bit - however the resulting
    /// frame is fine.
    #[test]
    fn depacketize_reserved_bit_set() {
        init_logging();
        let mut d = super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA")).unwrap();
        let timestamp = crate::Timestamp {
            pts: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(
            ReceivedPacketBuilder {
                // FU-A packet, start.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x7c\xa6fu-a start, ")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // FU-A packet, middle.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 3,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x7c\x26fu-a middle, ")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // FU-A packet, end.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 4,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x7c\x66fu-a end")
            .unwrap(),
        )
        .unwrap();
        let frame = match d.pull() {
            Some(CodecItem::VideoFrame(frame)) => frame,
            _ => panic!(),
        };
        assert_eq_hex!(
            frame.data(),
            b"\x00\x00\x00\x22\x66fu-a start, fu-a middle, fu-a end"
        );
    }

    /// Test bad framing at the start of stream from a Reolink RLC-822A
    /// Reolink RLC-822A (IPC_523128M8MP) running firmware v3.0.0.177_21012101:
    /// suppress incorrect access unit changes after the SPS and PPS.
    #[test]
    fn depacketize_reolink_bad_framing_at_start() {
        init_logging();
        let mut d = super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=640033;sprop-parameter-sets=Z2QAM6wVFKCgL/lQ,aO48sA==")).unwrap();
        let ts1 = crate::Timestamp {
            pts: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        let ts2 = crate::Timestamp {
            pts: 1,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(
            ReceivedPacketBuilder {
                // SPS with (incorrect) mark
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp: ts1,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x67\x64\x00\x33\xac\x15\x14\xa0\xa0\x2f\xf9\x50")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // PPS
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp: ts1,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x68\xee\x3c\xb0")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // Slice layer without partitioning IDR.
                // This has a different timestamp than the SPS and PPS, even though
                // RFC 6184 section 5.1 says that "the timestamp must match that of
                // the primary coded picture of the access unit and that the marker
                // bit can only be set on the final packet of the access unit.""
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp: ts2,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x65slice")
            .unwrap(),
        )
        .unwrap();
        let frame = match d.pull() {
            Some(CodecItem::VideoFrame(frame)) => frame,
            o => panic!("unexpected pull result {o:#?}"),
        };
        assert_eq_hex!(
            frame.data(),
            b"\x00\x00\x00\x0C\x67\x64\x00\x33\xac\x15\x14\xa0\xa0\x2f\xf9\x50\
              \x00\x00\x00\x04\x68\xee\x3c\xb0\
              \x00\x00\x00\x06\x65slice"
        );
        let want = VideoTimestamp {
            timestamp: Timestamp {
                pts: 1,
                clock_rate: NonZeroU32::new(90_000).unwrap(),
                start: 0,
            },
            dts: Some(1),
        };
        assert_eq!(frame.timestamp, want); // use the timestamp from the video frame.
    }

    /// Test bad framing at a GOP boundary in a stream from a Reolink RLC-822A
    /// Reolink RLC-822A (IPC_523128M8MP) running firmware v3.0.0.177_21012101:
    /// suppress incorrect access unit changes after the SPS and PPS.
    #[test]
    fn depacketize_reolink_gop_boundary() {
        init_logging();
        let mut d = super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=640033;sprop-parameter-sets=Z2QAM6wVFKCgL/lQ,aO48sA==")).unwrap();
        let ts1 = crate::Timestamp {
            pts: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        let ts2 = crate::Timestamp {
            pts: 1,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(
            ReceivedPacketBuilder {
                // Slice layer without partitioning non-IDR, representing the
                // last frame of the previous GOP.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp: ts1,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x01slice")
            .unwrap(),
        )
        .unwrap();
        let frame = match d.pull() {
            Some(CodecItem::VideoFrame(frame)) => frame,
            o => panic!("unexpected pull result {o:#?}"),
        };
        assert_eq_hex!(frame.data(), b"\x00\x00\x00\x06\x01slice");
        let want = VideoTimestamp {
            timestamp: Timestamp {
                pts: 0,
                clock_rate: NonZeroU32::new(90_000).unwrap(),
                start: 0,
            },
            dts: Some(0),
        };
        assert_eq!(frame.timestamp, want);
        d.push(
            ReceivedPacketBuilder {
                // SPS with (incorrect) timestamp matching last frame.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp: ts1,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false, // correctly has no mark, unlike first SPS in stream.
                payload_type: 0,
            }
            .build(*b"\x67\x64\x00\x33\xac\x15\x14\xa0\xa0\x2f\xf9\x50")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // PPS, again with timestamp matching last frame.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp: ts1,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x68\xee\x3c\xb0")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // Slice layer without partitioning IDR. Now correct timestamp.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp: ts2,
                ssrc: 0,
                sequence_number: 3,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x65slice")
            .unwrap(),
        )
        .unwrap();
        let frame = match d.pull() {
            Some(CodecItem::VideoFrame(frame)) => frame,
            o => panic!("unexpected pull result {o:#?}"),
        };
        assert_eq_hex!(
            frame.data(),
            b"\x00\x00\x00\x0C\x67\x64\x00\x33\xac\x15\x14\xa0\xa0\x2f\xf9\x50\
              \x00\x00\x00\x04\x68\xee\x3c\xb0\
              \x00\x00\x00\x06\x65slice"
        );
        let want = VideoTimestamp {
            timestamp: Timestamp {
                pts: 1,
                clock_rate: NonZeroU32::new(90_000).unwrap(),
                start: 0,
            },
            dts: Some(1),
        };
        assert_eq!(frame.timestamp, want); // use the timestamp from the video frame.
    }

    #[test]
    fn depacketize_parameter_change() {
        init_logging();
        let mut d = super::Depacketizer::new(90_000, Some("a=fmtp:96 packetization-mode=1;profile-level-id=4d002a;sprop-parameter-sets=Z00AKp2oHgCJ+WbgICAoAAADAAgAAAMAfCA=,aO48gA==")).unwrap();
        match d.parameters() {
            Some(crate::codec::ParametersRef::Video(v)) => {
                assert_eq!(v.pixel_dimensions(), (1920, 1080));
            }
            o => panic!("{o:?}"),
        }
        let timestamp = crate::Timestamp {
            pts: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(ReceivedPacketBuilder { // new SPS.
            ctx: crate::PacketContext::dummy(),
            stream_id: 0,
            timestamp,
            ssrc: 0,
            sequence_number: 0,
            loss: 0,
            mark: false,
            payload_type: 0,
        }.build(*b"\x67\x4d\x40\x1e\x9a\x64\x05\x01\xef\xf3\x50\x10\x10\x14\x00\x00\x0f\xa0\x00\x01\x38\x80\x10").unwrap()).unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // same PPS again.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x68\xee\x3c\x80")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // dummy slice NAL to end the AU.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x65slice")
            .unwrap(),
        )
        .unwrap();

        // By codec::Depacketizer::parameters's contract, it's unspecified what the depacketizer
        // parameters are set to between push and pull.

        let frame = match d.pull() {
            Some(CodecItem::VideoFrame(frame)) => frame,
            o => panic!("unexpected pull result {o:#?}"),
        };

        // After pull, new_parameters and parameters() both reflect the change.
        assert!(frame.has_new_parameters);
        match d.parameters() {
            Some(crate::codec::ParametersRef::Video(v)) => {
                assert_eq!(v.pixel_dimensions(), (640, 480));
            }
            _ => unreachable!(),
        }
    }

    /// Tests parsing empty parameters, which can for example happen with
    /// v4l2-rtspserver if the hardware hasn't given it a frame with the required data yet.
    /// (Mostly that it should not panic.)
    #[test]
    fn depacketize_empty() {
        init_logging();
        assert!(super::InternalParameters::parse_format_specific_params("").is_err());
        assert!(super::InternalParameters::parse_format_specific_params(" ").is_err());
    }

    /// Tests parsing parameters from GW Security camera, which erroneously puts
    /// an Annex B NAL separator at the end of each of the `sprop-parameter-sets` NALs.
    #[test]
    fn gw_security_params() {
        init_logging();
        let p = super::InternalParameters::parse_format_specific_params(
            "packetization-mode=1;\
             profile-level-id=5046302;\
             sprop-parameter-sets=Z00AHpWoLQ9puAgICBAAAAAB,aO48gAAAAAE=",
        )
        .unwrap();
        assert_eq!(p.generic_parameters.rfc6381_codec, "avc1.4D001E");
    }

    #[test]
    fn bad_format_specific_params() {
        init_logging();
        // These bad parameters are taken from a VStarcam camera. The sprop-parameter-sets
        // don't start with proper NAL headers. (They look almost like the raw RBSP of each
        // NAL plus extra trailing NUL bytes?)
        // https://github.com/scottlamb/retina/issues/42
        const BAD_PARAMS: &str = "packetization-mode=1;\
                                  profile-level-id=00f004;\
                                  sprop-parameter-sets=6QDwBE/LCAAAH0gAB1TgIAAAAAA=,AAAAAA==";
        super::InternalParameters::parse_format_specific_params(BAD_PARAMS).unwrap_err();

        // Creating a depacketizer should ignore (and log) the bad parameters.
        let mut d = super::Depacketizer::new(90_000, Some(BAD_PARAMS)).unwrap();
        assert!(d.parameters().is_none());

        // The stream should honor in-band parameters.
        let timestamp = crate::Timestamp {
            pts: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(ReceivedPacketBuilder {
            // SPS
            ctx: crate::PacketContext::dummy(),
            stream_id: 0,
            timestamp,
            ssrc: 0,
            sequence_number: 0,
            loss: 0,
            mark: false,
            payload_type: 0,
        }.build(
            *b"\x67\x4d\x00\x28\xe9\x00\xf0\x04\x4f\xcb\x08\x00\x00\x1f\x48\x00\x07\x54\xe0\x20",
        ).unwrap()).unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // PPS
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x68\xea\x8f\x20")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // IDR slice
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x65idr slice")
            .unwrap(),
        )
        .unwrap();
        let frame = match d.pull() {
            Some(CodecItem::VideoFrame(frame)) => frame,
            _ => panic!(),
        };
        assert!(frame.has_new_parameters);
        assert!(d.parameters().is_some());
    }

    #[test]
    fn sps_with_extra_trailing_bytes() {
        init_logging();
        // https://github.com/scottlamb/retina/issues/102
        const PARAMS: &str = "packetization-mode=1;profile-level-id=640033";
        let mut d = super::Depacketizer::new(90_000, Some(PARAMS)).unwrap();
        assert!(d.parameters().is_none());

        // The stream should honor in-band parameters, even with an extra byte.
        let timestamp = crate::Timestamp {
            pts: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(ReceivedPacketBuilder {
            // SPS
            ctx: crate::PacketContext::dummy(),
            stream_id: 0,
            timestamp,
            ssrc: 0,
            sequence_number: 0,
            loss: 0,
            mark: false,
            payload_type: 0,
        }.build(
            *b"\x67\x64\x00\x33\xac\x15\x14\xa0\xa0\x3d\xa1\x00\x00\x04\xf6\x00\x00\x63\x38\x04\x04",
        ).unwrap()).unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // PPS
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x68\xee\x3c\xb0")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // IDR slice
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x65idr slice")
            .unwrap(),
        )
        .unwrap();
        let frame = match d.pull() {
            Some(CodecItem::VideoFrame(frame)) => frame,
            _ => panic!(),
        };
        assert!(frame.has_new_parameters);
        assert!(d.parameters().is_some());
    }

    #[rustfmt::skip]
    static ANNEX_B_NALS: [u8; 44] = [
        // SPS
        0x67, 0x64, 0x00, 0x33, 0xac, 0x15, 0x14, 0xa0, 0xa0, 0x3d, 0xa1, 0x00, 0x00, 0x04, 0xf6,
        0x00, 0x00, 0x63, 0x38, 0x04,
        0x00, 0x00, 0x00, 0x01,
        // PPS
        0x68, 0xee, 0x3c, 0xb0, 0x00, 0x00, 0x01,
        // IDR slice
        0x65, b'i', b'd', b'r', b' ', b's', b'l', b'i', 0x00, 0x00, b'c', b'e', 0x00,
    ];

    #[rustfmt::skip]
    static PREFIXED_NALS: [u8; 48] = [
        // SPS
        0x00, 0x00, 0x00, 0x14,
        0x67, 0x64, 0x00, 0x33, 0xac, 0x15, 0x14, 0xa0, 0xa0, 0x3d, 0xa1,
        0x00, 0x00, 0x04, 0xf6, 0x00, 0x00, 0x63, 0x38, 0x04,
        // PPS
        0x00, 0x00, 0x00, 0x04,
        0x68, 0xee, 0x3c, 0xb0,
        // IDR slice
        0x00, 0x00, 0x00, 0x0c,
        0x65, b'i', b'd', b'r', b' ', b's', b'l', b'i', 0x00, 0x00, b'c', b'e',
    ];

    /// Tests that the depacketizer can handle Annex B separators in a "single-NAL" unit type.
    ///
    /// One bit of nuance here is that the Annex B separation has to happen *before* the
    /// `can_end_au` logic, as the initial NAL unit type is one that can not end a NAL.
    #[test]
    fn parse_annex_b_single_nal() {
        init_logging();
        let mut d =
            super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=640033"))
                .unwrap();
        let timestamp = crate::Timestamp {
            pts: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
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
            .build(ANNEX_B_NALS)
            .unwrap(),
        )
        .unwrap();
        let CodecItem::VideoFrame(frame) = d.pull().unwrap() else {
            panic!();
        };
        assert_eq_hex!(frame.data(), &PREFIXED_NALS);
    }

    /// Tests that the depacketizer can handle Annex B separators in a FU-A unit,
    /// split across multiple packets.
    #[test]
    fn parse_annex_b_fu_a() {
        init_logging();
        for first_pkt_len in 2..ANNEX_B_NALS.len() - 1 {
            for middle_pkt_len in [0, 1, 2, 3] {
                if first_pkt_len + middle_pkt_len >= ANNEX_B_NALS.len() {
                    continue;
                }
                println!(
                    "first_pkt_len={}, middle_pkt_len={}, last_pkt_len={}",
                    first_pkt_len,
                    middle_pkt_len,
                    ANNEX_B_NALS.len() - first_pkt_len - middle_pkt_len
                );
                let mut d = super::Depacketizer::new(
                    90_000,
                    Some("packetization-mode=1;profile-level-id=640033"),
                )
                .unwrap();
                let timestamp = crate::Timestamp {
                    pts: 0,
                    clock_rate: NonZeroU32::new(90_000).unwrap(),
                    start: 0,
                };
                let mut first_pkt = Vec::with_capacity(first_pkt_len + 1);
                first_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                first_pkt.push((ANNEX_B_NALS[0] & 0b0001_1111) | 0b1000_0000); // start
                first_pkt.extend_from_slice(&ANNEX_B_NALS[1..first_pkt_len]);
                println!("  pushing first pkt");
                d.push(
                    ReceivedPacketBuilder {
                        ctx: crate::PacketContext::dummy(),
                        stream_id: 0,
                        timestamp,
                        ssrc: 0,
                        sequence_number: 0,
                        loss: 0,
                        mark: false,
                        payload_type: 0,
                    }
                    .build(first_pkt)
                    .unwrap(),
                )
                .unwrap();
                assert!(d.pull().is_none());
                if middle_pkt_len > 0 {
                    let mut middle_pkt = Vec::with_capacity(middle_pkt_len + 2);
                    middle_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                    middle_pkt.push(ANNEX_B_NALS[0] & 0b0001_1111); // middle
                    middle_pkt.extend_from_slice(
                        &ANNEX_B_NALS[first_pkt_len..first_pkt_len + middle_pkt_len],
                    );
                    println!("  pushing middle pkt");
                    d.push(
                        ReceivedPacketBuilder {
                            ctx: crate::PacketContext::dummy(),
                            stream_id: 0,
                            timestamp,
                            ssrc: 0,
                            sequence_number: 1,
                            loss: 0,
                            mark: false,
                            payload_type: 0,
                        }
                        .build(middle_pkt)
                        .unwrap(),
                    )
                    .unwrap();
                    assert!(d.pull().is_none());
                }
                let mut last_pkt =
                    Vec::with_capacity(ANNEX_B_NALS.len() - first_pkt_len - middle_pkt_len + 2);
                last_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                last_pkt.push((ANNEX_B_NALS[0] & 0b0001_1111) | 0b0100_0000); // end
                last_pkt.extend_from_slice(&ANNEX_B_NALS[first_pkt_len + middle_pkt_len..]);
                println!("  pushing last pkt");
                d.push(
                    ReceivedPacketBuilder {
                        ctx: crate::PacketContext::dummy(),
                        stream_id: 0,
                        timestamp,
                        ssrc: 0,
                        sequence_number: 2,
                        loss: 0,
                        mark: true,
                        payload_type: 0,
                    }
                    .build(last_pkt)
                    .unwrap(),
                )
                .unwrap();
                println!("  pulling");
                let CodecItem::VideoFrame(frame) = d.pull().unwrap() else {
                    panic!();
                };
                assert_eq_hex!(frame.data(), &PREFIXED_NALS);
            }
        }
    }

    #[test]
    fn exit_on_inconsistent_headers_between_fu_a() {
        init_logging();
        let mut d = super::Depacketizer::new(90_000, Some("profile-level-id=TQAf;packetization-mode=1;sprop-parameter-sets=J00AH+dAKALdgKUFBQXwAAADABAAAAMCiwEAAtxoAAIlUX//AoA=,KO48gA==")).unwrap();
        let timestamp = crate::Timestamp {
            pts: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(
            ReceivedPacketBuilder {
                // FU-A start fragment
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x3c\x81start of non-idr")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());

        let push_result = d.push(
            ReceivedPacketBuilder {
                // FU-A packet, middle.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x3c\x07a wild sps appeared")
            .unwrap(),
        );
        assert!(push_result.is_err());
    }

    /// Tests the `process_annex_b` function in isolation.
    #[test]
    fn annex_b_parsing() {
        init_logging();

        // Essentially empty inputs.
        process_annex_b(Bytes::from_static(&[]), |_| panic!()).unwrap();
        process_annex_b(Bytes::from_static(&[0x00]), |_| panic!()).unwrap();
        process_annex_b(Bytes::from_static(&[0x00, 0x00, 0x01]), |_| panic!()).unwrap();
        process_annex_b(Bytes::from_static(&[0x00, 0x00, 0x00, 0x01]), |_| panic!()).unwrap();

        // Single NAL unit.
        let mut nals = vec![];
        process_annex_b(Bytes::from_static(&[1, 2, 3, 4]), |nal| {
            nals.push(nal);
            Ok(())
        })
        .unwrap();
        assert_eq_hexes!(nals, [Bytes::from_static(&[1, 2, 3, 4])]);
        nals.clear();
        process_annex_b(Bytes::from_static(&[0, 0, 1, 1, 2, 3, 4]), |nal| {
            nals.push(nal);
            Ok(())
        })
        .unwrap();
        assert_eq_hexes!(nals, [Bytes::from_static(&[1, 2, 3, 4])]);
        nals.clear();
        process_annex_b(Bytes::from_static(&[1, 2, 3, 4, 0, 0, 1]), |nal| {
            nals.push(nal);
            Ok(())
        })
        .unwrap();
        assert_eq_hexes!(nals, [Bytes::from_static(&[1, 2, 3, 4])]);

        // Error path.
        assert_eq!(
            process_annex_b(Bytes::from_static(&[1, 2, 3, 4, 0, 0, 1]), |_| {
                Err("asdf".into())
            }),
            Err("asdf".into()),
        );

        // Multiple NAL units.
        nals.clear();
        process_annex_b(Bytes::from_static(&[0, 0, 1, 1, 0, 0, 1, 2, 3, 4]), |nal| {
            nals.push(nal);
            Ok(())
        })
        .unwrap();
        assert_eq_hexes!(
            nals,
            [Bytes::from_static(&[1]), Bytes::from_static(&[2, 3, 4])]
        );
    }
}
