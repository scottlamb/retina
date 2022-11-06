// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [H.264](https://www.itu.int/rec/T-REC-H.264-201906-I/en)-encoded video.

use std::convert::TryFrom;
use std::fmt::Write;

use base64::Engine as _;
use bytes::{Buf, BufMut, Bytes, BytesMut};
use h264_reader::nal::{NalHeader, UnitType};
use log::{debug, log_enabled, trace};

use crate::{
    rtp::{ReceivedPacket, ReceivedPacketBuilder},
    Error, Timestamp,
};

use super::VideoFrame;

/// A [super::Depacketizer] implementation which finds access unit boundaries
/// and produces unfragmented NAL units as specified in [RFC
/// 6184](https://tools.ietf.org/html/rfc6184).
///
/// This doesn't inspect the contents of the NAL units, so it doesn't depend on or
/// verify compliance with H.264 section 7.4.1.2.3 "Order of NAL units and coded
/// pictures and association to access units".
///
/// Currently expects that the stream starts at an access unit boundary unless
/// packet loss is indicated.
#[derive(Debug)]
pub(crate) struct Depacketizer {
    input_state: DepacketizerInputState,

    /// A complete video frame ready for pull.
    pending: Option<VideoFrame>,

    parameters: Option<InternalParameters>,

    /// Holds NALs from RTP packets.
    nal_parser: NalParser,
}

/// Parses Annex B sequences from RTP NAL data.
///
/// RFC 6184 describes how NAL units should be represented by RTP packets. `Depacketizer` should map each
/// such NAL unit to 1 call to `NalParser::start_rtp_nal`, then 1 or more calls to `NalParser::append_rtp_nal`,
/// then 1 call to `NalParser::end_rtp_nal`.
///
/// If the camera complies with the RFC, this will add exactly one NAL unit. However, what some cameras
/// call a single NAL unit is actually a sequence of multiple NAL units with Annex B separators. `NalParser`
/// looks for these separators and adds multiple NAL units as needed.
/// See [scottlamb/retina#68](https://github.com/scottlamb/retina/issues/68).
#[derive(Debug)]
struct NalParser {
    /// In state `PreMark`, pieces of NALs, excluding their header bytes.
    /// Kept around (empty) in other states to re-use the backing allocation.
    pieces: Vec<Bytes>,

    /// In state `PreMark`, an entry for each NAL.
    /// Kept around (empty) in other states to re-use the backing allocation.
    nals: Vec<Nal>,

    // annex b delimiter watcher state
    did_find_boundary: bool,
}

impl NalParser {
    fn new() -> Self {
        NalParser {
            pieces: Vec::new(),
            nals: Vec::new(),
            did_find_boundary: false,
        }
    }

    /// Helper function to clear `NalParser::nals` and `NalParser::pieces` vectors.
    fn clear(&mut self) {
        self.nals.clear();
        self.pieces.clear()
    }

    /// Adds a piece to `self.pieces`. Returns the total length of pieces after adding,
    /// erroring if it becomes absurdly large.
    fn add_piece(&mut self, piece: Bytes) -> Result<u32, String> {
        self.pieces.push(piece);
        u32::try_from(self.pieces.len()).map_err(|_| "more than u32::MAX pieces!".to_string())
    }

    /// Given a byte buffer, it checks if the buffer is an Annex B stream by looking for
    /// boundaries (i.e. three consecutive 0x00). If it finds a boundary, it splits on it
    /// to break apart NALs from the Annex B stream.
    fn break_apart_nals(&mut self, data: Bytes) -> Result<bool, String> {
        let mut nal_start_idx = 0;
        for (idx, byte) in data.iter().enumerate() {
            if byte == &0x00 && idx + 2 < data.len() && &data[idx..idx + 3] == &[0x00; 3] {
                debug!("Found boundary with index range: {} - {}.", idx, idx + 2);
                // we found a boundary, let NalParser know that it should now keep adding
                // to last NAL even if the next FU-A frag header byte does not match the
                // header of the last saved NAL.
                self.did_find_boundary = true;
                let nal_end_idx = idx;

                let nal = data.slice(
                    if nal_start_idx == 0 {
                        // this is only for the first boundary, since `data` passed already has advanced 2 bytes
                        // to skip the packet type and NAL header
                        nal_start_idx
                    } else {
                        // ignore the first two bytes when saving NAL (Packet type header & NAL header)
                        nal_start_idx + 2
                    }..nal_end_idx,
                );

                // close previous nal
                self.push(nal)?;

                nal_start_idx = idx + 3;

                // create new nal which'll get updated
                let nal_header = data[idx + 4];
                self.nals.push(Nal {
                    hdr: NalHeader::new(nal_header).expect("header w/o F bit set is valid"),
                    next_piece_idx: u32::MAX,
                    len: 1,
                });
            }
        }

        // if we had found a boundary, we need to add the last NAL to pieces now
        if self.did_find_boundary {
            self.push(data.slice(nal_start_idx + 2..))?;
        }

        Ok(self.did_find_boundary)
    }

    /// Creates NAL from RTP packet
    fn start_rtp_nal(&mut self, nal_header: NalHeader) -> Result<(), String> {
        // Normal FU-A flow which conforms to the spec.
        self.nals.push(Nal {
            hdr: nal_header,
            next_piece_idx: u32::MAX, // should be overwritten later.
            len: 1,                   // should be overwritten in case of Annex B stream in FU-A
        });

        Ok(())
    }

    /// Appends data from RTP packet to `NalParser::pieces`
    fn append_rtp_nal(&mut self, data: Bytes) -> Result<(), String> {
        // handle Annex B stream if present (https://github.com/scottlamb/retina/issues/68)
        let did_find_boundary = self.break_apart_nals(data.clone())?;

        // if we had found boundary, we already handled adding pieces, so no need
        // to add pieces again
        if did_find_boundary {
            // reset annex b watcher state
            self.reset_annex_b_watcher();
            return Ok(());
        }

        // otherwise, add pieces as per normal flow
        self.push(data)?;
        Ok(())
    }

    /// Adds bytes to `pieces` and updates last `Nal`.
    fn push(&mut self, data: Bytes) -> Result<(), String> {
        let pieces = self.add_piece(data.clone())?;
        let last_nal = self.nals.last_mut().expect("nals non-empty while in FU-A");
        last_nal.next_piece_idx = pieces;
        last_nal.len += u32::try_from(data.len()).expect("u16 < u32::MAX");
        Ok(())
    }

    /// Helper function to reset Annex B watcher so it can start fresh on new RTP packets
    fn reset_annex_b_watcher(&mut self) {
        self.did_find_boundary = false;
    }
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
    timestamp: crate::Timestamp,
    stream_id: usize,

    /// Holds a value iff currently processing a FU-A. Stores the first [NalHeader] of the starting FU-A.
    in_fu_a: Option<NalHeader>,

    /// RTP packets lost as this access unit was starting.
    loss: u16,

    same_ts_as_prev: bool,
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
            parameters,
            nal_parser: NalParser::new(),
        })
    }

    pub(super) fn parameters(&self) -> Option<super::ParametersRef> {
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
                    debug_assert!(self.nal_parser.nals.is_empty());
                    debug_assert!(self.nal_parser.pieces.is_empty());
                    AccessUnit::start(&pkt, 0, false)
                }
                DepacketizerInputState::PreMark(mut access_unit) => {
                    let loss = pkt.loss();
                    if loss > 0 {
                        self.nal_parser.clear();
                        if access_unit.timestamp.timestamp == pkt.timestamp().timestamp {
                            // Loss within this access unit. Ignore until mark or new timestamp.
                            self.input_state = if pkt.mark() {
                                DepacketizerInputState::PostMark {
                                    timestamp: pkt.timestamp(),
                                    loss,
                                }
                            } else {
                                self.nal_parser.clear();
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
                    } else if access_unit.timestamp.timestamp != pkt.timestamp().timestamp {
                        if access_unit.in_fu_a.is_some() {
                            return Err(format!(
                                "Timestamp changed from {} to {} in the middle of a fragmented NAL",
                                access_unit.timestamp,
                                pkt.timestamp()
                            ));
                        }
                        let last_nal_hdr = self.nal_parser.nals.last().unwrap().hdr;
                        if can_end_au(last_nal_hdr.nal_unit_type()) {
                            access_unit.end_ctx = *pkt.ctx();
                            self.pending =
                                Some(self.finalize_access_unit(access_unit, "ts change")?);
                            AccessUnit::start(&pkt, 0, false)
                        } else {
                            log::debug!(
                                "Bogus mid-access unit timestamp change after {:?}",
                                last_nal_hdr
                            );
                            access_unit.timestamp.timestamp = pkt.timestamp().timestamp;
                            access_unit
                        }
                    } else {
                        access_unit
                    }
                }
                DepacketizerInputState::PostMark {
                    timestamp: state_ts,
                    loss,
                } => {
                    debug_assert!(self.nal_parser.nals.is_empty());
                    debug_assert!(self.nal_parser.pieces.is_empty());
                    AccessUnit::start(&pkt, loss, state_ts.timestamp == pkt.timestamp().timestamp)
                }
                DepacketizerInputState::Loss {
                    timestamp,
                    mut pkts,
                } => {
                    debug_assert!(self.nal_parser.nals.is_empty());
                    debug_assert!(self.nal_parser.pieces.is_empty());
                    if pkt.timestamp().timestamp == timestamp.timestamp {
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
        if data.is_empty() {
            return Err("Empty NAL".into());
        }
        // https://tools.ietf.org/html/rfc6184#section-5.2
        let nal_header = data[0];
        if (nal_header >> 7) != 0 {
            return Err(format!("NAL header {nal_header:02x} has F bit set"));
        }
        data.advance(1); // skip the header byte.
        match nal_header & 0b11111 {
            1..=23 => {
                if access_unit.in_fu_a.is_some() {
                    return Err(format!(
                        "Non-fragmented NAL {nal_header:02x} while fragment in progress"
                    ));
                }
                let len = u32::try_from(data.len()).expect("data len < u16::MAX") + 1;
                let next_piece_idx = self.nal_parser.add_piece(data)?;
                self.nal_parser.nals.push(Nal {
                    hdr: NalHeader::new(nal_header).expect("header w/o F bit set is valid"),
                    next_piece_idx,
                    len,
                });
            }
            24 => {
                // STAP-A. https://tools.ietf.org/html/rfc6184#section-5.7.1
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
                    let hdr = NalHeader::new(data[0])
                        .map_err(|_| format!("bad header {:02x} in STAP-A", data[0]))?;
                    match data.remaining().cmp(&usize::from(len)) {
                        std::cmp::Ordering::Less => {
                            return Err(format!(
                                "STAP-A too short: {} bytes remaining, expecting {}-byte NAL",
                                data.remaining(),
                                len
                            ))
                        }
                        std::cmp::Ordering::Equal => {
                            data.advance(1);
                            let next_piece_idx = self.nal_parser.add_piece(data)?;
                            self.nal_parser.nals.push(Nal {
                                hdr,
                                next_piece_idx,
                                len: u32::from(len),
                            });
                            break;
                        }
                        std::cmp::Ordering::Greater => {
                            let mut piece = data.split_to(usize::from(len));
                            piece.advance(1);
                            let next_piece_idx = self.nal_parser.add_piece(piece)?;
                            self.nal_parser.nals.push(Nal {
                                hdr,
                                next_piece_idx,
                                len: u32::from(len),
                            });
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
                if data.len() < 2 {
                    return Err(format!("FU-A len {} too short", data.len()));
                }
                let fu_header = data[0];
                let start = (fu_header & 0b10000000) != 0;
                let end = (fu_header & 0b01000000) != 0;
                let reserved = (fu_header & 0b00100000) != 0;
                let nal_header =
                    NalHeader::new((nal_header & 0b011100000) | (fu_header & 0b00011111))
                        .expect("NalHeader is valid");
                data.advance(1);
                if (start && end) || reserved {
                    return Err(format!("Invalid FU-A header {fu_header:02x}"));
                }
                if !end && mark {
                    return Err("FU-A pkt with MARK && !END".into());
                }
                match (start, access_unit.in_fu_a) {
                    (true, Some(_)) => {
                        return Err("FU-A with start bit while frag in progress".into())
                    }
                    (true, None) => {
                        self.nal_parser.start_rtp_nal(nal_header)?;
                        self.nal_parser.append_rtp_nal(data)?;
                        access_unit.in_fu_a = Some(nal_header);
                    }
                    (false, Some(header_of_starting_fu_a)) => {
                        self.nal_parser.append_rtp_nal(data)?;
                        if u8::from(nal_header) != u8::from(header_of_starting_fu_a) {
                            return Err(format!(
                                "FU-A has inconsistent NAL type: {:?} then {:?}",
                                header_of_starting_fu_a, nal_header,
                            ));
                        }
                        if end {
                            access_unit.in_fu_a = None;
                        } else if mark {
                            return Err("FU-A has MARK and no END".into());
                        }
                    }
                    (false, None) => {
                        if loss > 0 {
                            self.nal_parser.clear();
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
            let last_nal_hdr = self.nal_parser.nals.last().unwrap().hdr;
            if can_end_au(last_nal_hdr.nal_unit_type()) {
                access_unit.end_ctx = ctx;
                self.pending = Some(self.finalize_access_unit(access_unit, "mark")?);
                DepacketizerInputState::PostMark { timestamp, loss: 0 }
            } else {
                log::debug!(
                    "Bogus mid-access unit timestamp change after {:?}",
                    last_nal_hdr
                );
                access_unit.timestamp.timestamp = timestamp.timestamp;
                DepacketizerInputState::PreMark(access_unit)
            }
        } else {
            DepacketizerInputState::PreMark(access_unit)
        };
        Ok(())
    }

    pub(super) fn pull(&mut self) -> Option<super::CodecItem> {
        self.pending.take().map(super::CodecItem::VideoFrame)
    }

    /// Logs information about each access unit.
    /// Currently, "bad" access units (violating certain specification rules)
    /// are logged at debug priority, and others are logged at trace priority.
    fn log_access_unit(&self, au: &AccessUnit, reason: &str) {
        let mut errs = String::new();
        if au.same_ts_as_prev {
            errs.push_str("\n* same timestamp as previous access unit");
        }
        validate_order(&self.nal_parser.nals, &mut errs);
        if !errs.is_empty() {
            let mut nals = String::new();
            for (i, nal) in self.nal_parser.nals.iter().enumerate() {
                let _ = write!(&mut nals, "\n  {}: {:?}", i, nal.hdr);
            }
            debug!(
                "bad access unit (ended by {}) at ts {}\nerrors are:{}\nNALs are:{}",
                reason, au.timestamp, errs, nals
            );
        } else if log_enabled!(log::Level::Trace) {
            let mut nals = String::new();
            for (i, nal) in self.nal_parser.nals.iter().enumerate() {
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
        let mut is_random_access_point = false;
        let mut is_disposable = true;
        let mut new_sps = None;
        let mut new_pps = None;

        if log_enabled!(log::Level::Debug) {
            self.log_access_unit(&au, reason);
        }
        for nal in &self.nal_parser.nals {
            let next_piece_idx = usize::try_from(nal.next_piece_idx).expect("u32 fits in usize");
            let nal_pieces = &self.nal_parser.pieces[piece_idx..next_piece_idx];
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
                UnitType::SliceLayerWithoutPartitioningIdr => is_random_access_point = true,
                _ => {}
            }
            if nal.hdr.nal_ref_idc() != 0 {
                is_disposable = false;
            }
            // TODO: support optionally filtering non-VUI NALs.
            retained_len += 4usize + usize::try_from(nal.len).expect("u32 fits in usize");
            piece_idx = next_piece_idx;
        }
        let mut data = Vec::with_capacity(retained_len);
        piece_idx = 0;
        for nal in &self.nal_parser.nals {
            let next_piece_idx = usize::try_from(nal.next_piece_idx).expect("u32 fits in usize");
            let nal_pieces = &self.nal_parser.pieces[piece_idx..next_piece_idx];
            data.extend_from_slice(&nal.len.to_be_bytes()[..]);
            data.push(nal.hdr.into());
            let mut actual_len = 1;
            for piece in nal_pieces {
                data.extend_from_slice(&piece[..]);
                actual_len += piece.len();
            }
            debug_assert_eq!(
                usize::try_from(nal.len).expect("u32 fits in usize"),
                actual_len
            );
            piece_idx = next_piece_idx;
        }
        debug_assert_eq!(retained_len, data.len());
        self.nal_parser.clear();

        let has_new_parameters = match (
            new_sps.as_deref(),
            new_pps.as_deref(),
            self.parameters.as_ref(),
        ) {
            (Some(sps_nal), Some(pps_nal), _) => {
                // TODO: could map this to a RtpPacketError more accurately.
                self.parameters = Some(InternalParameters::parse_sps_and_pps(sps_nal, pps_nal)?);
                true
            }
            (Some(_), None, Some(old_ip)) | (None, Some(_), Some(old_ip)) => {
                let sps_nal = new_sps.as_deref().unwrap_or(&old_ip.sps_nal);
                let pps_nal = new_pps.as_deref().unwrap_or(&old_ip.pps_nal);
                // TODO: as above, could map this to a RtpPacketError more accurately.
                self.parameters = Some(InternalParameters::parse_sps_and_pps(sps_nal, pps_nal)?);
                true
            }
            _ => false,
        };
        Ok(VideoFrame {
            has_new_parameters,
            loss: au.loss,
            start_ctx: au.start_ctx,
            end_ctx: au.end_ctx,
            timestamp: au.timestamp,
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
            timestamp: pkt.timestamp(),
            stream_id: pkt.stream_id(),
            in_fu_a: None,

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
                    let _ = write!(errs, "access unit delimiter must be first in AU; was preceded by {:?}",
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

    /// The (single) SPS NAL.
    sps_nal: Bytes,

    /// The (single) PPS NAL.
    pps_nal: Bytes,
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
        for nal in sprop_parameter_sets.split(',') {
            let nal = base64::engine::general_purpose::STANDARD
                .decode(nal)
                .map_err(|_| {
                    "bad sprop-parameter-sets: NAL has invalid base64 encoding".to_string()
                })?;
            if nal.is_empty() {
                return Err("bad sprop-parameter-sets: empty NAL".into());
            }
            let header = h264_reader::nal::NalHeader::new(nal[0])
                .map_err(|_| format!("bad sprop-parameter-sets: bad NAL header {:0x}", nal[0]))?;
            match header.nal_unit_type() {
                UnitType::SeqParameterSet => {
                    if sps_nal.is_some() {
                        return Err("multiple SPSs".into());
                    }
                    sps_nal = Some(nal);
                }
                UnitType::PicParameterSet => {
                    if pps_nal.is_some() {
                        return Err("multiple PPSs".into());
                    }
                    pps_nal = Some(nal);
                }
                _ => return Err("only SPS and PPS expected in parameter sets".into()),
            }
        }
        let sps_nal = sps_nal.ok_or_else(|| "no sps".to_string())?;
        let pps_nal = pps_nal.ok_or_else(|| "no pps".to_string())?;
        Self::parse_sps_and_pps(&sps_nal, &pps_nal)
    }

    fn parse_sps_and_pps(sps_nal: &[u8], pps_nal: &[u8]) -> Result<InternalParameters, String> {
        let sps_rbsp = h264_reader::rbsp::decode_nal(sps_nal).map_err(|_| "bad sps")?;
        if sps_rbsp.len() < 5 {
            return Err("bad sps".into());
        }
        let rfc6381_codec = format!(
            "avc1.{:02X}{:02X}{:02X}",
            sps_rbsp[0], sps_rbsp[1], sps_rbsp[2]
        );
        let sps = h264_reader::nal::sps::SeqParameterSet::from_bits(
            h264_reader::rbsp::BitReader::new(&*sps_rbsp),
        )
        .map_err(|e| format!("Bad SPS: {e:?}"))?;
        debug!("sps: {:#?}", &sps);

        let pixel_dimensions = sps
            .pixel_dimensions()
            .map_err(|e| format!("SPS has invalid pixel dimensions: {e:?}"))?;

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
            },
            sps_nal,
            pps_nal,
        })
    }
}

/// Returns true iff the bytes of `nal` equal the bytes of `[hdr, ..data]`.
fn nal_matches(nal: &[u8], hdr: NalHeader, pieces: &[Bytes]) -> bool {
    if nal.is_empty() || nal[0] != u8::from(hdr) {
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

/// Saves the given NAL to a contiguous Bytes.
fn to_bytes(hdr: NalHeader, len: u32, pieces: &[Bytes]) -> Bytes {
    let len = usize::try_from(len).expect("u32 fits in usize");
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
                let usize_len = usize::try_from(len).expect("u32 fits in usize");
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
                    let usize_left = usize::try_from(left).expect("u32 fits in usize");
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
    use std::num::NonZeroU32;

    use h264_reader::nal::UnitType;

    use crate::testutil::init_logging;
    use crate::{codec::CodecItem, rtp::ReceivedPacketBuilder};

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
            assert_eq!(frame.unwrap().data(), &sample.bytes);
        }
    }
     */

    #[test]
    fn depacketize() {
        init_logging();
        let mut d = super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA")).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 0,
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
        assert_eq!(
            frame.data(),
            b"\x00\x00\x00\x06\x06plain\
                     \x00\x00\x00\x09\x06stap-a 1\
                     \x00\x00\x00\x09\x06stap-a 2\
                     \x00\x00\x00\x22\x66fu-a start, fu-a middle, fu-a end"
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
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        let ts2 = crate::Timestamp {
            timestamp: 1,
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
        assert_eq!(
            frame.data(),
            b"\x00\x00\x00\x0C\x67\x64\x00\x33\xac\x15\x14\xa0\xa0\x2f\xf9\x50\
              \x00\x00\x00\x04\x68\xee\x3c\xb0\
              \x00\x00\x00\x06\x65slice"
        );
        assert_eq!(frame.timestamp, ts2); // use the timestamp from the video frame.
    }

    /// Test bad framing at a GOP boundary in a stream from a Reolink RLC-822A
    /// Reolink RLC-822A (IPC_523128M8MP) running firmware v3.0.0.177_21012101:
    /// suppress incorrect access unit changes after the SPS and PPS.
    #[test]
    fn depacketize_reolink_gop_boundary() {
        init_logging();
        let mut d = super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=640033;sprop-parameter-sets=Z2QAM6wVFKCgL/lQ,aO48sA==")).unwrap();
        let ts1 = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        let ts2 = crate::Timestamp {
            timestamp: 1,
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
        assert_eq!(frame.data(), b"\x00\x00\x00\x06\x01slice");
        assert_eq!(frame.timestamp, ts1);
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
        assert_eq!(
            frame.data(),
            b"\x00\x00\x00\x0C\x67\x64\x00\x33\xac\x15\x14\xa0\xa0\x2f\xf9\x50\
              \x00\x00\x00\x04\x68\xee\x3c\xb0\
              \x00\x00\x00\x06\x65slice"
        );
        assert_eq!(frame.timestamp, ts2); // use the timestamp from the video frame.
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
            timestamp: 0,
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
        super::InternalParameters::parse_format_specific_params(
            "packetization-mode=1;\
             profile-level-id=5046302;\
             sprop-parameter-sets=Z00AHpWoLQ9puAgICBAAAAAB,aO48gAAAAAE=",
        )
        .unwrap_err();
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
            timestamp: 0,
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

    // FU-A packet containing Annex B stream (https://github.com/scottlamb/retina/issues/68)
    #[test]
    fn parse_annex_b_stream_in_fu_a() {
        init_logging();
        let mut d = super::Depacketizer::new(90_000, Some("profile-level-id=TQAf;packetization-mode=1;sprop-parameter-sets=J00AH+dAKALdgKUFBQXwAAADABAAAAMCiwEAAtxoAAIlUX//AoA=,KO48gA==")).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(
            ReceivedPacketBuilder {
                // FU-A start fragment which includes Annex B stream of 3 NALs
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(
            *b"\
            \x3c\x87\
            \x4d\x00\x1f\xe7\x40\x28\x02\xdd\x80\xa5\x05\x05\x05\xf0\x00\x00\x03\x00\x10\x00\x00\x03\x02\x8b\x01\x00\x02\xdc\x68\x00\x02\x25\x51\x7f\xff\x02\x80\
            \x00\x00\x00\
            \x01\x28\
            \xee\x3c\x80\
            \x00\x00\x00\
            \x01\x25\
            idr-slice, "
        )
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());

        // should've parsed Annex B stream from first FU-A frag into 3 NALs (SPS, PPS & IDR slice)
        let number_of_nals_in_first_frag = 3;
        assert!(d.nal_parser.nals.len() == number_of_nals_in_first_frag);
        assert!(d.nal_parser.pieces.len() == number_of_nals_in_first_frag);
        assert!(d.nal_parser.nals[0].hdr.nal_unit_type() == UnitType::SeqParameterSet);
        assert!(d.nal_parser.nals[1].hdr.nal_unit_type() == UnitType::PicParameterSet);
        assert!(
            d.nal_parser.nals[2].hdr.nal_unit_type() == UnitType::SliceLayerWithoutPartitioningIdr
        );

        d.push(
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
            .build(*b"\x3c\x07idr-slice continued, ")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());

        // For Annex B stream in FU-A, make sure we append next frags to the last nal
        // instead of creating a new one from the frag header, since the header is of the starting
        // NAL of previous frag, but instead is supposed to be the continuation of the last NAL from Annex B stream.

        // This test will also test that retina shouldn't panic on receiving different nal headers in frags of
        // a FU-A when the FU-A contains an Annex B stream.

        // no new nals are to be created
        assert!(d.nal_parser.nals.len() == number_of_nals_in_first_frag);
        // data from frag will get appended
        assert!(d.nal_parser.pieces.len() == number_of_nals_in_first_frag + 1);

        d.push(
            ReceivedPacketBuilder {
                // FU-A packet, end.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x3c\x47idr-slice end")
            .unwrap(),
        )
        .unwrap();

        let frame = match d.pull() {
            Some(CodecItem::VideoFrame(frame)) => frame,
            _ => panic!(),
        };
        assert_eq!(
            &frame.data()[..],
            b"\
            \x00\x00\x00\x26\
            \x27\
            \x4d\x00\x1f\xe7\x40\x28\x02\xdd\x80\xa5\x05\x05\x05\xf0\x00\x00\x03\x00\x10\x00\x00\x03\x02\x8b\x01\x00\x02\xdc\x68\x00\x02\x25\x51\x7f\xff\x02\x80\
            \x00\x00\x00\
            \x04\x28\
            \xee\x3c\x80\
            \x00\x00\x00\
            \x2e\x25\
            idr-slice, idr-slice continued, idr-slice end"
        );
    }

    #[test]
    fn exit_on_inconsistent_headers_between_fu_a() {
        init_logging();
        let mut d = super::Depacketizer::new(90_000, Some("profile-level-id=TQAf;packetization-mode=1;sprop-parameter-sets=J00AH+dAKALdgKUFBQXwAAADABAAAAMCiwEAAtxoAAIlUX//AoA=,KO48gA==")).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 0,
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
}
