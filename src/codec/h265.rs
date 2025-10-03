// Copyright (C) 2024 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [H.265](https://www.itu.int/rec/T-REC-H.265)-encoded video,
//! with RTP encoding as in [RFC 7798](https://tools.ietf.org/html/rfc7798).

#[doc(hidden)] // `pub` only for fuzz tests.
pub mod nal;

mod record;

use std::convert::TryFrom;
use std::fmt::Write;

use base64::Engine as _;
use bytes::{Buf, Bytes};
use log::{debug, log_enabled, trace};

use crate::codec::h26x::TolerantBitReader;
use crate::rtp::ReceivedPacket;

use super::VideoFrame;

/// A [super::Depacketizer] implementation which finds access unit boundaries
/// and produces unfragmented NAL units as specified in [RFC
/// 7798](https://tools.ietf.org/html/rfc7798).
///
/// This inspects the contents of the NAL units only minimally, and largely for
/// logging. In particular, it doesn't completely enforce verify compliance with
/// H.265 section 7.4.2.4 "Order of NAL units and association to coded pictures,
/// access units and coded video sequences". For compatibility with some broken
/// cameras that change timestamps mid-AU, it does extend AUs if they end with
/// parameter sets. See `can_end_au`.
///
/// Currently expects that the stream starts at an access unit boundary unless
/// packet loss is indicated.
#[derive(Debug)]
pub(crate) struct Depacketizer {
    input_state: DepacketizerInputState,

    /// A complete video frame ready for pull.
    pending: Option<VideoFrame>,

    parameters: Option<InternalParameters>,

    /// In state `PreMark`, pieces of NALs, excluding their header bytes.
    /// Kept around (empty) in other states to re-use the backing allocation.
    pieces: Vec<Bytes>,

    /// In state `PreMark`, an entry for each NAL.
    /// Kept around (empty) in other states to re-use the backing allocation.
    nals: Vec<Nal>,
}

#[derive(Debug)]
struct Nal {
    hdr: nal::Header,

    /// The length of `Depacketizer::pieces` as this NAL finishes.
    next_piece_idx: u32,

    /// The total length of this NAL, including the 2 header bytes.
    len: u32,
}

/// An access unit that is currently being accumulated during `PreMark` state.
#[derive(Debug)]
struct AccessUnit {
    start_ctx: crate::PacketContext,
    end_ctx: crate::PacketContext,
    timestamp: crate::Timestamp,
    stream_id: usize,

    /// True iff currently processing a FU-A.
    in_fu: bool,

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

/// Takes a `nal::Header` from `data`, advancing the latter.
///
/// Fails if `data` is too short or the NAL header is invalid.
fn take_hdr(data: &mut Bytes) -> Result<nal::Header, String> {
    let mut hdr_bytes = [0u8; 2];
    if data.len() < hdr_bytes.len() {
        return Err("Short NAL".into());
    };
    data.copy_to_slice(&mut hdr_bytes);
    nal::Header::try_from(hdr_bytes).map_err(|e| e.0)
}

impl Depacketizer {
    pub(super) fn new(
        clock_rate: u32,
        format_specific_params: Option<&str>,
    ) -> Result<Self, String> {
        if clock_rate != 90_000 {
            return Err(format!(
                "invalid H.265 clock rate {clock_rate}; must always be 90000"
            ));
        }

        let parameters = match format_specific_params {
            None => None,
            Some(fp) => match InternalParameters::parse_format_specific_params(fp) {
                Ok(p) => Some(p),
                Err(e) => {
                    log::warn!("Ignoring bad H.265 format-specific-params {:?}: {}", fp, e);
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
                        if access_unit.timestamp.timestamp == pkt.timestamp().timestamp {
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
                    } else if access_unit.timestamp.timestamp != pkt.timestamp().timestamp {
                        if access_unit.in_fu {
                            return Err(format!(
                                "Timestamp changed from {} to {} in the middle of a fragmented NAL",
                                access_unit.timestamp,
                                pkt.timestamp()
                            ));
                        }
                        let last_nal_hdr = self
                            .nals
                            .last()
                            .ok_or("nals should not be empty".to_string())?
                            .hdr;
                        if can_end_au(last_nal_hdr.unit_type()) {
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
                    debug_assert!(self.nals.is_empty());
                    debug_assert!(self.pieces.is_empty());
                    AccessUnit::start(&pkt, loss, state_ts.timestamp == pkt.timestamp().timestamp)
                }
                DepacketizerInputState::Loss {
                    timestamp,
                    mut pkts,
                } => {
                    debug_assert!(self.nals.is_empty());
                    debug_assert!(self.pieces.is_empty());
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

        let hdr = take_hdr(&mut data)?;

        match u8::from(hdr.unit_type()) {
            1..=47 => {
                // Single NAL Unit. https://datatracker.ietf.org/doc/html/rfc7798#section-4.4.1
                if access_unit.in_fu {
                    return Err(format!(
                        "Non-fragmented NAL {hdr:?} while fragment in progress"
                    ));
                }
                let len = u32::try_from(data.len() + 2).expect("data.len() should be <= u16::MAX");
                let next_piece_idx = self.add_piece(data)?;
                self.nals.push(Nal {
                    hdr,
                    next_piece_idx,
                    len,
                });
            }
            48 => {
                // Aggregation Packet. https://datatracker.ietf.org/doc/html/rfc7798#section-4.4.2
                loop {
                    if data.remaining() < 2 {
                        return Err(format!(
                            "AP has {} remaining bytes; expecting 2-byte length",
                            data.remaining()
                        ));
                    }
                    let len = data.get_u16();
                    match data.remaining().cmp(&usize::from(len)) {
                        std::cmp::Ordering::Less => {
                            return Err(format!(
                                "AP too short: {} bytes remaining, expecting {}-byte NAL",
                                data.remaining(),
                                len
                            ));
                        }
                        std::cmp::Ordering::Equal => {
                            let hdr = take_hdr(&mut data)?;
                            let next_piece_idx = self.add_piece(data)?;
                            self.nals.push(Nal {
                                hdr,
                                next_piece_idx,
                                len: u32::from(len),
                            });
                            break;
                        }
                        std::cmp::Ordering::Greater => {
                            let mut piece = data.split_to(usize::from(len));
                            let hdr = take_hdr(&mut piece)?;
                            let next_piece_idx = self.add_piece(piece)?;
                            self.nals.push(Nal {
                                hdr,
                                next_piece_idx,
                                len: u32::from(len),
                            });
                        }
                    }
                }
            }
            49 => {
                // Fragmentation Unit. https://datatracker.ietf.org/doc/html/rfc7798#section-4.4.3
                if data.len() < 2 {
                    return Err(format!("FU len {} too short", data.len()));
                }
                let fu_header = data.get_u8();
                let start = (fu_header & 0b10000000) != 0;
                let end = (fu_header & 0b01000000) != 0;
                let fu_type = nal::UnitType::try_from(fu_header & 0b00111111)
                    .expect("all 6-bit ints should be valid UnitTypes");
                let hdr = hdr.with_unit_type(fu_type);

                // Note: as only `tx-mode` `SRST` is supported, there is no DONL
                // field to decode.

                if start && end {
                    return Err(format!("Invalid FU header {fu_header:02x}"));
                }
                if !end && mark {
                    return Err("FU pkt with MARK && !END".into());
                }
                let u32_len = u32::try_from(data.len())
                    .map_err(|_| "RTP packet len must be < u16::MAX".to_string())?;
                match (start, access_unit.in_fu) {
                    (true, true) => return Err("FU with start bit while frag in progress".into()),
                    (true, false) => {
                        self.add_piece(data)?;
                        self.nals.push(Nal {
                            hdr,
                            next_piece_idx: u32::MAX, // should be overwritten later.
                            len: 2 + u32_len,
                        });
                        access_unit.in_fu = true;
                    }
                    (false, true) => {
                        let pieces = self.add_piece(data)?;
                        let nal = self
                            .nals
                            .last_mut()
                            .ok_or("nals non-empty while in fu".to_string())?;
                        if hdr != nal.hdr {
                            return Err(format!(
                                "FU has inconsistent NAL type: {:?} then {:?}",
                                nal.hdr, hdr,
                            ));
                        }
                        nal.len += u32_len;
                        if end {
                            nal.next_piece_idx = pieces;
                            access_unit.in_fu = false;
                        } else if mark {
                            return Err("FU has MARK and no END".into());
                        }
                    }
                    (false, false) => {
                        if loss > 0 {
                            self.pieces.clear();
                            self.nals.clear();
                            self.input_state = DepacketizerInputState::Loss {
                                timestamp,
                                pkts: loss,
                            };
                            return Ok(());
                        }
                        return Err("FU has start bit unset while no frag in progress".into());
                    }
                }
            }
            _ => return Err(format!("unexpected/bad nal header {hdr:?}")),
        }

        self.input_state = if mark {
            let last_nal_hdr = self
                .nals
                .last()
                .ok_or("nals should not be empty after mark".to_string())?
                .hdr;
            if can_end_au(last_nal_hdr.unit_type()) {
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

    /// Adds a piece to `self.pieces`, erroring if it becomes absurdly large.
    fn add_piece(&mut self, piece: Bytes) -> Result<u32, String> {
        self.pieces.push(piece);
        u32::try_from(self.pieces.len()).map_err(|_| "more than u32::MAX pieces!".to_string())
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
                reason, au.timestamp, nals
            );
        }
    }

    fn finalize_access_unit(&mut self, au: AccessUnit, reason: &str) -> Result<VideoFrame, String> {
        let mut piece_idx = 0;
        let mut retained_len = 0usize;

        // In H.265 terms, this is an IRAP. The coded picture with
        // `nuh_layer_id == 0` must have only VCLs with `nal_unit_type` in
        // the range `[BLA_W_LP, RSV_IRAP_VCL23]`.
        let mut is_random_access_point = true;
        let is_disposable = false;
        let mut new_vps = None::<Bytes>;
        let mut new_sps = None::<Bytes>;
        let mut new_pps = None::<Bytes>;

        if log_enabled!(log::Level::Debug) {
            self.log_access_unit(&au, reason);
        }
        for nal in &self.nals {
            let next_piece_idx = crate::to_usize(nal.next_piece_idx);
            let nal_pieces = &self.pieces[piece_idx..next_piece_idx];
            match nal.hdr.unit_type() {
                nal::UnitType::VpsNut => {
                    if self
                        .parameters
                        .as_ref()
                        .map(|p| !nal_matches(&p.vps_nal[..], nal.hdr, nal_pieces))
                        .unwrap_or(true)
                    {
                        new_vps = Some(to_bytes(nal.hdr, nal.len, nal_pieces));
                    }
                }
                nal::UnitType::SpsNut => {
                    if self
                        .parameters
                        .as_ref()
                        .map(|p| !nal_matches(&p.sps_nal[..], nal.hdr, nal_pieces))
                        .unwrap_or(true)
                    {
                        new_sps = Some(to_bytes(nal.hdr, nal.len, nal_pieces));
                    }
                }
                nal::UnitType::PpsNut => {
                    if self
                        .parameters
                        .as_ref()
                        .map(|p| !nal_matches(&p.pps_nal[..], nal.hdr, nal_pieces))
                        .unwrap_or(true)
                    {
                        new_pps = Some(to_bytes(nal.hdr, nal.len, nal_pieces));
                    }
                }
                u if matches!(
                    u.unit_type_class(),
                    nal::UnitTypeClass::Vcl { intra_coded: false }
                ) =>
                {
                    is_random_access_point = false;
                }
                _ => {}
            }
            retained_len += 4usize + crate::to_usize(nal.len);
            piece_idx = next_piece_idx;
        }
        let mut data = Vec::with_capacity(retained_len);
        piece_idx = 0;
        for nal in &self.nals {
            let next_piece_idx = crate::to_usize(nal.next_piece_idx);
            let nal_pieces = &self.pieces[piece_idx..next_piece_idx];

            data.extend_from_slice(&nal.len.to_be_bytes());
            data.extend_from_slice(&nal.hdr[..]);

            let mut actual_len = 2;
            for piece in nal_pieces {
                data.extend_from_slice(&piece[..]);
                actual_len += piece.len();
            }
            debug_assert_eq!(crate::to_usize(nal.len), actual_len);
            piece_idx = next_piece_idx;
        }
        debug_assert_eq!(retained_len, data.len());

        self.nals.clear();
        self.pieces.clear();

        // TODO: simpler if we require all or none to be set?
        // although only one could be different.
        let all_new_params = new_vps.is_some() && new_sps.is_some() && new_pps.is_some();
        let some_new_params = new_vps.is_some() || new_sps.is_some() || new_pps.is_some();
        let has_new_parameters = if all_new_params || (some_new_params && self.parameters.is_some())
        {
            let old_ip = self.parameters.as_ref();
            let vps_nal = new_vps
                .as_deref()
                .unwrap_or_else(|| &old_ip.unwrap().vps_nal);
            let sps_nal = new_sps
                .as_deref()
                .unwrap_or_else(|| &old_ip.unwrap().sps_nal);
            let pps_nal = new_pps
                .as_deref()
                .unwrap_or_else(|| &old_ip.unwrap().pps_nal);
            let seen_extra_trailing_data =
                old_ip.map(|o| o.seen_extra_trailing_data).unwrap_or(false);
            self.parameters = Some(InternalParameters::parse_vps_sps_pps(
                vps_nal,
                sps_nal,
                pps_nal,
                seen_extra_trailing_data,
            )?);
            true
        } else {
            false
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
fn can_end_au(nal_unit_type: nal::UnitType) -> bool {
    // H.265 section 7.4.2.4.4 "Order of NAL units and coded pictures and their
    // association to access units" says "When any VPS NAL units, SPS NAL units,
    // PPS NAL units, prefix SEI NAL units, NAL units with nal_unit_type in the
    // range of RSV_NVCL41..RSV_NVCL44, or NAL units with nal_unit_type in the
    // range of UNSPEC48..UNSPEC55 are present, they shall not follow the last
    // VCL NAL unit of the access unit."
    !matches!(
        nal_unit_type,
        nal::UnitType::VpsNut
            | nal::UnitType::SpsNut
            | nal::UnitType::PpsNut
            | nal::UnitType::RsvNvcl41
            | nal::UnitType::RsvNvcl42
            | nal::UnitType::RsvNvcl43
            | nal::UnitType::RsvNvcl44
            | nal::UnitType::Unspec48
            | nal::UnitType::Unspec49
            | nal::UnitType::Unspec50
            | nal::UnitType::Unspec51
            | nal::UnitType::Unspec52
            | nal::UnitType::Unspec53
            | nal::UnitType::Unspec54
            | nal::UnitType::Unspec55
    )
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
            in_fu: false,

            // TODO: overflow?
            loss: pkt.loss() + additional_loss,
            same_ts_as_prev,
        }
    }
}

/// Checks NAL unit type ordering against (some of the) rules of H.265 section
/// 7.4.2.4.4.
fn validate_order(nals: &[Nal], errs: &mut String) {
    let mut seen_layer0_vcl = false;
    for (i, nal) in nals.iter().enumerate() {
        let l = nal.hdr.nuh_layer_id();
        let u = nal.hdr.unit_type();
        if l == 0 && matches!(u.unit_type_class(), nal::UnitTypeClass::Vcl { .. }) {
            seen_layer0_vcl = true;
        } else if l == 0 && u == nal::UnitType::AudNut {
            if i != 0 {
                let _ = write!(
                    errs,
                    "\n* layer-0 access unit delimiter must be first in AU; was preceded by {:?}",
                    nals[i - 1].hdr
                );
            }
        } else if u == nal::UnitType::EosNut {
            if !seen_layer0_vcl {
                let _ = write!(errs, "\n* end of sequence without layer-0 VCL");
            }
        } else if u == nal::UnitType::EobNut {
            #[allow(clippy::collapsible_if)]
            if i != nals.len() - 1 {
                errs.push_str("\n* end of bitstream NAL isn't last");
            }
        }
    }
    if !seen_layer0_vcl {
        errs.push_str("\n* no layer-0 VCL");
    }
}

#[derive(Clone, Debug)]
struct InternalParameters {
    generic_parameters: super::VideoParameters,

    /// The (single) VPS NAL.
    vps_nal: Bytes,

    /// The (single) SPS NAL.
    sps_nal: Bytes,

    /// The (single) PPS NAL.
    pps_nal: Bytes,

    seen_extra_trailing_data: bool,
}

impl InternalParameters {
    /// Parses metadata from the `format-specific-params` of a SDP `fmtp` media attribute.
    fn parse_format_specific_params(format_specific_params: &str) -> Result<Self, String> {
        let mut sps_nal = None;
        let mut pps_nal = None;
        let mut vps_nal = None;
        for p in format_specific_params.split(';') {
            match p.trim().split_once('=') {
                Some(("tx-mode", "SRST")) => {}
                Some(("tx-mode", v)) => {
                    return Err(format!("unsupported/unexpected tx-mode {v}; expected SRST"));
                }
                Some(("sprop-vps", v)) => Self::store_sprop_nal("sprop-vps", v, &mut vps_nal)?,
                Some(("sprop-sps", v)) => Self::store_sprop_nal("sprop-sps", v, &mut sps_nal)?,
                Some(("sprop-pps", v)) => Self::store_sprop_nal("sprop-pps", v, &mut pps_nal)?,
                Some((_, _)) => {}
                None => return Err(format!("key {p} without value")),
            }
        }
        let vps_nal = vps_nal.ok_or_else(|| "no vps".to_string())?;
        let sps_nal = sps_nal.ok_or_else(|| "no sps".to_string())?;
        let pps_nal = pps_nal.ok_or_else(|| "no pps".to_string())?;
        Self::parse_vps_sps_pps(&vps_nal, &sps_nal, &pps_nal, false)
    }

    fn store_sprop_nal(key: &str, value: &str, out: &mut Option<Vec<u8>>) -> Result<(), String> {
        let nal = base64::engine::general_purpose::STANDARD
            .decode(value)
            .map_err(|e| format!("bad parameter {key}: NAL has invalid base64 encoding: {e}"))?;
        if nal.is_empty() {
            return Err(format!("bad parameter {key}: empty NAL"));
        }
        if out.is_some() {
            return Err(format!("multiple {key} parameters"));
        }
        *out = Some(nal);
        Ok(())
    }

    fn parse_vps_sps_pps(
        vps_nal: &[u8],
        sps_nal: &[u8],
        pps_nal: &[u8],
        mut seen_extra_trailing_data: bool,
    ) -> Result<InternalParameters, String> {
        let (vps_h, _vps_bits) =
            nal::split(vps_nal).map_err(|e| format!("failed to parse VPS: {e}"))?;
        if vps_h.unit_type() != nal::UnitType::VpsNut {
            return Err("VPS NAL is not VPS".into());
        }

        let sps_hex = crate::hex::LimitedHex::new(sps_nal, 256);
        let (sps_h, sps_bits) =
            nal::split(sps_nal).map_err(|e| format!("{e}\nwhile parsing SPS: {sps_hex}"))?;
        if sps_h.unit_type() != nal::UnitType::SpsNut {
            return Err("SPS NAL is not SPS".into());
        }
        let mut sps_has_extra_trailing_data = false;
        let sps_bits = TolerantBitReader {
            inner: sps_bits,
            has_extra_trailing_data: &mut sps_has_extra_trailing_data,
        };
        let sps = nal::Sps::from_bits(sps_bits)
            .map_err(|e| format!("{e}\nwhile parsing SPS: {sps_hex}"))?;
        if sps_has_extra_trailing_data && !seen_extra_trailing_data {
            log::warn!(
                "Ignoring trailing data in SPS {sps_hex}; will not log about trailing data again for this stream."
            );
            seen_extra_trailing_data = true;
        }

        let pps_hex = crate::hex::LimitedHex::new(pps_nal, 256);
        let (pps_h, pps_bits) =
            nal::split(pps_nal).map_err(|e| format!("{e}\nwhile parsing PPS: {pps_hex}"))?;
        if pps_h.unit_type() != nal::UnitType::PpsNut {
            return Err("PPS NAL is not PPS".into());
        }
        let mut pps_has_extra_trailing_data = false;
        let pps_bits = TolerantBitReader {
            inner: pps_bits,
            has_extra_trailing_data: &mut pps_has_extra_trailing_data,
        };
        let pps = nal::Pps::from_bits(pps_bits)
            .map_err(|e| format!("{e}\nwhile parsing PPS: {pps_hex}"))?;
        if pps_has_extra_trailing_data && !seen_extra_trailing_data {
            log::warn!(
                "Ignoring trailing data in PPS {pps_hex}; will not log about trailing data again for this stream."
            );
            seen_extra_trailing_data = true;
        }

        let rfc6381_codec = sps.rfc6381_codec();

        let pixel_dimensions = sps.pixel_dimensions()?;
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
        let (pixel_aspect_ratio, frame_rate);
        if let Some(v) = sps.vui() {
            pixel_aspect_ratio = v
                .aspect_ratio()
                .and_then(nal::AspectRatioInfo::get)
                .map(|(v, h)| (u32::from(v), u32::from(h)));
            frame_rate = v
                .timing_info()
                .map(|t| (t.num_units_in_tick(), t.time_scale()))
        } else {
            pixel_aspect_ratio = None;
            frame_rate = None;
        }

        let hevc_decoder_config =
            record::decoder_configuration_record(pps_nal, &pps, sps_nal, &sps, vps_nal);
        Ok(InternalParameters {
            generic_parameters: super::VideoParameters {
                rfc6381_codec,
                pixel_dimensions,
                pixel_aspect_ratio,
                frame_rate,
                extra_data: hevc_decoder_config.record,
                codec: super::VideoParametersCodec::H265 {
                    sps: hevc_decoder_config.sps.clone(),
                    pps: hevc_decoder_config.pps.clone(),
                    vps: hevc_decoder_config.vps.clone(),
                },
            },
            vps_nal: hevc_decoder_config.vps,
            sps_nal: hevc_decoder_config.sps,
            pps_nal: hevc_decoder_config.pps,
            seen_extra_trailing_data,
        })
    }
}

/// Returns true iff the bytes of `nal` equal the bytes of `[hdr, ..data]`.
fn nal_matches(nal: &[u8], hdr: nal::Header, pieces: &[Bytes]) -> bool {
    if nal.first_chunk() != Some(&*hdr) {
        return false;
    }
    let mut nal_pos = 2;
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
fn to_bytes(hdr: nal::Header, len: u32, pieces: &[Bytes]) -> Bytes {
    let len = crate::to_usize(len);
    let mut out = Vec::with_capacity(len);
    out.extend(&*hdr);
    for piece in pieces {
        out.extend_from_slice(&piece[..]);
    }
    debug_assert_eq!(len, out.len());
    out.into()
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroU32;

    use crate::{
        PacketContext, codec::CodecItem, rtp::ReceivedPacketBuilder, testutil::init_logging,
    };

    #[test]
    fn depacketize() {
        init_logging();
        let mut d = super::Depacketizer::new(90_000, Some("profile-id=1;sprop-sps=QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=;sprop-pps=RAHA8saNA7NA;sprop-vps=QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==")).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(
            ReceivedPacketBuilder {
                // plain PREFIX_SEI packet.
                ctx: PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x4e\x01plain")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // aggregation packet.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            // .build(*b"\x18\x00\x09\x06stap-a 1\x00\x09\x06stap-a 2")
            .build(*b"\x60\x01\x00\x0a\x4e\x01stap-a 1\x00\x0a\x4e\x01stap-a 2")
            .unwrap(),
        )
        .unwrap();
        assert!(d.pull().is_none());
        d.push(
            ReceivedPacketBuilder {
                // FU packet, start.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x62\x01\x94fu start, ")
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
            .build(*b"\x62\x01\x14fu middle, ")
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
            .build(*b"\x62\x01\x54fu end")
            .unwrap(),
        )
        .unwrap();
        let frame = match d.pull() {
            Some(CodecItem::VideoFrame(frame)) => frame,
            _ => panic!(),
        };
        assert_eq!(
            frame.data(),
            b"\x00\x00\x00\x07\x4e\x01plain\
              \x00\x00\x00\x0a\x4e\x01stap-a 1\
              \x00\x00\x00\x0a\x4e\x01stap-a 2\
              \x00\x00\x00\x1d\x28\x01fu start, fu middle, fu end"
        );
    }

    #[test]
    fn parse_tenda_cp3pro_format_specific_params() {
        init_logging();
        let p = super::InternalParameters::parse_format_specific_params(
            "profile-space=0;\
             profile-id=1;\
             tier-flag=0;\
             level-id=63;\
             interop-constraints=900000000000;\
             sprop-vps=QAEMAf//AWAAAAMAkAAAAwAAAwA/LAwAAgAAAwAoAAIAAgACgA==;\
             sprop-sps=QgEBAWAAAAMAkAAAAwAAAwA/oAUCAXFlLkkyS7I=;\
             sprop-pps=RAHA8vAzJA==",
        )
        .unwrap();
        assert_eq!(p.generic_parameters.pixel_dimensions(), (640, 368));
    }

    /// Parses `format-specific-params` from <https://github.com/scottlamb/moonfire-nvr/issues/333>.
    #[test]
    fn parse_hacked_xiaomi_yi_pro_2k_home_format_specific_params() {
        init_logging();
        let p = super::InternalParameters::parse_format_specific_params(
            "profile-space=0;\
             profile-id=1;\
             tier-flag=0;\
             level-id=186;\
             interop-constraints=000000000000;\
             sprop-vps=QAEMAf//AWAAAAMAAAMAAAMAAAMAuqwJ;\
             sprop-sps=QgEBAWAAAAMAAAMAAAMAAAMAuqABICAFEf5a7kSIi/Lc1AQEBAI=;\
             sprop-pps=RAHA8oSJAzJA",
        )
        .unwrap();
        assert_eq!(p.generic_parameters.pixel_dimensions(), (2304, 1296));
    }
}
