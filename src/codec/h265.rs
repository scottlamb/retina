// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [H.265](https://www.itu.int/rec/T-REC-H.265)-encoded video,
//! with RTP encoding as in [RFC 7798](https://tools.ietf.org/html/rfc7798).

#[doc(hidden)] // `pub` only for fuzz tests.
pub mod nal;

mod record;

use std::convert::TryFrom;
use std::fmt::Write;

use base64::Engine as _;
use bytes::Bytes;
use log::{debug, log_enabled, trace};

use crate::buf::{BufRange, Mark, MarkBuf, PacketRef};
use crate::codec::h26x::TolerantBitReader;
use crate::codec::{
    Accumulate, FrameBody, Loss, LossReason, VideoFrameEnd, VideoFrameStart, VideoHandler,
    VideoParameters,
};
use crate::inputs::Input as _;

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
pub(crate) struct Depacketizer<Ctx> {
    input_state: DepacketizerInputState<Ctx>,

    /// Completed items ready to be pulled via the test-only `push_collect`/`pull` interface.
    #[cfg(test)]
    pending: super::testutil::Pending,

    parameters: Option<InternalParameters>,

    /// Mark pinning ring buffer data for the current access unit's ranges.
    /// Set when the first piece is added; cleared on finalize/discard.
    mark: Option<Mark>,

    /// In state `PreMark`, pieces of NALs, excluding their header bytes.
    /// Kept around (empty) in other states to re-use the backing allocation.
    pieces: Vec<BufRange>,

    /// In state `PreMark`, an entry for each complete NAL.
    /// Kept around (empty) in other states to re-use the backing allocation.
    nals: Vec<Nal>,

    /// True if we've seen a FU sequence where the NAL headers differ between
    /// fragments.
    seen_inconsistent_fu_nal_hdr: bool,

    /// True if we've seen a FU with both S and E bits set (a single-fragment
    /// FU, forbidden by RFC 7798 section 4.4.3).
    seen_single_fragment_fu: bool,

    /// The format used by the test-only `push_collect`/`pull` interface.
    #[cfg(test)]
    test_format: super::FrameFormat,
}

type Nal = super::h26x::Nal<nal::Header>;

impl super::h26x::NalHeader for nal::Header {
    type Bytes = [u8; 2];

    #[inline]
    fn bytes(self) -> [u8; 2] {
        *self
    }

    #[inline]
    fn is_parameter_set(self) -> bool {
        matches!(
            self.unit_type(),
            nal::UnitType::VpsNut | nal::UnitType::SpsNut | nal::UnitType::PpsNut
        )
    }
}

/// An access unit that is currently being accumulated during `PreMark` state.
#[derive(Debug)]
struct AccessUnit<Ctx> {
    start_ctx: Ctx,
    end_ctx: Ctx,
    timestamp: crate::Timestamp,

    /// The NAL currently being assembled from fragmentation units, if any.
    fu: Option<InProgressNal>,

    /// RTP packets lost as this access unit was starting.
    loss: u16,

    same_ts_as_prev: bool,

    /// Metadata from the NALs scanned so far.
    meta: FrameMeta,

    /// The number of `Depacketizer::nals` reflected in `meta`.
    scanned_nals: u32,

    /// Set once `frame_start` has been called.
    started: Option<Accumulate>,

    delivery: super::h26x::Delivery,

    /// True if `Depacketizer::nals` and `Depacketizer::pieces` have been
    /// trimmed mid-access unit, so they no longer describe all of it.
    /// Only happens under `Accumulate::No`.
    trimmed: bool,
}

#[derive(Debug)]
struct InProgressNal {
    hdr: nal::Header,

    /// The length so far, including the header bytes.
    len: u32,
}

/// Metadata about an access unit, gathered as its NALs are scanned.
#[derive(Debug)]
struct FrameMeta {
    /// True unless a non-intra-coded VCL NAL has been seen.
    is_random_access_point: bool,

    /// True if a VCL NAL has been seen.
    seen_vcl: bool,

    /// Parameter sets which differ from `Depacketizer::parameters`, if any.
    /// Boxed because they're rare, and `AccessUnit` moves on every packet.
    new_params: Option<Box<NewParams>>,

    /// Whether the first VCL NAL begins a picture, once known. If packets
    /// were lost just before this access unit and this isn't `Some(true)`,
    /// the access unit may be missing its beginning.
    first_vcl_starts_picture: Option<bool>,

    /// The header of the last complete NAL, for `can_end_au`.
    last_nal_hdr: Option<nal::Header>,
}

#[derive(Debug, Default)]
struct NewParams {
    vps: Option<Bytes>,
    sps: Option<Bytes>,
    pps: Option<Bytes>,

    /// Parameters parsed from the above when the frame started, to be
    /// committed when it ends. Reset if another parameter set arrives.
    parsed: Option<InternalParameters>,
}

#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
enum DepacketizerInputState<Ctx> {
    /// Not yet processing an access unit.
    New,

    /// Ignoring the remainder of an access unit because of interior packet loss.
    Loss {
        timestamp: crate::Timestamp,
        pkts: u16,
    },

    /// Currently processing an access unit.
    /// This will be flushed after a marked packet or when receiving a later timestamp.
    PreMark(AccessUnit<Ctx>),

    /// Finished processing the given packet. It's an error to receive the same timestamp again.
    PostMark {
        timestamp: crate::Timestamp,
        loss: u16,
    },
}

impl<Ctx: Clone> Depacketizer<Ctx> {
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
            #[cfg(test)]
            pending: Default::default(),
            mark: None,
            pieces: Vec::new(),
            nals: Vec::new(),
            parameters,
            seen_inconsistent_fu_nal_hdr: false,
            seen_single_fragment_fu: false,
            #[cfg(test)]
            test_format: Default::default(),
        })
    }

    /// Sets the format used by the test-only `push_collect`/`pull` interface.
    #[cfg(test)]
    fn set_frame_format(&mut self, format: super::FrameFormat) {
        self.test_format = format;
    }

    pub(super) fn check_invariants(&self) {
        if !matches!(self.input_state, DepacketizerInputState::PreMark(_)) {
            assert!(self.nals.is_empty());
            assert!(self.pieces.is_empty());
            assert!(self.mark.is_none());
        }
    }

    fn discard_au(&mut self) {
        self.nals.clear();
        self.pieces.clear();
        self.mark = None;
    }

    pub(super) fn parameters(&self) -> Option<&VideoParameters> {
        self.parameters.as_ref().map(|p| &p.generic_parameters)
    }

    /// Updates `au.meta` to reflect NALs completed since the last call.
    fn scan_meta(&self, au: &mut AccessUnit<Ctx>, buf: &MarkBuf) {
        let scanned_nals = crate::to_usize(au.scanned_nals);
        let mut piece_idx = match scanned_nals {
            0 => 0,
            i => crate::to_usize(self.nals[i - 1].next_piece_idx),
        };
        for nal in &self.nals[scanned_nals..] {
            let next_piece_idx = crate::to_usize(nal.next_piece_idx);
            let nal_pieces = &self.pieces[piece_idx..next_piece_idx];
            let p = self.parameters.as_ref();
            match nal.hdr.unit_type() {
                nal::UnitType::VpsNut
                    if p.map(|p| !nal_matches(p.in_band_vps(), nal.hdr, nal_pieces, buf))
                        .unwrap_or(true) =>
                {
                    let np = au.meta.new_params.get_or_insert_default();
                    np.vps = Some(to_bytes(nal.hdr, nal.len, nal_pieces, buf));
                    np.parsed = None;
                }
                nal::UnitType::SpsNut
                    if p.map(|p| !nal_matches(p.in_band_sps(), nal.hdr, nal_pieces, buf))
                        .unwrap_or(true) =>
                {
                    let np = au.meta.new_params.get_or_insert_default();
                    np.sps = Some(to_bytes(nal.hdr, nal.len, nal_pieces, buf));
                    np.parsed = None;
                }
                nal::UnitType::PpsNut
                    if p.map(|p| !nal_matches(p.in_band_pps(), nal.hdr, nal_pieces, buf))
                        .unwrap_or(true) =>
                {
                    let np = au.meta.new_params.get_or_insert_default();
                    np.pps = Some(to_bytes(nal.hdr, nal.len, nal_pieces, buf));
                    np.parsed = None;
                }
                _ => {}
            }
            match nal.hdr.unit_type().unit_type_class() {
                nal::UnitTypeClass::Vcl { intra_coded } => {
                    au.meta.seen_vcl = true;
                    au.meta
                        .first_vcl_starts_picture
                        .get_or_insert_with(|| super::h26x::starts_picture(nal_pieces, buf));
                    if !intra_coded {
                        au.meta.is_random_access_point = false;
                    }
                }
                nal::UnitTypeClass::NonVcl => {}
            }
            au.meta.last_nal_hdr = Some(nal.hdr);
            piece_idx = next_piece_idx;
        }
        au.scanned_nals = u32::try_from(self.nals.len()).expect("NAL count fits in u32");
    }

    /// Parses new parameters, returning `None` if they're incomplete.
    fn parse_new_params(&self, np: &NewParams) -> Result<Option<InternalParameters>, String> {
        let old_ip = self.parameters.as_ref();
        let (Some(vps_nal), Some(sps_nal), Some(pps_nal)) = (
            np.vps.as_deref().or(old_ip.map(|p| &p.vps_nal[..])),
            np.sps.as_deref().or(old_ip.map(|p| &p.sps_nal[..])),
            np.pps.as_deref().or(old_ip.map(|p| &p.pps_nal[..])),
        ) else {
            return Ok(None);
        };
        let seen_extra_trailing_data = old_ip.map(|o| o.seen_extra_trailing_data).unwrap_or(false);
        InternalParameters::parse_vps_sps_pps(vps_nal, sps_nal, pps_nal, seen_extra_trailing_data)
            .map(Some)
    }

    /// Calls `frame_start` for a frame which is still in progress.
    ///
    /// The frame's metadata so far is provisional. In particular, parameters
    /// are parsed but not committed to `self.parameters` until the frame ends.
    fn start_frame(
        &self,
        au: &mut AccessUnit<Ctx>,
        buf: &MarkBuf,
        handler: &mut impl VideoHandler<Ctx>,
    ) {
        if au.meta.first_vcl_starts_picture.is_none() {
            // The first VCL NAL is still in progress; its pieces follow the
            // last complete NAL's.
            let first_piece = self
                .nals
                .last()
                .map_or(0, |n| crate::to_usize(n.next_piece_idx));
            au.meta.first_vcl_starts_picture = Some(super::h26x::starts_picture(
                &self.pieces[first_piece..],
                buf,
            ));
        }
        let mut is_random_access_point = au.meta.is_random_access_point;
        if let Some(fu) = au.fu.as_ref()
            && matches!(
                fu.hdr.unit_type().unit_type_class(),
                nal::UnitTypeClass::Vcl { intra_coded: false }
            )
        {
            is_random_access_point = false;
        }
        if let Some(np) = au.meta.new_params.as_mut()
            && np.parsed.is_none()
        {
            // On error, leave `parsed` empty; `finalize_access_unit` will try
            // again and report the error.
            np.parsed = self.parse_new_params(np).ok().flatten();
        }
        let new_params = au
            .meta
            .new_params
            .as_ref()
            .and_then(|np| np.parsed.as_ref());
        au.started = Some(
            handler.frame_start(&VideoFrameStart {
                is_decodable: true,
                missing_prefix: au.loss > 0 && au.meta.first_vcl_starts_picture != Some(true),
                timestamp: au.timestamp,
                ctx: &au.start_ctx,
                is_random_access_point,
                is_disposable: false,
                has_new_parameters: new_params.is_some(),
                parameters: new_params
                    .or(self.parameters.as_ref())
                    .map(|p| &p.generic_parameters),
            }),
        );
    }

    /// After a packet, starts the frame if possible and delivers its data so far.
    fn stream(
        &mut self,
        au: &mut AccessUnit<Ctx>,
        buf: &MarkBuf,
        handler: &mut impl VideoHandler<Ctx>,
    ) {
        self.scan_meta(au, buf);
        let in_progress = au.fu.as_ref().map(|fu| fu.hdr);
        if au.started.is_none()
            && (au.meta.seen_vcl
                || in_progress.is_some_and(|h| {
                    matches!(
                        h.unit_type().unit_type_class(),
                        nal::UnitTypeClass::Vcl { .. }
                    )
                }))
        {
            self.start_frame(au, buf, handler);
        }
        let Some(accumulate) = au.started else {
            return;
        };
        au.delivery
            .deliver(&self.nals, &self.pieces, in_progress, buf, handler);
        if accumulate == Accumulate::No && au.delivery.caught_up(self.pieces.len()) {
            // Everything has been delivered, and parameter sets have been
            // copied into `au.meta`. Release the buffer space.
            self.nals.clear();
            self.pieces.clear();
            au.scanned_nals = 0;
            au.delivery.cleared();
            au.trimmed = true;
            self.mark = None;
        }
    }

    /// Supplies a new packet, delivering any resulting events to `handler`.
    pub(super) fn push(&mut self, pkt: &PacketRef<'_, Ctx>, handler: &mut impl VideoHandler<Ctx>) {
        let r = self.push_inner(pkt, handler);

        // Several error paths within `push_inner` just use the `?` operator to bail out with
        // `input_state` at `New` when they encounter a problem mid-access unit. Restore
        // the invariant so the caller can try to recover after error.
        if !matches!(self.input_state, DepacketizerInputState::PreMark(_)) {
            self.discard_au();
        }
        if let Err(description) = r {
            super::report_corrupt(pkt, description, |l| handler.loss(l));
        }
    }

    fn push_inner(
        &mut self,
        pkt: &PacketRef<'_, Ctx>,
        handler: &mut impl VideoHandler<Ctx>,
    ) -> Result<(), String> {
        let meta = &pkt.meta;
        let payload_pos = pkt.payload_pos();
        let payload_len = pkt.payload_len();
        let buf = pkt.buf();

        let mut access_unit =
            match std::mem::replace(&mut self.input_state, DepacketizerInputState::New) {
                DepacketizerInputState::New => {
                    debug_assert!(self.nals.is_empty());
                    debug_assert!(self.pieces.is_empty());
                    AccessUnit::start(meta, 0, false)
                }
                DepacketizerInputState::PreMark(mut access_unit) => {
                    let loss = meta.loss;
                    if loss > 0 {
                        self.discard_au();
                        if access_unit.timestamp.timestamp == meta.timestamp.timestamp {
                            // Loss within this access unit. Ignore until mark or new timestamp.
                            self.input_state = if meta.mark {
                                DepacketizerInputState::PostMark {
                                    timestamp: meta.timestamp,
                                    loss,
                                }
                            } else {
                                DepacketizerInputState::Loss {
                                    timestamp: meta.timestamp,
                                    pkts: loss,
                                }
                            };
                            return Ok(());
                        }
                        // A suffix of a previous access unit was lost; discard it.
                        // A prefix of the new one may have been lost; try parsing.
                        AccessUnit::start(meta, 0, false)
                    } else if access_unit.timestamp.timestamp != meta.timestamp.timestamp {
                        if access_unit.fu.is_some() {
                            // Something went wrong: perhaps the end of the last fragmentation unit was dropped
                            // without loss being indicated. Report corruption, but also process the current packet.
                            handler.loss(&Loss {
                            ctx: &meta.ctx,
                            reason: LossReason::Corrupt(super::Corruption::new(format!(
                                "timestamp changed from {} to {} in the middle of a fragmented NAL",
                                access_unit.timestamp, meta.timestamp
                            ))),
                        });
                            self.discard_au();
                            AccessUnit::start(meta, 0, false)
                        } else {
                            let last_nal_hdr = access_unit
                                .meta
                                .last_nal_hdr
                                .ok_or("nals should not be empty".to_string())?;
                            if can_end_au(last_nal_hdr.unit_type()) {
                                access_unit.end_ctx = meta.ctx.clone();
                                self.finalize_access_unit(access_unit, "ts change", buf, handler)?;
                                AccessUnit::start(meta, 0, false)
                            } else {
                                log::debug!(
                                    "Bogus mid-access unit timestamp change after {:?}",
                                    last_nal_hdr
                                );
                                access_unit.timestamp.timestamp = meta.timestamp.timestamp;
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
                    AccessUnit::start(meta, loss, state_ts.timestamp == meta.timestamp.timestamp)
                }
                DepacketizerInputState::Loss {
                    timestamp,
                    mut pkts,
                } => {
                    debug_assert!(self.nals.is_empty());
                    debug_assert!(self.pieces.is_empty());
                    if meta.timestamp.timestamp == timestamp.timestamp {
                        pkts += meta.loss;
                        self.input_state = DepacketizerInputState::Loss { timestamp, pkts };
                        return Ok(());
                    }
                    AccessUnit::start(meta, pkts, false)
                }
            };

        let mark = meta.mark;
        let loss = meta.loss;
        let timestamp = meta.timestamp;

        if payload_len < 2 {
            return Err("Short NAL".into());
        }
        // Pin the payload data in the ring buffer.
        match &self.mark {
            None => self.mark = Some(pkt.mark()),
            Some(m) => assert!(
                m.belongs_to(buf),
                "depacketizer holding data from one MarkBuf was pushed a packet from another"
            ),
        }

        let payload = pkt.payload();

        let hdr_bytes = payload.peek_array::<2>();
        let hdr = nal::Header::try_from(hdr_bytes).map_err(|e| e.0)?;

        match u8::from(hdr.unit_type()) {
            0..=47 => {
                // Single NAL Unit. https://datatracker.ietf.org/doc/html/rfc7798#section-4.4.1
                if access_unit.fu.is_some() {
                    return Err(format!(
                        "Non-fragmented NAL {hdr:?} while fragment in progress"
                    ));
                }
                let next_piece_idx = self.add_piece(BufRange {
                    pos: payload_pos + 2,
                    len: payload_len - 2,
                })?;
                self.nals.push(Nal {
                    hdr,
                    next_piece_idx,
                    len: u32::from(payload_len),
                });
            }
            48 => {
                // Aggregation Packet. https://datatracker.ietf.org/doc/html/rfc7798#section-4.4.2
                if access_unit.fu.is_some() {
                    return Err("AP while fragment in progress".into());
                }
                // Skip the 2-byte AP header.
                let mut payload = payload;
                payload.advance(2);
                let mut pos = payload_pos + 2;
                loop {
                    if payload.len() < 2 {
                        return Err(format!(
                            "AP has {} remaining bytes; expecting 2-byte length",
                            payload.len(),
                        ));
                    }
                    let nal_len = u16::from_be_bytes(payload.peek_array::<2>());
                    payload.advance(2);
                    pos += 2;
                    if usize::from(nal_len) > payload.len() {
                        return Err(format!(
                            "AP too short: {} bytes remaining, expecting {nal_len}-byte NAL",
                            payload.len(),
                        ));
                    }
                    if nal_len < 2 {
                        return Err("Short NAL".into());
                    }
                    let nal_hdr_bytes = payload.peek_array::<2>();
                    let nal_hdr = nal::Header::try_from(nal_hdr_bytes).map_err(|e| e.0)?;
                    let next_piece_idx = self.add_piece(BufRange {
                        pos: pos + 2,
                        len: nal_len - 2,
                    })?;
                    self.nals.push(Nal {
                        hdr: nal_hdr,
                        next_piece_idx,
                        len: u32::from(nal_len),
                    });
                    payload.advance(usize::from(nal_len));
                    pos += u64::from(nal_len);
                    if payload.is_empty() {
                        break;
                    }
                }
            }
            49 => {
                // Fragmentation Unit. https://datatracker.ietf.org/doc/html/rfc7798#section-4.4.3
                // Empty fragments are silly but allowed.
                if payload_len < 3 {
                    return Err(format!("FU len {payload_len} too short"));
                }
                let fu_header = payload.byte_at(2);
                let start = (fu_header & 0b10000000) != 0;
                let end = (fu_header & 0b01000000) != 0;
                let fu_type = nal::UnitType::try_from(fu_header & 0b00111111)
                    .expect("all 6-bit ints should be valid UnitTypes");
                let hdr = hdr.with_unit_type(fu_type);

                // Note: as only `tx-mode` `SRST` is supported, there is no DONL
                // field to decode.

                if !end && mark {
                    return Err("FU pkt with MARK && !END".into());
                }
                let frag_len = payload_len - 3;
                let u32_frag_len = u32::from(frag_len);
                match (start, access_unit.fu.take()) {
                    (true, Some(_)) => {
                        return Err("FU with start bit while frag in progress".into());
                    }
                    (true, None) => {
                        if end && !self.seen_single_fragment_fu {
                            // RFC 7798 section 4.4.3: "the Start bit and End bit MUST NOT both be
                            // set to one in the same FU header". Some cameras violate this by
                            // wrapping small NALs in a single-fragment FU.
                            // Tolerate by treating them as a complete NAL.
                            log::warn!(
                                "FU header {fu_header:02x} has both start and end bits set; \
                                 treating as a complete NAL. \
                                 Will not log about this again for this stream."
                            );
                            self.seen_single_fragment_fu = true;
                        }
                        let next_piece_idx = self.add_piece(BufRange {
                            pos: payload_pos + 3,
                            len: frag_len,
                        })?;
                        if end {
                            self.nals.push(Nal {
                                hdr,
                                next_piece_idx,
                                len: 2 + u32_frag_len,
                            });
                        } else {
                            access_unit.fu = Some(InProgressNal {
                                hdr,
                                len: 2 + u32_frag_len,
                            });
                        }
                    }
                    (false, Some(mut fu)) => {
                        let next_piece_idx = self.add_piece(BufRange {
                            pos: payload_pos + 3,
                            len: frag_len,
                        })?;
                        if hdr != fu.hdr && !self.seen_inconsistent_fu_nal_hdr {
                            log::warn!(
                                "FU has inconsistent NAL header: {:?} then {:?}; will not log about this again for this stream",
                                fu.hdr,
                                hdr,
                            );
                            self.seen_inconsistent_fu_nal_hdr = true;
                        }
                        fu.len += u32_frag_len;
                        if end {
                            self.nals.push(Nal {
                                hdr: fu.hdr,
                                next_piece_idx,
                                len: fu.len,
                            });
                        } else {
                            access_unit.fu = Some(fu);
                        }
                    }
                    (false, None) => {
                        if loss > 0 {
                            self.discard_au();
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

        self.stream(&mut access_unit, buf, handler);
        self.input_state = if mark {
            let last_nal_hdr = access_unit
                .meta
                .last_nal_hdr
                .ok_or("nals should not be empty after mark".to_string())?;
            if can_end_au(last_nal_hdr.unit_type()) {
                access_unit.end_ctx = meta.ctx.clone();
                self.finalize_access_unit(access_unit, "mark", buf, handler)?;
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

    /// Adds a piece to `self.pieces`, erroring if it becomes absurdly large.
    fn add_piece(&mut self, piece: BufRange) -> Result<u32, String> {
        self.pieces.push(piece);
        u32::try_from(self.pieces.len()).map_err(|_| "more than u32::MAX pieces!".to_string())
    }

    /// Logs information about each access unit.
    /// Currently, "bad" access units (violating certain specification rules)
    /// are logged at debug priority, and others are logged at trace priority.
    fn log_access_unit(&self, au: &AccessUnit<Ctx>, reason: &str) {
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

    fn finalize_access_unit(
        &mut self,
        mut au: AccessUnit<Ctx>,
        reason: &str,
        buf: &MarkBuf,
        handler: &mut impl VideoHandler<Ctx>,
    ) -> Result<(), String> {
        if !au.trimmed && log_enabled!(log::Level::Debug) {
            self.log_access_unit(&au, reason);
        }

        // Commit new parameters before building the frame, so prepended
        // params reflect the latest VPS/SPS/PPS.
        let new_params = match au.meta.new_params.take() {
            None => None,
            Some(mut np) => match np.parsed.take() {
                Some(p) => Some(p),
                None => self.parse_new_params(&np)?,
            },
        };
        let has_new_parameters = new_params.is_some();
        if new_params.is_some() {
            self.parameters = new_params;
        }

        let accumulate = match au.started {
            Some(a) => a,
            None => handler.frame_start(&VideoFrameStart {
                is_decodable: true,
                missing_prefix: au.loss > 0 && au.meta.first_vcl_starts_picture != Some(true),
                timestamp: au.timestamp,
                ctx: &au.start_ctx,
                is_random_access_point: au.meta.is_random_access_point,
                is_disposable: false,
                has_new_parameters,
                parameters: self.parameters.as_ref().map(|p| &p.generic_parameters),
            }),
        };
        au.delivery
            .deliver(&self.nals, &self.pieces, None, buf, handler);

        handler.frame_end(&mut VideoFrameEnd {
            is_decodable: true,
            missing_prefix: au.loss > 0 && au.meta.first_vcl_starts_picture != Some(true),
            timestamp: au.timestamp,
            start_ctx: &au.start_ctx,
            end_ctx: &au.end_ctx,
            is_random_access_point: au.meta.is_random_access_point,
            is_disposable: false,
            has_new_parameters,
            body: FrameBody::H265(FrameEndBody {
                au: (accumulate == Accumulate::Yes && !au.trimmed).then_some(AuData {
                    nals: &self.nals,
                    pieces: &self.pieces,
                    buf,
                }),
                parameters: &mut self.parameters,
                is_random_access_point: au.meta.is_random_access_point,
                has_new_parameters,
            }),
        });
        self.nals.clear();
        self.pieces.clear();
        self.mark = None;
        Ok(())
    }
}

#[cfg(test)]
impl Depacketizer<crate::PacketContext> {
    /// Supplies a new packet via the test-only `push_collect`/`pull` interface.
    ///
    /// Between any two calls to `push_collect`, the caller must call `pull`
    /// until it returns `None`.
    fn push_collect(&mut self, pkt: &PacketRef<'_, crate::PacketContext>) {
        let mut pending = std::mem::take(&mut self.pending);
        pending.push(pkt, self.test_format, |c| self.push(pkt, c));
        self.pending = pending;
    }

    fn pull(&mut self) -> Option<Result<super::testutil::Item, String>> {
        self.pending.pull()
    }
}

/// Access to a finished access unit, for [`VideoFrameEnd`].
pub(crate) struct FrameEndBody<'a> {
    /// The access unit's data, if accumulated and not yet taken.
    au: Option<AuData<'a>>,
    parameters: &'a mut Option<InternalParameters>,
    is_random_access_point: bool,
    has_new_parameters: bool,
}

struct AuData<'a> {
    nals: &'a [Nal],
    pieces: &'a [BufRange],
    buf: &'a MarkBuf,
}

impl FrameEndBody<'_> {
    pub(super) fn parameters(&self) -> Option<&VideoParameters> {
        self.parameters.as_ref().map(|p| &p.generic_parameters)
    }

    /// Returns the parameter set NALs to prepend to the frame in the given format.
    fn prepend_params(&self, format: super::FrameFormat) -> Option<[&[u8]; 3]> {
        use super::ParameterSetInsertion;
        let prepend = self.is_random_access_point
            && match format.parameter_set_insertion {
                ParameterSetInsertion::EachKeyFrame => true,
                ParameterSetInsertion::OnChange => self.has_new_parameters,
                ParameterSetInsertion::Never => false,
            };
        if !prepend {
            return None;
        }
        self.parameters
            .as_ref()
            .map(|p| [&p.vps_nal[..], &p.sps_nal[..], &p.pps_nal[..]])
    }

    pub(super) fn data_len(&self, format: super::FrameFormat) -> Option<usize> {
        let au = self.au.as_ref()?;
        let params = self.prepend_params(format);
        Some(super::h26x::frame_len(
            au.nals,
            params.as_ref().map_or(&[][..], |p| &p[..]),
        ))
    }

    pub(super) fn visit(
        &self,
        format: super::FrameFormat,
        visitor: &mut impl FnMut(&[u8]),
    ) -> bool {
        let Some(au) = self.au.as_ref() else {
            return false;
        };
        let params = self.prepend_params(format);
        super::h26x::visit_frame(
            au.nals,
            au.pieces,
            au.buf,
            params.as_ref().map_or(&[][..], |p| &p[..]),
            format.h26x_framing,
            visitor,
        );
        true
    }

    /// Overrides the parameters for this and subsequent frames.
    pub(super) fn set_parameters(
        &mut self,
        vps: &[u8],
        sps: &[u8],
        pps: &[u8],
    ) -> Result<(), String> {
        let old = self.parameters.as_ref();
        let mut new = InternalParameters::parse_vps_sps_pps(
            vps,
            sps,
            pps,
            old.is_some_and(|p| p.seen_extra_trailing_data),
        )?;
        new.overridden = old.map(|p| {
            Box::new((
                Bytes::copy_from_slice(p.in_band_vps()),
                Bytes::copy_from_slice(p.in_band_sps()),
                Bytes::copy_from_slice(p.in_band_pps()),
            ))
        });
        *self.parameters = Some(new);
        self.has_new_parameters = true;
        Ok(())
    }

    pub(super) fn build(&mut self, format: super::FrameFormat) -> Option<Vec<u8>> {
        let len = self.data_len(format)?;
        let mut data = Vec::with_capacity(len);
        self.visit(format, &mut |chunk| data.extend_from_slice(chunk));
        debug_assert_eq!(len, data.len());
        self.au = None;
        Some(data)
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

impl<Ctx: Clone> AccessUnit<Ctx> {
    fn start(
        meta: &crate::rtp::PacketMeta<Ctx>,
        additional_loss: u16,
        same_ts_as_prev: bool,
    ) -> Self {
        AccessUnit {
            start_ctx: meta.ctx.clone(),
            end_ctx: meta.ctx.clone(),
            timestamp: meta.timestamp,
            fu: None,
            meta: FrameMeta {
                is_random_access_point: true,
                seen_vcl: false,
                new_params: None,
                first_vcl_starts_picture: None,
                last_nal_hdr: None,
            },
            scanned_nals: 0,
            started: None,
            delivery: Default::default(),
            trimmed: false,

            // TODO: overflow?
            loss: meta.loss + additional_loss,
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

    /// If set via [`VideoFrameEnd::set_h265_parameters`], the in-band VPS, SPS,
    /// and PPS which were overridden. Parameter sets received later are
    /// compared against these to detect changes, so that a camera repeating
    /// its original parameters doesn't undo the override.
    overridden: Option<Box<(Bytes, Bytes, Bytes)>>,
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

        let all_pixel_dimensions = sps.all_pixel_dimensions()?;
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

        let (decoder_config_record, vps_nal_b, sps_nal_b, pps_nal_b) = {
            let hevc_decoder_config =
                record::decoder_configuration_record(pps_nal, &pps, sps_nal, &sps, vps_nal);
            (
                hevc_decoder_config.record,
                hevc_decoder_config.vps,
                hevc_decoder_config.sps,
                hevc_decoder_config.pps,
            )
        };
        Ok(InternalParameters {
            generic_parameters: super::VideoParameters {
                rfc6381_codec,
                all_pixel_dimensions,
                pixel_aspect_ratio,
                frame_rate,
                annex_b_parameter_sets: super::h26x::annex_b_parameter_sets(&[
                    &vps_nal_b, &sps_nal_b, &pps_nal_b,
                ]),
                decoder_config_record,
                codec: super::VideoParametersCodec::H265 {
                    sps: sps_nal_b.clone(),
                    pps: pps_nal_b.clone(),
                    vps: vps_nal_b.clone(),
                },
            },
            vps_nal: vps_nal_b,
            sps_nal: sps_nal_b,
            pps_nal: pps_nal_b,
            seen_extra_trailing_data,
            overridden: None,
        })
    }

    /// Returns the VPS as last received in-band (or via `sprop-vps`).
    fn in_band_vps(&self) -> &[u8] {
        self.overridden
            .as_ref()
            .map_or(&self.vps_nal[..], |o| &o.0[..])
    }

    /// Returns the SPS as last received in-band (or via `sprop-sps`).
    fn in_band_sps(&self) -> &[u8] {
        self.overridden
            .as_ref()
            .map_or(&self.sps_nal[..], |o| &o.1[..])
    }

    /// Returns the PPS as last received in-band (or via `sprop-pps`).
    fn in_band_pps(&self) -> &[u8] {
        self.overridden
            .as_ref()
            .map_or(&self.pps_nal[..], |o| &o.2[..])
    }
}

/// Returns true iff the bytes of `nal` equal the bytes of `[hdr, ..data]`.
fn nal_matches(nal: &[u8], hdr: nal::Header, pieces: &[BufRange], buf: &MarkBuf) -> bool {
    if nal.first_chunk() != Some(&*hdr) {
        return false;
    }
    let mut nal_pos = 2;
    for piece in pieces {
        let new_pos = nal_pos + usize::from(piece.len);
        if nal.len() < new_pos {
            return false;
        }
        let (s1, s2) = buf.split(piece.pos, usize::from(piece.len)).slices();
        if s1 != &nal[nal_pos..nal_pos + s1.len()] {
            return false;
        }
        if s2 != &nal[nal_pos + s1.len()..new_pos] {
            return false;
        }
        nal_pos = new_pos;
    }
    nal_pos == nal.len()
}

/// Saves the given NAL to a contiguous `Bytes`.
fn to_bytes(hdr: nal::Header, len: u32, pieces: &[BufRange], buf: &MarkBuf) -> Bytes {
    let len = crate::to_usize(len);
    let mut out = Vec::with_capacity(len);
    out.extend(&*hdr);
    for piece in pieces {
        let (s1, s2) = buf.split(piece.pos, usize::from(piece.len)).slices();
        out.extend_from_slice(s1);
        out.extend_from_slice(s2);
    }
    debug_assert_eq!(len, out.len());
    out.into()
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroU32;

    use crate::{
        PacketContext,
        buf::{MarkBuf, PacketRef},
        codec::testutil::Item,
        testutil::TestPacket,
        testutil::{assert_eq_hex, init_logging},
    };

    #[test]
    fn depacketize() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, Some("profile-id=1;sprop-sps=QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=;sprop-pps=RAHA8saNA7NA;sprop-vps=QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==")).unwrap();
        d.set_frame_format(crate::codec::FrameFormat {
            parameter_set_insertion: crate::codec::ParameterSetInsertion::Never,
            ..Default::default()
        });
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        {
            let pkt = TestPacket {
                // plain PREFIX_SEI packet.
                ctx: PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x4e\x01plain");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // aggregation packet.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            // .build(*b"\x18\x00\x09\x06stap-a 1\x00\x09\x06stap-a 2")
            .write(
                &mut buf,
                *b"\x60\x01\x00\x0a\x4e\x01stap-a 1\x00\x0a\x4e\x01stap-a 2",
            );
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU packet, start.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x62\x01\x94fu start, ");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU packet, middle.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 3,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x62\x01\x14fu middle, ");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU packet, end.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 4,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x62\x01\x54fu end");
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            _ => panic!(),
        };
        assert_eq_hex!(
            frame.data(),
            b"\x00\x00\x00\x07\x4e\x01plain\
              \x00\x00\x00\x0a\x4e\x01stap-a 1\
              \x00\x00\x00\x0a\x4e\x01stap-a 2\
              \x00\x00\x00\x1d\x28\x01fu start, fu middle, fu end"
        );
        assert!(!d.seen_inconsistent_fu_nal_hdr);
    }

    /// Tests that inline VPS/SPS/PPS NALs are stripped when `strip_inline_parameters` is true,
    /// and retained by default.
    ///
    /// The VPS/SPS/PPS bytes are sent as single-NAL RTP packets, matching the sprop parameters
    /// used to initialize the depacketizer (so no re-parse is triggered). An IDR_W_RADL (type 19)
    /// closes the access unit.
    #[test]
    fn depacketize_strip_inline_parameters() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        use base64::Engine as _;
        let b64 = base64::engine::general_purpose::STANDARD;

        // These VPS/SPS/PPS bytes match the sprop parameters in the depacketize test.
        let vps_nal = b64
            .decode("QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==")
            .unwrap();
        let sps_nal = b64
            .decode("QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=")
            .unwrap();
        let pps_nal = b64.decode("RAHA8saNA7NA").unwrap();
        // IDR_W_RADL NAL (type 19, 0x26; byte 0): \x26\x01 + data
        let idr_nal: &[u8] = b"\x26\x01idr";

        let sprop = "profile-id=1;sprop-sps=QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=;sprop-pps=RAHA8saNA7NA;sprop-vps=QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==";
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };

        let push_pkts = |d: &mut super::Depacketizer<PacketContext>, buf: &mut MarkBuf| {
            // VPS (mark=false: parameter sets can't end an AU).
            {
                let pkt = TestPacket {
                    ctx: PacketContext::dummy(),
                    timestamp,
                    ssrc: 0,
                    sequence_number: 0,
                    loss: 0,
                    mark: false,
                    payload_type: 0,
                }
                .write(buf, vps_nal.clone());
                d.push_collect(&pkt);
            }
            assert_eq!(d.pull(), None);
            // SPS
            {
                let pkt = TestPacket {
                    ctx: PacketContext::dummy(),
                    timestamp,
                    ssrc: 0,
                    sequence_number: 1,
                    loss: 0,
                    mark: false,
                    payload_type: 0,
                }
                .write(buf, sps_nal.clone());
                d.push_collect(&pkt);
            }
            assert_eq!(d.pull(), None);
            // PPS
            {
                let pkt = TestPacket {
                    ctx: PacketContext::dummy(),
                    timestamp,
                    ssrc: 0,
                    sequence_number: 2,
                    loss: 0,
                    mark: false,
                    payload_type: 0,
                }
                .write(buf, pps_nal.clone());
                d.push_collect(&pkt);
            }
            assert_eq!(d.pull(), None);
            // IDR_W_RADL (mark=true: ends the access unit).
            {
                let pkt = TestPacket {
                    ctx: PacketContext::dummy(),
                    timestamp,
                    ssrc: 0,
                    sequence_number: 3,
                    loss: 0,
                    mark: true,
                    payload_type: 0,
                }
                .write(buf, idr_nal.iter().copied());
                d.push_collect(&pkt);
            }
        };

        // Without stripping: VPS/SPS/PPS are included in frame data.
        {
            let mut d = super::Depacketizer::new(90_000, Some(sprop)).unwrap();
            push_pkts(&mut d, &mut buf);
            let frame = match d.pull() {
                Some(Ok(Item::Video(frame))) => frame,
                o => panic!("{o:#?}"),
            };
            let expected_len = (4 + vps_nal.len())
                + (4 + sps_nal.len())
                + (4 + pps_nal.len())
                + (4 + idr_nal.len());
            assert_eq!(
                frame.data().len(),
                expected_len,
                "without stripping, all NALs including VPS/SPS/PPS should be in output"
            );
        }

        // With stripping: only the IDR NAL is in frame data.
        {
            let mut d = super::Depacketizer::new(90_000, Some(sprop)).unwrap();
            d.set_frame_format(crate::codec::FrameFormat::MP4);
            push_pkts(&mut d, &mut buf);
            let frame = match d.pull() {
                Some(Ok(Item::Video(frame))) => frame,
                o => panic!("{o:#?}"),
            };
            let mut expected = Vec::new();
            expected.extend_from_slice(&(idr_nal.len() as u32).to_be_bytes());
            expected.extend_from_slice(idr_nal);
            // Only IDR NAL: 4-byte length prefix + idr_nal bytes.
            assert_eq_hex!(frame.data(), &expected);
        }

        // SIMPLE mode (Annex B framing, parameter sets prepended on each key frame).
        {
            let mut d = super::Depacketizer::new(90_000, Some(sprop)).unwrap();
            d.set_frame_format(crate::codec::FrameFormat::SIMPLE);
            push_pkts(&mut d, &mut buf);
            let frame = match d.pull() {
                Some(Ok(Item::Video(frame))) => frame,
                o => panic!("{o:#?}"),
            };
            let mut expected = Vec::new();
            for nal in [&*vps_nal, &*sps_nal, &*pps_nal, idr_nal] {
                expected.extend_from_slice(&super::super::h26x::ANNEX_B_START_CODE);
                expected.extend_from_slice(nal);
            }
            assert_eq_hex!(frame.data(), &expected);
        }
    }

    #[test]
    fn allow_inconsistent_fu_nal_header() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, None).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        {
            let pkt = TestPacket {
                // FU packet, start.
                ctx: PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x62\x01\x94fu start, ");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU packet, end.
                ctx: PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x62\x01\x66fu end"); // incorrect NAL type FdNut.
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            _ => panic!(),
        };
        assert_eq_hex!(frame.data(), b"\x00\x00\x00\x12\x28\x01fu start, fu end");
        assert!(d.seen_inconsistent_fu_nal_hdr);
    }

    /// Tests that a FU with both S and E bits set is treated as a complete NAL
    /// rather than rejected. RFC 7798 section 4.4.3 forbids this, but some cameras
    /// send it anyway for small NALs.
    #[test]
    fn single_fragment_fu() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, None).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        assert!(!d.seen_single_fragment_fu);
        // FU packet with S=1 E=1 FuType=1 (TRAIL_R) — header 0xc1,
        // as observed in the wild.
        let pkt = TestPacket {
            ctx: PacketContext::dummy(),
            timestamp,
            ssrc: 0,
            sequence_number: 0,
            loss: 0,
            mark: true,
            payload_type: 0,
        }
        .write(&mut buf, *b"\x62\x01\xc1small nal");
        d.push_collect(&pkt);
        assert!(d.seen_single_fragment_fu);
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            o => panic!("unexpected pull result: {o:?}"),
        };
        // Reconstructed NAL: type=1 layer=0 TID=1 -> header \x02\x01, then payload.
        // Length = 2 (header) + 9 (payload) = 11 = 0x0b.
        assert_eq_hex!(frame.data(), b"\x00\x00\x00\x0b\x02\x01small nal");
    }

    /// Tests that empty FU fragments (no payload bytes after the FU header) are
    /// accepted and ignored, as some cameras send them.
    #[test]
    fn empty_fragment() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, None).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        {
            let pkt = TestPacket {
                // FU packet, start (with data).
                ctx: PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x62\x01\x94start, ");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU packet, middle (empty payload after FU header).
                ctx: PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x62\x01\x14");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU packet, end (with data).
                ctx: PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x62\x01\x54end");
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            _ => panic!(),
        };
        assert_eq_hex!(frame.data(), b"\x00\x00\x00\x0c\x28\x01start, end");
    }

    #[test]
    fn skip_end_of_fragment() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, None).unwrap();
        let timestamp0 = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        {
            let pkt = TestPacket {
                // FU packet, start.
                ctx: PacketContext::dummy(),
                timestamp: timestamp0,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x62\x01\x94fu start, ");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        let timestamp1 = crate::Timestamp {
            timestamp: 1,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        {
            let pkt = TestPacket {
                // plain PREFIX_SEI packet.
                ctx: PacketContext::dummy(),
                timestamp: timestamp1,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x4e\x01plain");
            d.push_collect(&pkt);
        }
        let Some(Err(e)) = d.pull() else { panic!() };
        assert_eq!(
            e,
            "timestamp changed from 0 (mod-2^32: 0), npt 0.000 to 1 (mod-2^32: 1), npt 0.000 in the middle of a fragmented NAL"
        );
        let Some(Ok(Item::Video(f))) = d.pull() else {
            panic!()
        };
        assert_eq!(f.data, *b"\x00\x00\x00\x07\x4e\x01plain");
        assert_eq!(d.pull(), None);
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

    #[test]
    fn events_stream() {
        use crate::codec::events::testutil::{Event, Recorder, hex};
        use crate::codec::{Accumulate, UnitPosition};
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, None).unwrap();
        for accumulate in [Accumulate::Yes, Accumulate::No] {
            let mut h = Recorder::new(accumulate);
            let push = |d: &mut super::Depacketizer<PacketContext>,
                        buf: &mut MarkBuf,
                        seq: u16,
                        ts: i64,
                        mark: bool,
                        payload: &[u8],
                        h: &mut Recorder| {
                let meta = crate::rtp::PacketMeta {
                    ctx: PacketContext::dummy(),
                    timestamp: crate::Timestamp {
                        timestamp: ts,
                        clock_rate: NonZeroU32::new(90_000).unwrap(),
                        start: 0,
                    },
                    ssrc: 0,
                    sequence_number: seq,
                    mark,
                    loss: 0,
                };
                let pos = buf.end();
                buf.extend(payload);
                buf.advance_unparsed(buf.end());
                d.push(&PacketRef::new(meta, buf, pos, payload.len() as u16), h);
            };

            // IDR_W_RADL, fragmented.
            push(&mut d, &mut buf, 0, 0, false, b"\x62\x01\x93start", &mut h);
            assert_eq!(
                h.take(),
                vec![
                    Event::FrameStart {
                        is_random_access_point: true,
                        is_disposable: false,
                        has_new_parameters: false,
                    },
                    Event::Data(UnitPosition::Start, hex(b"\x26\x01start")),
                ]
            );
            push(&mut d, &mut buf, 1, 0, true, b"\x62\x01\x53 end", &mut h);
            assert_eq!(
                h.take(),
                vec![
                    Event::Data(UnitPosition::End, hex(b" end")),
                    Event::FrameEnd {
                        is_random_access_point: true,
                        is_disposable: false,
                        has_new_parameters: false,
                        data: (accumulate == Accumulate::Yes)
                            .then(|| hex(b"\x00\x00\x00\x0b\x26\x01start end")),
                    },
                ]
            );
            assert!(d.mark.is_none());

            // TRAIL_R, as a single NAL.
            push(&mut d, &mut buf, 2, 1, true, b"\x02\x01slice", &mut h);
            assert_eq!(
                h.take(),
                vec![
                    Event::FrameStart {
                        is_random_access_point: false,
                        is_disposable: false,
                        has_new_parameters: false,
                    },
                    Event::Data(UnitPosition::Complete, hex(b"\x02\x01slice")),
                    Event::FrameEnd {
                        is_random_access_point: false,
                        is_disposable: false,
                        has_new_parameters: false,
                        data: (accumulate == Accumulate::Yes)
                            .then(|| hex(b"\x00\x00\x00\x07\x02\x01slice")),
                    },
                ]
            );
        }
    }

    /// `VideoFrameEnd::set_h265_parameters` overrides parameters, surviving
    /// repeats of the in-band parameters it replaced.
    #[test]
    fn set_h265_parameters() {
        use crate::codec::{Accumulate, FrameFormat, VideoFrameEnd, VideoFrameStart, VideoHandler};
        use base64::Engine as _;
        let b64 = |s: &str| base64::engine::general_purpose::STANDARD.decode(s).unwrap();
        let (vps_a, sps_a, pps_a) = (
            b64("QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA=="),
            b64("QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE="),
            b64("RAHA8saNA7NA"),
        );
        let (vps_b, sps_b, pps_b) = (
            b64("QAEMAf//AWAAAAMAkAAAAwAAAwA/LAwAAgAAAwAoAAIAAgACgA=="),
            b64("QgEBAWAAAAMAkAAAAwAAAwA/oAUCAXFlLkkyS7I="),
            b64("RAHA8vAzJA=="),
        );

        struct Overrider<'a> {
            b: [&'a [u8]; 3],
            overridden: bool,
            frames: Vec<(bool, Vec<u8>)>,
        }
        impl VideoHandler<PacketContext> for Overrider<'_> {
            fn frame_start(&mut self, _: &VideoFrameStart<'_, PacketContext>) -> Accumulate {
                Accumulate::Yes
            }
            fn frame_end(&mut self, fe: &mut VideoFrameEnd<'_, PacketContext>) {
                if !self.overridden {
                    let [vps, sps, pps] = self.b;
                    fe.set_h265_parameters(vps, sps, pps).unwrap();
                    self.overridden = true;
                }
                let data = fe.complete_frame(FrameFormat::default()).unwrap();
                self.frames.push((fe.has_new_parameters(), data));
            }
        }

        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, None).unwrap();
        let mut h = Overrider {
            b: [&vps_b, &sps_b, &pps_b],
            overridden: false,
            frames: Vec::new(),
        };
        let mut push =
            |d: &mut super::Depacketizer<_>, seq: u16, ts: i64, mark: bool, payload: &[u8]| {
                let meta = crate::rtp::PacketMeta {
                    ctx: PacketContext::dummy(),
                    timestamp: crate::Timestamp {
                        timestamp: ts,
                        clock_rate: NonZeroU32::new(90_000).unwrap(),
                        start: 0,
                    },
                    ssrc: 0,
                    sequence_number: seq,
                    mark,
                    loss: 0,
                };
                let pos = buf.end();
                buf.extend(payload);
                buf.advance_unparsed(buf.end());
                d.push(
                    &PacketRef::new(meta, &buf, pos, payload.len() as u16),
                    &mut h,
                );
            };
        const IDR: &[u8] = b"\x26\x01slice";
        let mut expected_frame = Vec::new();
        for nal in [&vps_b[..], &sps_b[..], &pps_b[..], IDR] {
            expected_frame.extend_from_slice(&(nal.len() as u32).to_be_bytes());
            expected_frame.extend_from_slice(nal);
        }
        for (i, ts) in [0, 1].into_iter().enumerate() {
            let seq = 4 * i as u16;
            push(&mut d, seq, ts, false, &vps_a);
            push(&mut d, seq + 1, ts, false, &sps_a);
            push(&mut d, seq + 2, ts, false, &pps_a);
            push(&mut d, seq + 3, ts, true, IDR);
        }
        assert_eq!(
            h.frames,
            vec![
                (true, expected_frame.clone()), // overridden
                (false, expected_frame),        // in-band set A doesn't undo override
            ]
        );
        let Some(v) = d.parameters() else { panic!() };
        let crate::codec::VideoParametersCodec::H265 { sps, .. } = v.codec_params() else {
            panic!()
        };
        assert_eq!(&sps[..], &sps_b[..]);
    }
}
