// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [H.265](https://www.itu.int/rec/T-REC-H.265)-encoded video,
//! with RTP encoding as in [RFC 7798](https://tools.ietf.org/html/rfc7798).

#[doc(hidden)] // `pub` only for fuzz tests.
pub mod nal;

mod analyzer;
mod record;

pub(crate) use analyzer::Analyzer;

use std::collections::VecDeque;
use std::convert::TryFrom;

use base64::Engine as _;
use bytes::Bytes;

use crate::buf::{BufRange, MarkBuf, PacketRef};
use crate::codec::h26x::{NalAnalyzer as _, TolerantBitReader};
use crate::codec::{CodecItem, DepacketizeError, Handler, LossReason, ParametersRef};
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
    input_state: DepacketizerInputState,

    /// Completed items ready to be pulled via the legacy `push`/`pull` interface.
    pending: VecDeque<Result<CodecItem, DepacketizeError>>,

    /// The transport-independent layer, which holds the current access unit's
    /// NALs (in state `PreMark`) and the stream's parameters.
    analyzer: Analyzer<Ctx>,

    /// True if we've seen a FU sequence where the NAL headers differ between
    /// fragments.
    seen_inconsistent_fu_nal_hdr: bool,

    /// True if we've seen a FU with both S and E bits set (a single-fragment
    /// FU, forbidden by RFC 7798 section 4.4.3).
    seen_single_fragment_fu: bool,

    /// Output format controlling NAL framing and parameter set insertion.
    frame_format: super::FrameFormat,
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

/// RTP-level state of an access unit being accumulated during `PreMark` state.
/// The rest of its state is in the [`Analyzer`].
#[derive(Debug)]
struct AccessUnit {
    /// The initial header of the NAL being assembled from fragmentation
    /// units, if any.
    fu: Option<nal::Header>,
}

#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
enum DepacketizerInputState {
    /// Not processing an access unit; the next packet starts one.
    New,

    /// Ignoring the remainder of an access unit with the given timestamp,
    /// because of interior packet loss.
    Loss { timestamp: crate::Timestamp },

    /// Currently processing an access unit.
    /// This will be flushed after a marked packet or when receiving a later timestamp.
    PreMark(AccessUnit),
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
            pending: VecDeque::with_capacity(1),
            analyzer: Analyzer::with_internal_parameters(parameters),
            seen_inconsistent_fu_nal_hdr: false,
            seen_single_fragment_fu: false,
            frame_format: Default::default(),
        })
    }

    /// Sets the frame format for output assembly.
    ///
    /// If existing parameters were parsed with a different framing, they are
    /// re-parsed to produce the correct `extra_data` format.
    pub(super) fn set_frame_format(&mut self, format: super::FrameFormat) {
        self.frame_format = format;
        self.analyzer.set_framing(format.h26x_framing);
    }

    pub(super) fn check_invariants(&self) {
        if !matches!(self.input_state, DepacketizerInputState::PreMark(_)) {
            assert!(self.analyzer.is_idle());
        }
    }

    pub(super) fn parameters(&self) -> Option<super::ParametersRef<'_>> {
        self.analyzer.parameters().map(super::ParametersRef::Video)
    }

    /// Starts an access unit with the given packet.
    fn start_au(&mut self, meta: &crate::rtp::PacketMeta<Ctx>) -> AccessUnit {
        self.analyzer.start_au(meta.timestamp, meta.ctx.clone());
        AccessUnit { fu: None }
    }

    /// Supplies a new packet, delivering any resulting events to `handler`.
    pub(super) fn push_with(
        &mut self,
        pkt: &PacketRef<'_, Ctx>,
        handler: &mut impl Handler<Ctx>,
    ) -> Result<(), String> {
        let r = self.push_inner(pkt, handler);

        // Several error paths within `push_inner` just use the `?` operator to bail out with
        // `input_state` at `New` when they encounter a problem mid-access unit. Restore
        // the invariant so the caller can try to recover after error.
        if !matches!(self.input_state, DepacketizerInputState::PreMark(_)) {
            self.analyzer.discard_lossy_au();
        }
        r
    }

    fn push_inner(
        &mut self,
        pkt: &PacketRef<'_, Ctx>,
        handler: &mut impl Handler<Ctx>,
    ) -> Result<(), String> {
        let meta = &pkt.meta;
        let payload_pos = pkt.payload_pos();
        let payload_len = pkt.payload_len();
        let buf = pkt.buf();

        // Reporting loss discards any access unit in progress, so first note
        // its timestamp.
        let au_timestamp = self.analyzer.au_timestamp();
        let loss = meta.loss;
        if loss > 0 {
            self.analyzer
                .loss(&meta.ctx, LossReason::PacketLoss { packets: loss }, handler);
        }

        let mut r = Ok(());
        let mut access_unit =
            match std::mem::replace(&mut self.input_state, DepacketizerInputState::New) {
                DepacketizerInputState::New => self.start_au(meta),
                DepacketizerInputState::PreMark(access_unit) => {
                    let au_timestamp = au_timestamp.expect("au in progress");
                    if loss > 0 {
                        if au_timestamp.timestamp == meta.timestamp.timestamp {
                            // Loss within this access unit. Ignore until mark or new timestamp.
                            if !meta.mark {
                                self.input_state = DepacketizerInputState::Loss {
                                    timestamp: meta.timestamp,
                                };
                            }
                            return Ok(());
                        }
                        // A suffix of a previous access unit was lost; it's been discarded.
                        // A prefix of the new one may have been lost; try parsing.
                        self.start_au(meta)
                    } else if au_timestamp.timestamp != meta.timestamp.timestamp {
                        if access_unit.fu.is_some() {
                            // Something went wrong: perhaps the end of the last fragmentation unit was dropped
                            // without loss being indicated. Return error, but also process the current packet.
                            r = Err(format!(
                                "timestamp changed from {} to {} in the middle of a fragmented NAL",
                                au_timestamp, meta.timestamp
                            ));
                            self.analyzer.discard_lossy_au();
                            self.start_au(meta)
                        } else {
                            let last_nal_hdr = self
                                .analyzer
                                .last_nal_hdr()
                                .ok_or("nals should not be empty".to_string())?;
                            if can_end_au(last_nal_hdr.unit_type()) {
                                self.analyzer.finish_au_with(buf, &meta.ctx, handler)?;
                                self.start_au(meta)
                            } else {
                                log::debug!(
                                    "Bogus mid-access unit timestamp change after {:?}",
                                    last_nal_hdr
                                );
                                self.analyzer.set_au_timestamp(meta.timestamp);
                                access_unit
                            }
                        }
                    } else {
                        access_unit
                    }
                }
                DepacketizerInputState::Loss { timestamp } => {
                    debug_assert!(self.analyzer.is_idle());
                    if meta.timestamp.timestamp == timestamp.timestamp {
                        self.input_state = DepacketizerInputState::Loss { timestamp };
                        return Ok(());
                    }
                    self.start_au(meta)
                }
            };

        let mark = meta.mark;
        let timestamp = meta.timestamp;

        if payload_len < 2 {
            return Err("Short NAL".into());
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
                self.push_nal(buf, hdr_bytes, payload_pos + 2, payload_len - 2)?;
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
                    self.push_nal(buf, payload.peek_array::<2>(), pos + 2, nal_len - 2)?;
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
                let frag = BufRange {
                    pos: payload_pos + 3,
                    len: u32::from(payload_len - 3),
                };
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
                        self.analyzer
                            .start_nal(&*hdr, buf, frag.pos, crate::to_usize(frag.len))?;
                        self.push_fragment(buf, None, end)?;
                        if !end {
                            access_unit.fu = Some(hdr);
                        }
                    }
                    (false, Some(initial_hdr)) => {
                        if hdr != initial_hdr && !self.seen_inconsistent_fu_nal_hdr {
                            log::warn!(
                                "FU has inconsistent NAL header: {:?} then {:?}; will not log about this again for this stream",
                                initial_hdr,
                                hdr,
                            );
                            self.seen_inconsistent_fu_nal_hdr = true;
                        }
                        self.push_fragment(buf, Some(frag), end)?;
                        if !end {
                            access_unit.fu = Some(initial_hdr);
                        }
                    }
                    (false, None) => {
                        if loss > 0 {
                            // The start of this NAL was lost (and reported).
                            // Discard the rest of the access unit.
                            self.analyzer.discard_lossy_au();
                            self.input_state = DepacketizerInputState::Loss { timestamp };
                            return Ok(());
                        }
                        return Err("FU has start bit unset while no frag in progress".into());
                    }
                }
            }
            _ => return Err(format!("unexpected/bad nal header {hdr:?}")),
        }

        self.analyzer.stream_with(buf, handler);
        self.input_state = if mark {
            let last_nal_hdr = self
                .analyzer
                .last_nal_hdr()
                .ok_or("nals should not be empty after mark".to_string())?;
            if can_end_au(last_nal_hdr.unit_type()) {
                self.analyzer.finish_au_with(buf, &meta.ctx, handler)?;
                DepacketizerInputState::New
            } else {
                log::debug!(
                    "Bogus mid-access unit timestamp change after {:?}",
                    last_nal_hdr
                );
                self.analyzer.set_au_timestamp(timestamp);
                DepacketizerInputState::PreMark(access_unit)
            }
        } else {
            DepacketizerInputState::PreMark(access_unit)
        };
        r
    }

    /// Supplies a complete NAL with the given header, whose body is at
    /// `[pos, pos + len)`.
    fn push_nal(&mut self, buf: &MarkBuf, hdr: [u8; 2], pos: u64, len: u16) -> Result<(), String> {
        self.analyzer.start_nal(&hdr, buf, pos, usize::from(len))?;
        self.push_fragment(buf, None, true)
    }

    /// Supplies part of the NAL in progress, ending it if `end`.
    fn push_fragment(
        &mut self,
        buf: &MarkBuf,
        frag: Option<BufRange>,
        end: bool,
    ) -> Result<(), String> {
        if let Some(frag) = frag {
            self.analyzer
                .extend_nal(buf, frag.pos, crate::to_usize(frag.len))?;
        }
        if end {
            self.analyzer.finish_nal()?;
        }
        Ok(())
    }
}

impl Depacketizer<crate::PacketContext> {
    /// Supplies a new packet via the legacy `push`/`pull` interface.
    ///
    /// Between any two calls to `push`, the caller must call `pull` until it
    /// returns `None`.
    pub(super) fn push(&mut self, pkt: &PacketRef<'_>) -> Result<(), String> {
        if let Some(p) = self.pending.front() {
            panic!("push with data already pending: {p:?}");
        }
        let mut pending = std::mem::take(&mut self.pending);
        let format = self.frame_format;
        let r = self.push_with(
            pkt,
            &mut super::LegacyHandler {
                pending: &mut pending,
                meta: &pkt.meta,
                format,
            },
        );
        self.pending = pending;
        r
    }

    pub(super) fn pull(&mut self) -> Option<Result<CodecItem, DepacketizeError>> {
        self.pending.pop_front()
    }
}

/// Access to a finished access unit, for [`FrameEnd`].
pub(crate) struct FrameEndBody<'a> {
    /// The access unit's data, if accumulated and not yet taken.
    au: Option<AuData<'a>>,
    parameters: Option<&'a InternalParameters>,
    is_random_access_point: bool,
    has_new_parameters: bool,
}

struct AuData<'a> {
    nals: &'a [Nal],
    pieces: &'a [BufRange],
    buf: &'a MarkBuf,
}

impl FrameEndBody<'_> {
    pub(super) fn parameters(&self) -> Option<ParametersRef<'_>> {
        self.parameters
            .map(|p| ParametersRef::Video(&p.generic_parameters))
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
        Self::parse_vps_sps_pps(
            &vps_nal,
            &sps_nal,
            &pps_nal,
            false,
            super::h26x::Framing::FourByteLength,
        )
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
        framing: super::h26x::Framing,
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

        let (extra_data, vps_nal_b, sps_nal_b, pps_nal_b) = match framing {
            super::h26x::Framing::FourByteLength => {
                let hevc_decoder_config =
                    record::decoder_configuration_record(pps_nal, &pps, sps_nal, &sps, vps_nal);
                (
                    hevc_decoder_config.record,
                    hevc_decoder_config.vps,
                    hevc_decoder_config.sps,
                    hevc_decoder_config.pps,
                )
            }
            super::h26x::Framing::AnnexB => {
                // Annex B: start code prefix + VPS + start code prefix + SPS + start code prefix + PPS.
                let mut buf = bytes::BytesMut::with_capacity(
                    12 + vps_nal.len() + sps_nal.len() + pps_nal.len(),
                );
                buf.extend_from_slice(&super::h26x::ANNEX_B_START_CODE);
                let vps_start = buf.len();
                buf.extend_from_slice(vps_nal);
                let vps_end = buf.len();
                buf.extend_from_slice(&super::h26x::ANNEX_B_START_CODE);
                let sps_start = buf.len();
                buf.extend_from_slice(sps_nal);
                let sps_end = buf.len();
                buf.extend_from_slice(&super::h26x::ANNEX_B_START_CODE);
                let pps_start = buf.len();
                buf.extend_from_slice(pps_nal);
                let pps_end = buf.len();
                let buf = buf.freeze();
                (
                    buf.clone(),
                    buf.slice(vps_start..vps_end),
                    buf.slice(sps_start..sps_end),
                    buf.slice(pps_start..pps_end),
                )
            }
        };
        Ok(InternalParameters {
            generic_parameters: super::VideoParameters {
                rfc6381_codec,
                all_pixel_dimensions,
                pixel_aspect_ratio,
                frame_rate,
                extra_data,
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
        })
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroU32;

    use crate::{
        PacketContext,
        buf::{MarkBuf, PacketRef},
        codec::CodecItem,
        rtp::ReceivedPacketBuilder,
        testutil::{assert_eq_hex, init_logging},
    };

    fn push_via_buf(
        d: &mut super::Depacketizer<PacketContext>,
        meta: crate::rtp::PacketMeta,
        payload: &[u8],
        buf: &mut MarkBuf,
    ) -> Result<(), String> {
        let pos = buf.end();
        buf.extend(payload);
        buf.advance_unparsed(buf.end());
        d.push(&PacketRef::new(meta, buf, pos, payload.len() as u16))
    }

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
            let pkt = ReceivedPacketBuilder {
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
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        assert_eq!(d.pull(), None);
        {
            let pkt = ReceivedPacketBuilder {
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
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        assert_eq!(d.pull(), None);
        {
            let pkt = ReceivedPacketBuilder {
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
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        assert_eq!(d.pull(), None);
        {
            let pkt = ReceivedPacketBuilder {
                // FU packet, middle.
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
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        assert_eq!(d.pull(), None);
        {
            let pkt = ReceivedPacketBuilder {
                // FU packet, end.
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
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        let frame = match d.pull() {
            Some(Ok(CodecItem::VideoFrame(frame))) => frame,
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
                let pkt = ReceivedPacketBuilder {
                    ctx: PacketContext::dummy(),
                    stream_id: 0,
                    timestamp,
                    ssrc: 0,
                    sequence_number: 0,
                    loss: 0,
                    mark: false,
                    payload_type: 0,
                }
                .build(vps_nal.clone())
                .unwrap();
                push_via_buf(
                    d,
                    crate::rtp::PacketMeta::from_received(&pkt),
                    pkt.payload(),
                    buf,
                )
            }
            .unwrap();
            assert_eq!(d.pull(), None);
            // SPS
            {
                let pkt = ReceivedPacketBuilder {
                    ctx: PacketContext::dummy(),
                    stream_id: 0,
                    timestamp,
                    ssrc: 0,
                    sequence_number: 1,
                    loss: 0,
                    mark: false,
                    payload_type: 0,
                }
                .build(sps_nal.clone())
                .unwrap();
                push_via_buf(
                    d,
                    crate::rtp::PacketMeta::from_received(&pkt),
                    pkt.payload(),
                    buf,
                )
            }
            .unwrap();
            assert_eq!(d.pull(), None);
            // PPS
            {
                let pkt = ReceivedPacketBuilder {
                    ctx: PacketContext::dummy(),
                    stream_id: 0,
                    timestamp,
                    ssrc: 0,
                    sequence_number: 2,
                    loss: 0,
                    mark: false,
                    payload_type: 0,
                }
                .build(pps_nal.clone())
                .unwrap();
                push_via_buf(
                    d,
                    crate::rtp::PacketMeta::from_received(&pkt),
                    pkt.payload(),
                    buf,
                )
            }
            .unwrap();
            assert_eq!(d.pull(), None);
            // IDR_W_RADL (mark=true: ends the access unit).
            {
                let pkt = ReceivedPacketBuilder {
                    ctx: PacketContext::dummy(),
                    stream_id: 0,
                    timestamp,
                    ssrc: 0,
                    sequence_number: 3,
                    loss: 0,
                    mark: true,
                    payload_type: 0,
                }
                .build(idr_nal.iter().copied())
                .unwrap();
                push_via_buf(
                    d,
                    crate::rtp::PacketMeta::from_received(&pkt),
                    pkt.payload(),
                    buf,
                )
            }
            .unwrap();
        };

        // Without stripping: VPS/SPS/PPS are included in frame data.
        {
            let mut d = super::Depacketizer::new(90_000, Some(sprop)).unwrap();
            push_pkts(&mut d, &mut buf);
            let frame = match d.pull() {
                Some(Ok(CodecItem::VideoFrame(frame))) => frame,
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
                Some(Ok(CodecItem::VideoFrame(frame))) => frame,
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
                Some(Ok(CodecItem::VideoFrame(frame))) => frame,
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

    /// Tests that every IRAP picture type (not just IDR) is a random access
    /// point, and so gets the parameter sets prepended in `SIMPLE` mode.
    /// See [#132](https://github.com/scottlamb/retina/issues/132).
    #[test]
    fn irap_random_access() {
        init_logging();
        use base64::Engine as _;
        let b64 = base64::engine::general_purpose::STANDARD;
        let vps_nal = b64
            .decode("QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==")
            .unwrap();
        let sps_nal = b64
            .decode("QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=")
            .unwrap();
        let pps_nal = b64.decode("RAHA8saNA7NA").unwrap();
        let sprop = "profile-id=1;sprop-sps=QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=;sprop-pps=RAHA8saNA7NA;sprop-vps=QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==";

        for (vcl_nal, want_rap) in [
            (&b"\x2a\x01cra"[..], true),
            (&b"\x20\x01bla_w_lp"[..], true),
            (&b"\x22\x01bla_w_radl"[..], true),
            (&b"\x24\x01bla_n_lp"[..], true),
            (&b"\x26\x01idr_w_radl"[..], true),
            (&b"\x28\x01idr_n_lp"[..], true),
            (&b"\x02\x01trail_r"[..], false),
            (&b"\x10\x01rasl_n"[..], false),
        ] {
            let mut buf = MarkBuf::new(65536);
            let mut d = super::Depacketizer::new(90_000, Some(sprop)).unwrap();
            d.set_frame_format(crate::codec::FrameFormat::SIMPLE);
            let pkt = ReceivedPacketBuilder {
                ctx: PacketContext::dummy(),
                stream_id: 0,
                timestamp: crate::Timestamp {
                    timestamp: 0,
                    clock_rate: NonZeroU32::new(90_000).unwrap(),
                    start: 0,
                },
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(vcl_nal.iter().copied())
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
            .unwrap();
            let frame = match d.pull() {
                Some(Ok(CodecItem::VideoFrame(frame))) => frame,
                o => panic!("{o:#?}"),
            };
            assert_eq!(
                frame.is_random_access_point(),
                want_rap,
                "NAL header {:02x?}",
                &vcl_nal[..2]
            );
            let mut expected = Vec::new();
            let param_nals: &[&[u8]] = if want_rap {
                &[&vps_nal, &sps_nal, &pps_nal]
            } else {
                &[]
            };
            for nal in param_nals.iter().copied().chain([vcl_nal]) {
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
            let pkt = ReceivedPacketBuilder {
                // FU packet, start.
                ctx: PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x62\x01\x94fu start, ")
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        assert_eq!(d.pull(), None);
        {
            let pkt = ReceivedPacketBuilder {
                // FU packet, end.
                ctx: PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x62\x01\x66fu end") // incorrect NAL type FdNut.
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        let frame = match d.pull() {
            Some(Ok(CodecItem::VideoFrame(frame))) => frame,
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
        push_via_buf(
            &mut d,
            crate::rtp::PacketMeta {
                ctx: PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
            },
            b"\x62\x01\xc1small nal",
            &mut buf,
        )
        .unwrap();
        assert!(d.seen_single_fragment_fu);
        let frame = match d.pull() {
            Some(Ok(CodecItem::VideoFrame(frame))) => frame,
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
            let pkt = ReceivedPacketBuilder {
                // FU packet, start (with data).
                ctx: PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x62\x01\x94start, ")
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        assert_eq!(d.pull(), None);
        {
            let pkt = ReceivedPacketBuilder {
                // FU packet, middle (empty payload after FU header).
                ctx: PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x62\x01\x14")
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        assert_eq!(d.pull(), None);
        {
            let pkt = ReceivedPacketBuilder {
                // FU packet, end (with data).
                ctx: PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x62\x01\x54end")
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        let frame = match d.pull() {
            Some(Ok(CodecItem::VideoFrame(frame))) => frame,
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
            let pkt = ReceivedPacketBuilder {
                // FU packet, start.
                ctx: PacketContext::dummy(),
                stream_id: 0,
                timestamp: timestamp0,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x62\x01\x94fu start, ")
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        assert_eq!(d.pull(), None);
        let timestamp1 = crate::Timestamp {
            timestamp: 1,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        let e = {
            let pkt = ReceivedPacketBuilder {
                // plain TRAIL_R packet.
                ctx: PacketContext::dummy(),
                stream_id: 0,
                timestamp: timestamp1,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x02\x01plain")
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap_err();
        assert_eq!(
            e,
            "timestamp changed from 0 (mod-2^32: 0), npt 0.000 to 1 (mod-2^32: 1), npt 0.000 in the middle of a fragmented NAL"
        );
        let Some(Ok(CodecItem::VideoFrame(f))) = d.pull() else {
            panic!()
        };
        assert_eq!(f.data, *b"\x00\x00\x00\x07\x02\x01plain");
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
                    stream_id: 0,
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
                d.push_with(&PacketRef::new(meta, buf, pos, payload.len() as u16), h)
                    .unwrap();
            };

            // IDR_W_RADL, fragmented.
            push(&mut d, &mut buf, 0, 0, false, b"\x62\x01\x93start", &mut h);
            assert_eq!(
                h.take(),
                vec![
                    Event::FrameStart {
                        loss: 0,
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
                        loss: 0,
                        is_random_access_point: true,
                        is_disposable: false,
                        has_new_parameters: false,
                        data: (accumulate == Accumulate::Yes)
                            .then(|| hex(b"\x00\x00\x00\x0b\x26\x01start end")),
                    },
                ]
            );
            assert!(!d.analyzer.has_mark());

            // TRAIL_R, as a single NAL.
            push(&mut d, &mut buf, 2, 1, true, b"\x02\x01slice", &mut h);
            assert_eq!(
                h.take(),
                vec![
                    Event::FrameStart {
                        loss: 0,
                        is_random_access_point: false,
                        is_disposable: false,
                        has_new_parameters: false,
                    },
                    Event::Data(UnitPosition::Complete, hex(b"\x02\x01slice")),
                    Event::FrameEnd {
                        loss: 0,
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
}
