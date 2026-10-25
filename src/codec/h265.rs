// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [H.265](https://www.itu.int/rec/T-REC-H.265)-encoded video,
//! with RTP encoding as in [RFC 7798](https://tools.ietf.org/html/rfc7798).

#[doc(hidden)] // `pub` only for fuzz tests.
pub mod nal;

mod analyzer;
mod record;

#[cfg(not(feature = "unstable-codec-analyzer"))]
pub(crate) use analyzer::Analyzer;
#[cfg(feature = "unstable-codec-analyzer")]
#[cfg_attr(docsrs, doc(cfg(feature = "unstable-codec-analyzer")))]
pub use analyzer::Analyzer;

use std::convert::TryFrom;

use base64::Engine as _;
use bytes::Bytes;

use crate::buf::{BufRange, MarkBuf};
use crate::codec::h26x::{NalAnalyzer as _, TolerantBitReader};
use crate::codec::{LossReason, VideoHandler, VideoParameters};
use crate::inputs::Input as _;
use crate::rtp::ReceivedPacketRef;

/// Returns parameters for the given VPS, SPS, and PPS, in that order.
pub(super) fn parameters_from_sets(sets: &[&[u8]]) -> Result<VideoParameters, super::Error> {
    let &[vps, sps, pps] = sets else {
        unreachable!("expected VPS, SPS, and PPS");
    };
    InternalParameters::parse_vps_sps_pps(vps, sps, pps, true).map(|p| p.generic_parameters)
}

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

    /// Completed items ready to be pulled via the test-only `push_collect`/`pull` interface.
    #[cfg(test)]
    pending: super::testutil::Pending,

    /// The transport-independent layer, which holds the current access unit's
    /// NALs (in state `PreMark`) and the stream's parameters.
    analyzer: Analyzer<Ctx>,

    /// True if we've seen a FU sequence where the NAL headers differ between
    /// fragments.
    seen_inconsistent_fu_nal_hdr: bool,

    /// True if we've seen a FU with both S and E bits set (a single-fragment
    /// FU, forbidden by RFC 7798 section 4.4.3).
    seen_single_fragment_fu: bool,

    /// See [`super::VideoDepacketizer::set_max_frame_bytes`].
    max_frame_bytes: usize,

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

/// RTP-level state of an access unit being accumulated during `PreMark` state.
/// The rest of its state is in the [`Analyzer`].
#[derive(Debug)]
struct AccessUnit {
    /// The initial header of the NAL being assembled from fragmentation
    /// units, if any.
    fu: Option<nal::Header>,

    /// Payload bytes retained since the access unit started or the analyzer
    /// last released its data, for [`Depacketizer::max_frame_bytes`].
    retained: usize,
}

#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
enum DepacketizerInputState {
    /// Not processing an access unit; the next packet starts one.
    New,

    /// Ignoring the remainder of an access unit with the given timestamp,
    /// because of interior packet loss or another problem already reported.
    Loss { timestamp: crate::Timestamp },

    /// Currently processing an access unit.
    /// This will be flushed after a marked packet or when receiving a later timestamp.
    PreMark(AccessUnit),
}

impl<Ctx: Clone> Depacketizer<Ctx> {
    pub(super) fn new(
        clock_rate: u32,
        format_specific_params: Option<&str>,
    ) -> Result<Self, super::Error> {
        if clock_rate != 90_000 {
            return Err(super::Error::invalid(format!(
                "invalid H.265 clock rate {clock_rate}; must always be 90000"
            )));
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
            analyzer: Analyzer::with_internal_parameters(parameters),
            seen_inconsistent_fu_nal_hdr: false,
            seen_single_fragment_fu: false,
            max_frame_bytes: usize::MAX,
            #[cfg(test)]
            test_format: Default::default(),
        })
    }

    pub(super) fn set_max_frame_bytes(&mut self, max_frame_bytes: usize) {
        self.max_frame_bytes = max_frame_bytes;
    }

    /// Sets the format used by the test-only `push_collect`/`pull` interface.
    #[cfg(test)]
    fn set_frame_format(&mut self, format: super::FrameFormat) {
        self.test_format = format;
    }

    pub(super) fn check_invariants(&self) {
        if !matches!(self.input_state, DepacketizerInputState::PreMark(_)) {
            assert!(self.analyzer.is_idle());
        }
    }

    pub(super) fn parameters(&self) -> Option<&VideoParameters> {
        self.analyzer.parameters()
    }

    /// Starts an access unit with the given packet.
    fn start_au(&mut self, meta: &crate::rtp::ReceivedPacketMeta<Ctx>) -> AccessUnit {
        self.analyzer.start_au(meta.timestamp, meta.ctx.clone());
        AccessUnit {
            fu: None,
            retained: 0,
        }
    }

    /// Supplies a new packet, delivering any resulting events to `handler`.
    pub(super) fn push(
        &mut self,
        pkt: &ReceivedPacketRef<'_, Ctx>,
        handler: &mut impl VideoHandler<Ctx>,
    ) {
        if let Err(description) = self.push_inner(pkt, handler) {
            // Several error paths within `push_inner` just use the `?`
            // operator to bail out with `input_state` at `New` when they
            // encounter a problem mid-access unit. Discard it and report.
            self.input_state = DepacketizerInputState::New;
            self.analyzer.loss(
                &pkt.meta.ctx,
                LossReason::Corrupt(super::Corruption::new(description)),
                handler,
            );
        }
        debug_assert!(
            matches!(self.input_state, DepacketizerInputState::PreMark(_))
                || self.analyzer.is_idle()
        );
    }

    fn push_inner(
        &mut self,
        pkt: &ReceivedPacketRef<'_, Ctx>,
        handler: &mut impl VideoHandler<Ctx>,
    ) -> Result<(), String> {
        let meta = &pkt.meta;
        let payload_pos = pkt.payload_pos();
        let payload_len = pkt.payload_len();
        let buf = pkt.buf();

        // Reporting loss discards any access unit in progress, so first note
        // its timestamp and whether it was evicted.
        let au_timestamp = self.analyzer.au_timestamp();
        let evicted = self.analyzer.is_evicted();
        let loss = meta.continuity.loss_count();
        if let Some(reason) = super::packet_loss_reason(meta.continuity) {
            self.analyzer.loss(&meta.ctx, reason, handler);
        }
        if evicted {
            self.analyzer.loss(&meta.ctx, LossReason::Evicted, handler);
        }

        let mut access_unit =
            match std::mem::replace(&mut self.input_state, DepacketizerInputState::New) {
                DepacketizerInputState::New => self.start_au(meta),
                DepacketizerInputState::PreMark(access_unit) => {
                    let au_timestamp = au_timestamp.expect("au in progress");
                    if loss > 0 || evicted {
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
                            // without loss being indicated. Report corruption, but also process the current packet.
                            self.analyzer.loss(
                            &meta.ctx,
                            LossReason::Corrupt(super::Corruption::new(format!(
                                "timestamp changed from {} to {} in the middle of a fragmented NAL",
                                au_timestamp, meta.timestamp
                            ))),
                            handler,
                        );
                            self.start_au(meta)
                        } else {
                            let last_nal_hdr = self
                                .analyzer
                                .last_nal_hdr()
                                .ok_or("nals should not be empty".to_string())?;
                            if can_end_au(last_nal_hdr.unit_type()) {
                                self.analyzer.finish_au_with(buf, &meta.ctx, handler);
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
        access_unit.retained += usize::from(payload_len);
        if access_unit.retained > self.max_frame_bytes {
            self.analyzer.loss(
                &meta.ctx,
                LossReason::TooLarge {
                    limit: self.max_frame_bytes,
                },
                handler,
            );
            if !mark {
                self.input_state = DepacketizerInputState::Loss { timestamp };
            }
            return Ok(());
        }
        // Pin the payload data in the ring buffer, allowing for reordering.
        self.analyzer.pin_at(buf, pkt.pin_pos());

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
                            .start_nal(&*hdr, buf, frag.pos, crate::to_usize(frag.len))
                            .map_err(|e| e.to_string())?;
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
        if !self.analyzer.has_mark() {
            access_unit.retained = 0;
        }
        self.input_state = if mark {
            let last_nal_hdr = self
                .analyzer
                .last_nal_hdr()
                .ok_or("nals should not be empty after mark".to_string())?;
            if can_end_au(last_nal_hdr.unit_type()) {
                self.analyzer.finish_au_with(buf, &meta.ctx, handler);
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
        Ok(())
    }

    /// Supplies a complete NAL with the given header, whose body is at
    /// `[pos, pos + len)`.
    fn push_nal(&mut self, buf: &MarkBuf, hdr: [u8; 2], pos: u64, len: u16) -> Result<(), String> {
        self.analyzer
            .start_nal(&hdr, buf, pos, usize::from(len))
            .map_err(|e| e.to_string())?;
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
                .extend_nal(buf, frag.pos, crate::to_usize(frag.len))
                .map_err(|e| e.to_string())?;
        }
        if end {
            self.analyzer.finish_nal().map_err(|e| e.to_string())?;
        }
        Ok(())
    }
}

#[cfg(test)]
impl Depacketizer<crate::PacketContext> {
    /// Supplies a new packet via the test-only `push_collect`/`pull` interface.
    ///
    /// Between any two calls to `push_collect`, the caller must call `pull`
    /// until it returns `None`.
    fn push_collect(&mut self, pkt: &ReceivedPacketRef<'_, crate::PacketContext>) {
        let mut pending = std::mem::take(&mut self.pending);
        pending.push_reporting_loss(self.test_format, |c| self.push(pkt, c));
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
    parameters: &'a Option<InternalParameters>,
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

    pub(super) fn build(&mut self, format: super::FrameFormat) -> Option<Vec<u8>> {
        let len = self.data_len(format)?;
        let mut data = Vec::with_capacity(len);
        self.visit(format, &mut |chunk| data.extend_from_slice(chunk));
        debug_assert_eq!(len, data.len());
        self.au = None;
        Some(data)
    }
}

/// Returns true for a "random access skipped leading (RASL)" VCL NAL unit.
///
/// H.265 section 7.4.2.2 / Table 7-1: these may reference pictures preceding
/// their associated IRAP picture in decoding order.
fn is_rasl(hdr: nal::Header) -> bool {
    matches!(hdr.unit_type(), nal::UnitType::RaslN | nal::UnitType::RaslR)
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

    /// If set via [`VideoFrameStart::set_parameters`], the in-band VPS, SPS,
    /// and PPS which were overridden. Parameter sets received later are
    /// compared against these to detect changes, so that a camera repeating
    /// its original parameters doesn't undo the override.
    overridden: Option<Box<(Bytes, Bytes, Bytes)>>,
}

/// Parameters set via [`VideoFrameStart::set_parameters`], not yet committed.
#[derive(Debug)]
struct ParametersOverride(Box<InternalParameters>);

impl super::events::ParametersOverrideSlot for Option<ParametersOverride> {
    fn parameters(&self) -> Option<&VideoParameters> {
        self.as_ref().map(|o| &o.0.generic_parameters)
    }

    fn set(&mut self, parameters: &VideoParameters) -> Result<(), super::Error> {
        let super::VideoParametersCodec::H265 { vps, sps, pps } = &parameters.codec else {
            return Err(super::Error::invalid(
                "parameters aren't for an H.265 stream",
            ));
        };
        let p = InternalParameters::parse_vps_sps_pps(vps, sps, pps, true)?;
        *self = Some(ParametersOverride(Box::new(p)));
        Ok(())
    }
}

impl ParametersOverride {
    /// Returns the parameters to use in place of `old`, remembering the in-band
    /// parameter sets `old` represents so that repeats of them don't undo the override.
    fn commit(self, old: Option<&InternalParameters>) -> InternalParameters {
        let mut new = *self.0;
        if let Some(old) = old {
            new.seen_extra_trailing_data = old.seen_extra_trailing_data;
            new.overridden = Some(Box::new((
                Bytes::copy_from_slice(old.in_band_vps()),
                Bytes::copy_from_slice(old.in_band_sps()),
                Bytes::copy_from_slice(old.in_band_pps()),
            )));
        } else {
            new.seen_extra_trailing_data = false;
        }
        new
    }
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
        Self::parse_vps_sps_pps(&vps_nal, &sps_nal, &pps_nal, false).map_err(|e| e.to_string())
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
    ) -> Result<InternalParameters, super::Error> {
        let (vps_h, _vps_bits) = nal::split(vps_nal).map_err(|e| {
            super::Error::invalid(format!("failed to parse VPS: {e}")).with_source(e)
        })?;
        if vps_h.unit_type() != nal::UnitType::VpsNut {
            return Err(super::Error::invalid("VPS NAL is not VPS"));
        }

        let sps_hex = crate::hex::LimitedHex::new(sps_nal, 256);
        let (sps_h, sps_bits) = nal::split(sps_nal).map_err(|e| {
            super::Error::invalid(format!("{e}\nwhile parsing SPS: {sps_hex}")).with_source(e)
        })?;
        if sps_h.unit_type() != nal::UnitType::SpsNut {
            return Err(super::Error::invalid("SPS NAL is not SPS"));
        }
        let mut sps_has_extra_trailing_data = false;
        let sps_bits = TolerantBitReader {
            inner: sps_bits,
            has_extra_trailing_data: &mut sps_has_extra_trailing_data,
        };
        let sps = nal::Sps::from_bits(sps_bits).map_err(|e| {
            super::Error::invalid(format!("{e}\nwhile parsing SPS: {sps_hex}")).with_source(e)
        })?;
        if sps_has_extra_trailing_data && !seen_extra_trailing_data {
            log::warn!(
                "Ignoring trailing data in SPS {sps_hex}; will not log about trailing data again for this stream."
            );
            seen_extra_trailing_data = true;
        }

        let pps_hex = crate::hex::LimitedHex::new(pps_nal, 256);
        let (pps_h, pps_bits) = nal::split(pps_nal).map_err(|e| {
            super::Error::invalid(format!("{e}\nwhile parsing PPS: {pps_hex}")).with_source(e)
        })?;
        if pps_h.unit_type() != nal::UnitType::PpsNut {
            return Err(super::Error::invalid("PPS NAL is not PPS"));
        }
        let mut pps_has_extra_trailing_data = false;
        let pps_bits = TolerantBitReader {
            inner: pps_bits,
            has_extra_trailing_data: &mut pps_has_extra_trailing_data,
        };
        let pps = nal::Pps::from_bits(pps_bits).map_err(|e| {
            super::Error::invalid(format!("{e}\nwhile parsing PPS: {pps_hex}")).with_source(e)
        })?;
        if pps_has_extra_trailing_data && !seen_extra_trailing_data {
            log::warn!(
                "Ignoring trailing data in PPS {pps_hex}; will not log about trailing data again for this stream."
            );
            seen_extra_trailing_data = true;
        }

        let rfc6381_codec = sps.rfc6381_codec();

        let all_pixel_dimensions = sps
            .all_pixel_dimensions()
            .map_err(|e| super::Error::invalid(format!("{e}\nin SPS: {sps_hex}")).with_source(e))?;
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

/// Packetizes H.265 NAL units per RFC 7798.
///
/// Emits single NAL unit packets, aggregation packets (if enabled), and
/// fragmentation units. Only `tx-mode=SRST` with `sprop-max-don-diff=0` is
/// supported, so there are no DONL or DOND fields. See
/// [`crate::codec::VideoPacketizer`].
#[cfg(feature = "unstable-send")]
pub(crate) type Packetizer = super::h26x::packetizer::Packetizer<PacketizeCodec>;

#[cfg(feature = "unstable-send")]
#[derive(Debug)]
pub(crate) enum PacketizeCodec {}

#[cfg(feature = "unstable-send")]
impl super::h26x::packetizer::Codec for PacketizeCodec {
    type Header = [u8; 2];
    type FuHeader = [u8; 3];
    const PARAMETER_SETS: usize = 3;

    fn parameter_sets(parameters: &VideoParameters) -> Option<Vec<Bytes>> {
        match &parameters.codec {
            super::VideoParametersCodec::H265 { vps, sps, pps } => {
                Some(vec![vps.clone(), sps.clone(), pps.clone()])
            }
            _ => None,
        }
    }

    fn parameters(sets: &[&[u8]]) -> Result<VideoParameters, super::Error> {
        parameters_from_sets(sets)
    }

    fn payload_format(_parameters: &VideoParameters, sets: &[Bytes]) -> super::PayloadFormat {
        let e = &base64::engine::general_purpose::STANDARD;
        super::PayloadFormat::new("video", "H265", 90_000).with_fmtp(format!(
            "sprop-vps={};sprop-sps={};sprop-pps={}",
            e.encode(&sets[0]),
            e.encode(&sets[1]),
            e.encode(&sets[2]),
        ))
    }

    fn parameter_set_index(hdr: [u8; 2]) -> Option<usize> {
        match unit_type(hdr) {
            nal::UnitType::VpsNut => Some(0),
            nal::UnitType::SpsNut => Some(1),
            nal::UnitType::PpsNut => Some(2),
            _ => None,
        }
    }

    /// Types 48–63 are unspecified by H.265, and RFC 7798 uses 48–50 for
    /// aggregation packets, fragmentation units, and PACI packets.
    fn invalid_header(hdr: [u8; 2]) -> Option<&'static str> {
        if hdr[0] >> 1 & 0b11_1111 >= 48 {
            Some("invalid type")
        } else if hdr[1] & 0b111 == 0 {
            Some("zero TemporalId plus 1")
        } else {
            None
        }
    }

    /// Per RFC 7798 section 4.4.2, the F bit is the OR of the aggregated NALs'
    /// F bits, and the LayerId and TID are the minimums of theirs.
    fn aggregation_header(a: [u8; 2], b: [u8; 2]) -> [u8; 2] {
        let f = (a[0] | b[0]) & 0b1000_0000;
        let layer_id = |h: [u8; 2]| (h[0] & 0b1) << 5 | h[1] >> 3;
        let layer_id = layer_id(a).min(layer_id(b));
        let tid = (a[1] & 0b111).min(b[1] & 0b111);
        [
            f | 48 << 1 | layer_id >> 5,
            (layer_id & 0b1_1111) << 3 | tid,
        ]
    }

    /// Per RFC 7798 section 4.4.3, the payload header is the NAL's header with
    /// type 49, followed by an FU header with the start and end bits and the
    /// NAL's type.
    fn fu_header(hdr: [u8; 2], start: bool, end: bool) -> [u8; 3] {
        [
            (hdr[0] & 0b1000_0001) | 49 << 1,
            hdr[1],
            u8::from(start) << 7 | u8::from(end) << 6 | (hdr[0] >> 1 & 0b11_1111),
        ]
    }

    fn is_vcl(hdr: [u8; 2]) -> bool {
        matches!(
            unit_type(hdr).unit_type_class(),
            nal::UnitTypeClass::Vcl { .. }
        )
    }

    fn is_access_unit_delimiter(hdr: [u8; 2]) -> bool {
        unit_type(hdr) == nal::UnitType::AudNut
    }

    fn ends_sequence(hdr: [u8; 2]) -> bool {
        matches!(
            unit_type(hdr),
            nal::UnitType::EosNut | nal::UnitType::EobNut
        )
    }

    /// Per section 7.4.2.2, the filler's `TemporalId` must match the access
    /// unit's, so this copies the VCL NAL's layer ID and TID.
    fn filler_header(vcl: Option<[u8; 2]>) -> [u8; 2] {
        let vcl = vcl.unwrap_or([0, 1]);
        [u8::from(nal::UnitType::FdNut) << 1 | (vcl[0] & 0b1), vcl[1]]
    }
}

/// Returns the type of a NAL with the given header.
///
/// Unlike [`nal::Header::try_from`], this tolerates the `forbidden_zero_bit`,
/// which the packetizer sets on NALs it truncates.
#[cfg(feature = "unstable-send")]
fn unit_type(hdr: [u8; 2]) -> nal::UnitType {
    nal::UnitType::try_from(hdr[0] >> 1 & 0b11_1111).expect("6-bit type is in range")
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroU32;

    use crate::{
        PacketContext,
        buf::MarkBuf,
        codec::testutil::Item,
        rtp::ReceivedPacketRef,
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
            let pkt = TestPacket {
                ctx: PacketContext::dummy(),
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
            .write(&mut buf, vcl_nal.iter().copied());
            d.push_collect(&pkt);
            let frame = match d.pull() {
                Some(Ok(Item::Video(frame))) => frame,
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
                // plain TRAIL_R packet.
                ctx: PacketContext::dummy(),
                timestamp: timestamp1,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x02\x01plain");
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
        use crate::codec::{Accumulate, Position};
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
                let meta = crate::rtp::ReceivedPacketMeta {
                    ctx: PacketContext::dummy(),
                    timestamp: crate::Timestamp {
                        timestamp: ts,
                        clock_rate: NonZeroU32::new(90_000).unwrap(),
                        start: 0,
                    },
                    ssrc: 0,
                    sequence_number: seq,
                    mark,
                    continuity: crate::rtp::Continuity::Contiguous,
                };
                let pos = buf.end();
                buf.extend(payload);
                buf.advance_unparsed(buf.end());
                d.push(
                    &ReceivedPacketRef::new(meta, buf, pos, payload.len() as u16),
                    h,
                );
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
                    Event::Data(Position::Start, hex(b"\x26\x01start")),
                ]
            );
            push(&mut d, &mut buf, 1, 0, true, b"\x62\x01\x53 end", &mut h);
            assert_eq!(
                h.take(),
                vec![
                    Event::Data(Position::End, hex(b" end")),
                    Event::FrameEnd {
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
                        is_random_access_point: false,
                        is_disposable: false,
                        has_new_parameters: false,
                    },
                    Event::Data(Position::Complete, hex(b"\x02\x01slice")),
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

    /// `VideoFrameStart::set_parameters` overrides parameters, surviving
    /// repeats of the in-band parameters it replaced.
    #[test]
    fn set_parameters() {
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

        /// Records `(has_new_parameters at start, SPS at start, has_new_parameters at end, data)`.
        struct Overrider<'a> {
            b: [&'a [u8]; 3],
            overridden: bool,
            frames: Vec<(bool, Vec<u8>, bool, Vec<u8>)>,
            start: Option<(bool, Vec<u8>)>,
        }
        fn sps(p: Option<&crate::codec::VideoParameters>) -> Vec<u8> {
            match &p.unwrap().codec {
                crate::codec::VideoParametersCodec::H265 { sps, .. } => sps.to_vec(),
                _ => unreachable!(),
            }
        }
        impl VideoHandler<PacketContext> for Overrider<'_> {
            fn frame_start(&mut self, fs: &mut VideoFrameStart<'_, PacketContext>) -> Accumulate {
                if !self.overridden {
                    let p =
                        crate::codec::VideoParameters::from_h265_parameter_sets(self.b).unwrap();
                    fs.set_parameters(&p).unwrap();
                    self.overridden = true;
                }
                self.start = Some((fs.has_new_parameters(), sps(fs.parameters())));
                Accumulate::Yes
            }
            fn frame_end(&mut self, fe: &mut VideoFrameEnd<'_, PacketContext>) {
                let (start_new, start_sps) = self.start.take().unwrap();
                let data = fe.complete_frame(FrameFormat::default()).unwrap();
                self.frames
                    .push((start_new, start_sps, fe.has_new_parameters(), data));
            }
        }

        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, None).unwrap();
        let mut h = Overrider {
            b: [&vps_b, &sps_b, &pps_b],
            overridden: false,
            frames: Vec::new(),
            start: None,
        };
        let mut push =
            |d: &mut super::Depacketizer<_>, seq: u16, ts: i64, mark: bool, payload: &[u8]| {
                let meta = crate::rtp::ReceivedPacketMeta {
                    ctx: PacketContext::dummy(),
                    timestamp: crate::Timestamp {
                        timestamp: ts,
                        clock_rate: NonZeroU32::new(90_000).unwrap(),
                        start: 0,
                    },
                    ssrc: 0,
                    sequence_number: seq,
                    mark,
                    continuity: crate::rtp::Continuity::Contiguous,
                };
                let pos = buf.end();
                buf.extend(payload);
                buf.advance_unparsed(buf.end());
                d.push(
                    &ReceivedPacketRef::new(meta, &buf, pos, payload.len() as u16),
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
                // overridden
                (true, sps_b.clone(), true, expected_frame.clone()),
                // in-band set A doesn't undo override
                (false, sps_b.clone(), false, expected_frame),
            ]
        );
        let Some(v) = d.parameters() else { panic!() };
        let crate::codec::VideoParametersCodec::H265 { sps, .. } = &v.codec else {
            panic!()
        };
        assert_eq!(&sps[..], &sps_b[..]);
    }
}

#[cfg(all(test, feature = "unstable-send"))]
mod packetizer_tests {
    use std::num::NonZeroU32;

    use super::*;
    use crate::codec::{
        ParameterSetInsertion, Payload, PayloadSink, Position, VideoFrameInfo,
        VideoPacketizerOptions,
    };
    use crate::testutil::HexDebug;

    fn b64(s: &str) -> Vec<u8> {
        base64::engine::general_purpose::STANDARD.decode(s).unwrap()
    }

    fn parameter_sets() -> [Vec<u8>; 3] {
        [
            b64("QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA=="),
            b64("QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE="),
            b64("RAHA8saNA7NA"),
        ]
    }

    /// A payload as recorded by `Recorder`: `(mark, frame_start, data)`.
    type Recorded = (bool, bool, HexDebug);

    struct Recorder {
        payloads: Vec<Recorded>,
        congested: bool,
        max_payload_size: u16,
    }

    impl Default for Recorder {
        fn default() -> Self {
            Self::new(1400)
        }
    }

    impl Recorder {
        fn new(max_payload_size: u16) -> Self {
            Self {
                payloads: Default::default(),
                congested: Default::default(),
                max_payload_size,
            }
        }

        fn take(&mut self) -> Vec<Recorded> {
            std::mem::take(&mut self.payloads)
        }
    }

    impl PayloadSink for Recorder {
        fn payload(&mut self, p: &Payload<'_>) {
            self.payloads.push((
                p.mark(),
                p.position().is_first(),
                HexDebug(p.data().concat()),
            ));
        }

        fn congested(&self) -> bool {
            self.congested
        }

        fn max_payload_size(&self) -> u16 {
            self.max_payload_size
        }
    }

    fn rec(mark: bool, frame_start: bool, data: &[u8]) -> Recorded {
        (mark, frame_start, HexDebug(data.to_vec()))
    }

    fn packetizer(parameter_set_insertion: ParameterSetInsertion) -> Packetizer {
        let [vps, sps, pps] = parameter_sets();
        let params = InternalParameters::parse_vps_sps_pps(&vps, &sps, &pps, false)
            .unwrap()
            .generic_parameters;
        Packetizer::new(
            &params,
            VideoPacketizerOptions::default().parameter_set_insertion(parameter_set_insertion),
        )
        .unwrap()
    }

    fn frame(ts: i64, is_random_access_point: bool) -> VideoFrameInfo {
        VideoFrameInfo::new(crate::Timestamp::new(ts, NonZeroU32::new(90_000).unwrap(), 0).unwrap())
            .with_random_access_point(is_random_access_point)
    }

    /// Parameter sets and small NALs are aggregated into an aggregation packet.
    #[test]
    fn aggregation() {
        let mut p = packetizer(ParameterSetInsertion::EachKeyFrame);
        let mut r = Recorder::default();
        p.start_frame(frame(0, true), &mut r);
        p.push_unit(Position::Complete, &[b"\x4e\x01sei"], &mut r);
        p.push_unit(Position::Complete, &[b"\x26\x01", b"idr"], &mut r);
        assert_eq!(r.take(), []); // held until the frame's end.
        p.end_frame(&mut r);
        let [vps, sps, pps] = parameter_sets();
        let mut expected = vec![0x60, 0x01]; // AP with layer 0, TID 0.
        for nal in [&vps[..], &sps, &pps, b"\x4e\x01sei", b"\x26\x01idr"] {
            expected.extend_from_slice(&(nal.len() as u16).to_be_bytes());
            expected.extend_from_slice(nal);
        }
        assert_eq!(r.take(), [rec(true, true, &expected)]);

        // No parameter sets for a non-key frame; a lone NAL goes in a single NAL unit packet.
        p.start_frame(frame(1, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x02\x01p"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, true, b"\x02\x01p")]);
    }

    /// After `flush`, `end_frame` delivers a filler NAL with the VCL NAL's
    /// layer ID and TID.
    #[test]
    fn flush() {
        let mut p = packetizer(ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x03\x0bp"], &mut r); // layer 33, TID plus 1 = 3
        p.flush(&mut r);
        assert_eq!(r.take(), [rec(false, true, b"\x03\x0bp")]);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, false, b"\x4d\x0b\x80")]);
    }

    /// The aggregation packet's header has the minimum layer ID and TID.
    #[test]
    fn aggregation_header() {
        let mut p = packetizer(ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x02\x0bp"], &mut r); // layer 1, TID plus 1 = 3
        p.push_unit(Position::Complete, &[b"\x03\x02q"], &mut r); // layer 32, TID plus 1 = 2
        p.end_frame(&mut r);
        assert_eq!(
            r.take(),
            [rec(
                true,
                true,
                b"\x60\x0a\x00\x03\x02\x0bp\x00\x03\x03\x02q"
            )]
        );
    }

    /// Fragments are delivered as soon as they're known not to be last,
    /// referencing the input; the final fragment is held for the marker bit.
    #[test]
    fn fu_streaming() {
        let mut p = packetizer(ParameterSetInsertion::Never);
        let mut r = Recorder::new(7);
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Start, &[b"\x02\x01abc"], &mut r);
        assert_eq!(r.take(), []); // might still fit in a single NAL unit packet.
        p.push_unit(Position::Middle, &[b"defghij"], &mut r);
        assert_eq!(
            r.take(),
            [
                rec(false, true, b"\x62\x01\x81abcd"),
                rec(false, false, b"\x62\x01\x01efgh")
            ]
        );
        p.push_unit(Position::End, &[b""], &mut r);
        assert_eq!(r.take(), []);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, false, b"\x62\x01\x41ij")]);
    }

    /// A NAL which exactly fits isn't fragmented; one byte more is.
    #[test]
    fn fu_boundary() {
        let mut p = packetizer(ParameterSetInsertion::Never);
        let mut r = Recorder::new(5);
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x02\x01abc"], &mut r);
        p.push_unit(Position::Complete, &[b"\x02\x01abcd"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(
            r.take(),
            [
                rec(false, true, b"\x02\x01abc"),
                rec(false, false, b"\x62\x01\x81ab"),
                rec(true, false, b"\x62\x01\x41cd"),
            ]
        );
    }

    /// The two-byte NAL header may be split across chunks.
    #[test]
    fn split_header() {
        let mut p = packetizer(ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x02", b"\x01p"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, true, b"\x02\x01p")]);
    }

    /// Invalid NALs are discarded by `push_unit`, including any continuation
    /// chunks: types which would be mistaken for aggregation or fragmentation
    /// packets, a zero TID, or a truncated header.
    #[test]
    fn invalid_nal() {
        let mut p = packetizer(ParameterSetInsertion::Never);
        let mut r = Recorder::new(100);
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x62\x01x"], &mut r); // type 49 (FU)
        p.push_unit(Position::Start, &[b"\x02\x00x"], &mut r); // TID 0
        p.push_unit(Position::End, &[b"yz"], &mut r);
        p.push_unit(Position::Complete, &[b"\x02"], &mut r);
        p.push_unit(Position::Complete, &[b"\x02\x01p"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, true, b"\x02\x01p")]);
    }

    /// `push_frame` rejects invalid NALs without delivering anything.
    #[test]
    fn push_frame_invalid_nal() {
        let mut p = packetizer(ParameterSetInsertion::Never);
        let mut r = Recorder::new(100);
        for (data, expected) in [
            (
                &b"\x00\x00\x00\x03\x02\x01p\x00\x00\x00\x03\x60\x01x"[..],
                "invalid type",
            ),
            (b"\x00\x00\x00\x03\x82\x01p", "F bit"),
            (b"\x00\x00\x00\x03\x02\x00p", "zero TemporalId"),
            (b"\x00\x00\x00\x01\x02", "shorter than a NAL header"),
        ] {
            let e = p
                .push_frame(
                    frame(0, false),
                    crate::codec::h26x::Framing::FourByteLength,
                    data,
                    &mut r,
                )
                .unwrap_err();
            assert!(e.to_string().contains(expected), "{e}");
            assert_eq!(r.take(), []);
        }
    }

    /// `push_frame` splits Annex B data and takes over in-band parameter sets.
    #[test]
    fn push_frame_annex_b() {
        let vps_b = b64("QAEMAf//AWAAAAMAkAAAAwAAAwA/LAwAAgAAAwAoAAIAAgACgA==");
        let sps_b = b64("QgEBAWAAAAMAkAAAAwAAAwA/oAUCAXFlLkkyS7I=");
        let pps_b = b64("RAHA8vAzJA==");
        let mut p = packetizer(ParameterSetInsertion::OnChange);
        let mut r = Recorder::default();
        let mut data = Vec::new();
        for nal in [&vps_b[..], &sps_b, &pps_b, b"\x26\x01idr"] {
            data.extend_from_slice(b"\x00\x00\x00\x01");
            data.extend_from_slice(nal);
        }
        p.push_frame(
            frame(0, true),
            crate::codec::h26x::Framing::AnnexB,
            &data,
            &mut r,
        )
        .unwrap();
        let mut expected = vec![0x60, 0x01];
        for nal in [&vps_b[..], &sps_b, &pps_b, b"\x26\x01idr"] {
            expected.extend_from_slice(&(nal.len() as u16).to_be_bytes());
            expected.extend_from_slice(nal);
        }
        assert_eq!(r.take(), [rec(true, true, &expected)]);
        assert_eq!(
            p.payload_format().fmtp().unwrap(),
            "sprop-vps=QAEMAf//AWAAAAMAkAAAAwAAAwA/LAwAAgAAAwAoAAIAAgACgA==;\
             sprop-sps=QgEBAWAAAAMAkAAAAwAAAwA/oAUCAXFlLkkyS7I=;sprop-pps=RAHA8vAzJA=="
        );

        // Repeated parameter sets aren't a change, so they aren't inserted.
        p.push_frame(
            frame(1, true),
            crate::codec::h26x::Framing::AnnexB,
            &data,
            &mut r,
        )
        .unwrap();
        assert_eq!(r.take(), [rec(true, true, b"\x26\x01idr")]);
    }

    /// As with H.264, in-band parameter sets supplied via `push_unit` are
    /// inserted after any access unit delimiter, which stays first.
    #[test]
    fn push_unit_in_band_parameter_sets() {
        let vps_b = b64("QAEMAf//AWAAAAMAkAAAAwAAAwA/LAwAAgAAAwAoAAIAAgACgA==");
        let sps_b = b64("QgEBAWAAAAMAkAAAAwAAAwA/oAUCAXFlLkkyS7I=");
        let pps_b = b64("RAHA8vAzJA==");
        let au = [&b"\x46\x01\x50"[..], &vps_b, &sps_b, &pps_b, b"\x26\x01idr"];
        let mut p = packetizer(ParameterSetInsertion::OnChange);
        let mut r = Recorder::default();
        p.start_frame(frame(0, true), &mut r);
        for nal in au {
            p.push_unit(Position::Complete, &[nal], &mut r);
        }
        p.end_frame(&mut r);
        let mut expected = vec![0x60, 0x01];
        for nal in au {
            expected.extend_from_slice(&(nal.len() as u16).to_be_bytes());
            expected.extend_from_slice(nal);
        }
        assert_eq!(r.take(), [rec(true, true, &expected)]);
        assert!(
            p.payload_format()
                .fmtp()
                .unwrap()
                .contains("sprop-pps=RAHA8vAzJA==")
        );
        assert_eq!(
            p.parameters().parameter_sets().collect::<Vec<_>>(),
            [&vps_b[..], &sps_b, &pps_b]
        );
    }

    /// As in the H.264 `throttle_fu_a`: congestion mid-fragment truncates the
    /// NAL, setting the F bit in the final fragment's payload header, and
    /// frames are then dropped until a random access point.
    #[test]
    fn throttle_fu() {
        let mut p = packetizer(ParameterSetInsertion::Never);
        let mut r = Recorder::new(7);
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Start, &[b"\x02\x01abc"], &mut r);
        p.push_unit(Position::Middle, &[b"defghij"], &mut r);
        assert_eq!(
            r.take(),
            [
                rec(false, true, b"\x62\x01\x81abcd"),
                rec(false, false, b"\x62\x01\x01efgh")
            ]
        );
        r.congested = true;
        p.push_unit(Position::Middle, &[b"klmn"], &mut r);
        p.push_unit(Position::End, &[b"op"], &mut r);
        p.push_unit(Position::Complete, &[b"\x02\x01q"], &mut r);
        assert_eq!(r.take(), []);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, false, b"\xe2\x01\x41ijkl")]);

        // Uncongested, but awaiting a random access point.
        r.congested = false;
        p.start_frame(frame(1, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x02\x01r"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), []);
        p.start_frame(frame(2, true), &mut r);
        p.push_unit(Position::Complete, &[b"\x26\x01s"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, true, b"\x26\x01s")]);
    }

    /// Congestion at a NAL boundary truncates the next NAL to its header.
    #[test]
    fn throttle_nal_boundary() {
        let mut p = packetizer(ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x02\x01a"], &mut r);
        r.congested = true;
        p.push_unit(Position::Start, &[b"\x02\x01b"], &mut r);
        p.push_unit(Position::End, &[b"c"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(
            r.take(),
            [
                rec(false, true, b"\x02\x01a"),
                rec(true, false, b"\x82\x01")
            ]
        );
    }
}
