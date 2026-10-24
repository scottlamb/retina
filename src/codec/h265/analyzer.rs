// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Transport-independent analysis of H.265 access units.

use std::fmt::Write as _;

use bytes::Bytes;
use log::{debug, log_enabled, trace};

use super::{AuData, FrameEndBody, InternalParameters, Nal, nal};
use crate::buf::{BufRange, Mark, MarkBuf};
use crate::codec::h26x::{Delivery, Framing, NalAnalyzer, check_range};
use crate::codec::{
    Accumulate, FrameBody, FrameEnd, FrameStart, Handler, Loss, LossReason, ParametersRef,
    VideoParameters,
};

/// Analyzes H.265 access units (frames), regardless of how they're transported.
///
/// This is the codec layer beneath the H.265 RTP depacketizer. Its interface
/// is [`NalAnalyzer`]; see there for an overview.
///
/// It currently never reports a frame as disposable.
#[derive(Debug)]
pub struct Analyzer<Ctx> {
    parameters: Option<InternalParameters>,

    /// The framing of the parameters' `extra_data`.
    framing: Framing,

    /// Parameter sets which differ from `parameters`, to take effect at the
    /// next access unit's first slice. These followed the first slice of an
    /// earlier access unit, or were in an access unit without slices.
    /// They're consumed when an access unit with a slice finishes, and
    /// survive losses before then.
    pending: Option<Box<NewParams>>,

    /// Mark pinning buffer data for the current access unit's pieces.
    /// Set when the first piece is added; cleared when the access unit ends
    /// or [`Analyzer::stream_with`] releases its data.
    mark: Option<Mark>,

    /// Byte ranges of the current access unit's NAL bodies (excluding header
    /// bytes). Kept around (empty) between access units to re-use the
    /// backing allocation.
    pieces: Vec<BufRange>,

    /// An entry for each of the current access unit's complete NALs.
    /// Kept around (empty) between access units to re-use the backing allocation.
    nals: Vec<Nal>,

    /// The current access unit, if any.
    au: Option<AuState<Ctx>>,

    /// Packets lost since the last access unit started.
    lost: u16,

    /// The timestamp of the previous access unit, if any, for logging.
    prev_timestamp: Option<crate::Timestamp>,
}

#[derive(Debug)]
struct AuState<Ctx> {
    timestamp: crate::Timestamp,

    /// The context of the access unit's first input unit (such as a packet).
    start_ctx: Ctx,

    /// Packets lost as this access unit was starting. If non-zero, it may be
    /// missing its beginning.
    loss: u16,

    /// True if this access unit has the same timestamp as the previous one,
    /// which is noted when logging bad access units.
    same_ts_as_prev: bool,

    /// The NAL unit in progress, if any.
    in_progress: Option<InProgressNal>,

    /// Metadata from the NALs scanned so far.
    meta: FrameMeta,

    /// The number of `Analyzer::nals` reflected in `meta`.
    scanned_nals: u32,

    /// Set once `frame_start` has been called.
    started: Option<Accumulate>,

    delivery: Delivery,

    /// True if `Analyzer::nals` and `Analyzer::pieces` have been trimmed
    /// mid-access unit, so they no longer describe all of it.
    /// Only happens under `Accumulate::No`.
    trimmed: bool,
}

/// Tracks the NAL unit in progress, between `start_nal` and `finish_nal`.
#[derive(Debug)]
struct InProgressNal {
    hdr: nal::Header,

    /// The length so far, including the header bytes.
    len: u32,
}

/// Metadata about an access unit, gathered as its NALs are scanned.
#[derive(Debug)]
struct FrameMeta {
    /// True unless a non-IRAP VCL NAL has been seen.
    is_random_access_point: bool,

    /// True if a VCL NAL has been seen.
    seen_vcl: bool,

    /// Parameter sets for this frame which differ from
    /// `Analyzer::parameters`, if any: `Analyzer::pending`, updated by the
    /// sets preceding the first slice. Boxed because they're rare.
    new_params: Option<Box<NewParams>>,

    /// Parameter sets following the first slice which differ from those in
    /// `new_params` or `Analyzer::parameters`, if any. These are for later
    /// frames; see `AuView::scan_meta`.
    deferred: Option<Box<NewParams>>,

    /// The header of the last complete NAL, for `can_end_au`.
    last_nal_hdr: Option<nal::Header>,
}

impl Default for FrameMeta {
    fn default() -> Self {
        FrameMeta {
            is_random_access_point: true,
            seen_vcl: false,
            new_params: None,
            deferred: None,
            last_nal_hdr: None,
        }
    }
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

/// The kinds of parameter sets Retina tracks.
#[derive(Copy, Clone, Debug)]
enum ParameterSetKind {
    Vps,
    Sps,
    Pps,
}

impl ParameterSetKind {
    fn of(hdr: nal::Header) -> Option<Self> {
        match hdr.unit_type() {
            nal::UnitType::VpsNut => Some(Self::Vps),
            nal::UnitType::SpsNut => Some(Self::Sps),
            nal::UnitType::PpsNut => Some(Self::Pps),
            _ => None,
        }
    }

    /// Returns the set of this kind as last received in-band.
    fn in_band(self, p: &InternalParameters) -> &[u8] {
        match self {
            Self::Vps => &p.vps_nal,
            Self::Sps => &p.sps_nal,
            Self::Pps => &p.pps_nal,
        }
    }
}

impl NewParams {
    fn get(&self, kind: ParameterSetKind) -> Option<&Bytes> {
        match kind {
            ParameterSetKind::Vps => self.vps.as_ref(),
            ParameterSetKind::Sps => self.sps.as_ref(),
            ParameterSetKind::Pps => self.pps.as_ref(),
        }
    }

    fn get_mut(&mut self, kind: ParameterSetKind) -> &mut Option<Bytes> {
        match kind {
            ParameterSetKind::Vps => &mut self.vps,
            ParameterSetKind::Sps => &mut self.sps,
            ParameterSetKind::Pps => &mut self.pps,
        }
    }

    /// Returns a copy of the parameter sets, without parsed parameters.
    fn sets(&self) -> Box<Self> {
        Box::new(NewParams {
            vps: self.vps.clone(),
            sps: self.sps.clone(),
            pps: self.pps.clone(),
            parsed: None,
        })
    }

    /// Records a parameter set of the given kind in `slot`, which holds
    /// changes relative to `base`, the set of that kind in effect before them.
    ///
    /// `matches` compares the parameter set to stored bytes; `copy` copies it.
    /// A repeat of the latest set of this kind changes nothing, and a repeat
    /// of `base` undoes a change.
    fn note(
        slot: &mut Option<Box<Self>>,
        kind: ParameterSetKind,
        base: Option<&[u8]>,
        matches: impl Fn(&[u8]) -> bool,
        copy: impl FnOnce() -> Bytes,
    ) {
        let latest = slot.as_ref().and_then(|np| np.get(kind)).map(|b| &b[..]);
        if latest.or(base).is_some_and(&matches) {
            return;
        }
        if latest.is_some() && base.is_some_and(&matches) {
            let np = slot.as_mut().expect("latest is from slot");
            *np.get_mut(kind) = None;
            np.parsed = None;
            if np.vps.is_none() && np.sps.is_none() && np.pps.is_none() {
                *slot = None;
            }
            return;
        }
        let np = slot.get_or_insert_default();
        *np.get_mut(kind) = Some(copy());
        np.parsed = None;
    }
}

fn is_vcl(hdr: nal::Header) -> bool {
    matches!(
        hdr.unit_type().unit_type_class(),
        nal::UnitTypeClass::Vcl { .. }
    )
}

impl<Ctx: Clone> Analyzer<Ctx> {
    /// Creates an analyzer which has no parameters until they arrive in-band.
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self::with_internal_parameters(None)
    }
}

impl<Ctx: Clone> NalAnalyzer<Ctx> for Analyzer<Ctx> {
    fn parameters(&self) -> Option<&VideoParameters> {
        self.parameters.as_ref().map(|p| &p.generic_parameters)
    }

    fn start_au(&mut self, timestamp: crate::Timestamp, ctx: Ctx) {
        assert!(self.au.is_none(), "access unit already in progress");
        debug_assert!(self.nals.is_empty() && self.pieces.is_empty() && self.mark.is_none());
        self.au = Some(AuState {
            timestamp,
            start_ctx: ctx,
            loss: std::mem::take(&mut self.lost),
            same_ts_as_prev: self
                .prev_timestamp
                .is_some_and(|p| p.timestamp == timestamp.timestamp),
            in_progress: None,
            meta: FrameMeta {
                new_params: self.pending.as_deref().map(NewParams::sets),
                ..FrameMeta::default()
            },
            scanned_nals: 0,
            started: None,
            delivery: Delivery::default(),
            trimmed: false,
        });
    }

    fn push_nal(&mut self, buf: &MarkBuf, pos: u64, len: usize) -> Result<(), String> {
        check_range(buf, pos, len);
        if len < 2 {
            return Err("NAL unit shorter than its header".into());
        }
        let mut hdr = [0u8; 2];
        let (s1, s2) = buf.split(pos, 2).slices();
        hdr[..s1.len()].copy_from_slice(s1);
        hdr[s1.len()..].copy_from_slice(s2);
        self.start_nal(&hdr, buf, pos + 2, len - 2)?;
        self.finish_nal()
    }

    fn start_nal(
        &mut self,
        header: &[u8],
        buf: &MarkBuf,
        body_pos: u64,
        body_len: usize,
    ) -> Result<(), String> {
        let au = self.au.as_mut().expect("start_nal without start_au");
        assert!(
            au.in_progress.is_none(),
            "start_nal while a NAL unit is in progress"
        );
        check_range(buf, body_pos, body_len);
        let Ok(&hdr) = <&[u8; 2]>::try_from(header) else {
            return Err(format!(
                "expected a 2-byte NAL header; got {} bytes",
                header.len()
            ));
        };
        let hdr = nal::Header::try_from(hdr).map_err(|e| e.0)?;
        au.in_progress = Some(InProgressNal { hdr, len: 2 });
        self.add_piece(buf, body_pos, body_len)
    }

    fn extend_nal(&mut self, buf: &MarkBuf, pos: u64, len: usize) -> Result<(), String> {
        assert!(self.has_nal(), "extend_nal without start_nal");
        check_range(buf, pos, len);
        self.add_piece(buf, pos, len)
    }

    fn finish_nal(&mut self) -> Result<(), String> {
        let ip = self
            .au
            .as_mut()
            .and_then(|au| au.in_progress.take())
            .expect("finish_nal without start_nal");
        self.nals.push(Nal {
            hdr: ip.hdr,
            next_piece_idx: u32::try_from(self.pieces.len()).expect("piece count fits in u32"),
            len: ip.len,
        });
        Ok(())
    }
}

/// The crate-internal interface, for the RTP depacketizer.
impl<Ctx: Clone> Analyzer<Ctx> {
    /// Starts the frame if possible and delivers its data so far.
    ///
    /// This is optional; [`Analyzer::finish_au_with`] does the same. Calling
    /// it after each NAL unit or fragment delivers events with lower latency,
    /// and with [`Accumulate::No`] releases the buffer data supplied so far.
    pub(crate) fn stream_with<H: Handler<Ctx>>(&mut self, buf: &MarkBuf, handler: &mut H) {
        if self.au.is_none() {
            return;
        }
        self.stream_inner(buf, handler);
    }

    /// Finishes the current access unit, delivering any remaining events to
    /// `handler`.
    ///
    /// `end_ctx` will be supplied as [`FrameEnd::end_ctx`]. If the access
    /// unit is invalid (for example, it has an invalid parameter set, or a NAL
    /// unit is still in progress), discards it and returns an error instead
    /// of finishing the frame. An access unit without slices produces no
    /// events.
    ///
    /// # Panics
    ///
    /// Panics if no access unit is in progress.
    pub(crate) fn finish_au_with<H: Handler<Ctx>>(
        &mut self,
        buf: &MarkBuf,
        end_ctx: &Ctx,
        handler: &mut H,
    ) -> Result<(), String> {
        let mut au = self.au.take().expect("finish_au without start_au");
        self.prev_timestamp = Some(au.timestamp);
        let r = if au.in_progress.is_some() {
            Err("access unit ended in the middle of a NAL unit".to_owned())
        } else {
            self.finalize(&mut au, end_ctx, buf, handler)
        };
        self.discard_au();
        r
    }

    /// Sets the framing of the parameters' `extra_data`.
    ///
    /// If existing parameters were parsed with a different framing, they are
    /// re-parsed to produce the correct `extra_data` format.
    pub(crate) fn set_framing(&mut self, framing: Framing) {
        self.framing = framing;

        // Re-parse existing parameters so extra_data matches the new framing.
        if let Some(ref ip) = self.parameters {
            self.parameters = Some(
                InternalParameters::parse_vps_sps_pps(
                    &ip.vps_nal,
                    &ip.sps_nal,
                    &ip.pps_nal,
                    ip.seen_extra_trailing_data,
                    framing,
                )
                .expect("re-parse of previously valid VPS/SPS/PPS should not fail"),
            );
        }
    }

    /// Changes the current access unit's timestamp, if any, affecting only
    /// events not yet delivered. For senders which erroneously change
    /// timestamps mid-access unit.
    pub(crate) fn set_au_timestamp(&mut self, timestamp: crate::Timestamp) {
        if let Some(au) = self.au.as_mut() {
            au.timestamp = timestamp;
        }
    }

    pub(super) fn with_internal_parameters(parameters: Option<InternalParameters>) -> Self {
        Analyzer {
            parameters,
            framing: Framing::default(),
            pending: None,
            mark: None,
            pieces: Vec::new(),
            nals: Vec::new(),
            au: None,
            lost: 0,
            prev_timestamp: None,
        }
    }

    /// Reports lost or unusable input, such as
    /// [`LossReason::PacketLoss`].
    ///
    /// Discards any in-progress access unit. Lost packets are counted toward
    /// the next one, which may be missing its beginning.
    pub(crate) fn loss<H: Handler<Ctx>>(&mut self, ctx: &Ctx, reason: LossReason, handler: &mut H) {
        if let LossReason::PacketLoss { packets } = reason {
            self.lost = self.lost.saturating_add(packets);
        }
        self.loss_without_report();
        handler.loss(&Loss { ctx, reason });
    }

    /// Discards the access unit in progress, without reporting it, after loss
    /// or an error the caller reports.
    pub(crate) fn discard_lossy_au(&mut self) {
        self.loss_without_report();
    }

    /// Returns the current access unit's timestamp, if any.
    pub(crate) fn au_timestamp(&self) -> Option<crate::Timestamp> {
        self.au.as_ref().map(|au| au.timestamp)
    }

    /// Returns true if buffer data is pinned.
    #[cfg(test)]
    pub(crate) fn has_mark(&self) -> bool {
        self.mark.is_some()
    }

    /// Returns true if no access unit data is held.
    pub(crate) fn is_idle(&self) -> bool {
        self.au.is_none() && self.nals.is_empty() && self.pieces.is_empty() && self.mark.is_none()
    }

    /// Returns the header of the last complete NAL in the access unit, if any.
    ///
    /// Transports pass this to [`super::can_end_au`] to decide if an apparent
    /// access unit boundary is plausible.
    pub(crate) fn last_nal_hdr(&self) -> Option<nal::Header> {
        self.nals
            .last()
            .map(|n| n.hdr)
            .or_else(|| self.au.as_ref()?.meta.last_nal_hdr)
    }
}

/// Implementation details.
impl<Ctx: Clone> Analyzer<Ctx> {
    /// Returns true if a NAL unit is in progress, between
    /// [`Analyzer::start_nal`] and [`Analyzer::finish_nal`].
    fn has_nal(&self) -> bool {
        self.au.as_ref().is_some_and(|au| au.in_progress.is_some())
    }

    /// Adds `[pos, pos + len)` to the NAL unit in progress, pinning it.
    fn add_piece(&mut self, buf: &MarkBuf, pos: u64, len: usize) -> Result<(), String> {
        if len == 0 {
            return Ok(());
        }
        let ip = self
            .au
            .as_mut()
            .and_then(|au| au.in_progress.as_mut())
            .expect("NAL unit in progress");
        let piece_len = u32::try_from(len).map_err(|_| "excessively long NAL")?;
        ip.len = ip
            .len
            .checked_add(piece_len)
            .ok_or("excessively long NAL")?;
        crate::codec::h26x::pin(&mut self.mark, buf, pos);
        self.pieces.push(BufRange {
            pos,
            len: piece_len,
        });
        Ok(())
    }

    /// Abandons the in-progress access unit, if any, without reporting it.
    fn discard_au(&mut self) {
        self.nals.clear();
        self.pieces.clear();
        self.mark = None;
        self.au = None;
    }

    /// Discards any access unit in progress.
    fn loss_without_report(&mut self) {
        if let Some(au) = self.au.as_ref() {
            self.prev_timestamp = Some(au.timestamp);
        }
        self.discard_au();
    }

    /// Starts the frame if possible and delivers its data so far.
    fn stream_inner(&mut self, buf: &MarkBuf, handler: &mut impl Handler<Ctx>) {
        let Some(au) = self.au.as_mut() else {
            return;
        };
        let view = AuView {
            framing: self.framing,
            parameters: &self.parameters,
            nals: &self.nals,
            pieces: &self.pieces,
        };
        view.scan_meta(au, buf);
        let in_progress = au.in_progress.as_ref().map(|ip| ip.hdr);
        if au.started.is_none() && (au.meta.seen_vcl || in_progress.is_some_and(is_vcl)) {
            view.start_frame(au, handler);
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

    /// Delivers the remaining events for a complete access unit.
    ///
    /// The caller must then discard the access unit's data.
    fn finalize(
        &mut self,
        au: &mut AuState<Ctx>,
        end_ctx: &Ctx,
        buf: &MarkBuf,
        handler: &mut impl Handler<Ctx>,
    ) -> Result<(), String> {
        if !au.trimmed && log_enabled!(log::Level::Debug) {
            log_access_unit(&self.nals, au);
        }
        let view = AuView {
            framing: self.framing,
            parameters: &self.parameters,
            nals: &self.nals,
            pieces: &self.pieces,
        };
        view.scan_meta(au, buf);
        if au.started.is_none() && !au.meta.seen_vcl {
            // No frame_start, so no frame_end is owed. The parameter sets
            // (`pending`, updated by this access unit's) take effect at the
            // next slice.
            self.pending = au.meta.new_params.take().map(|np| np.sets());
            return Ok(());
        }

        // This frame consumes `pending` (via `new_params`), even if its
        // parameters turn out to be invalid. Sets after its first slice
        // await the next.
        self.pending = au.meta.deferred.take();

        // Commit new parameters before building the frame, so prepended
        // params reflect the latest VPS/SPS/PPS.
        let new_params = match au.meta.new_params.take() {
            None => None,
            Some(mut np) => match np.parsed.take() {
                Some(p) => Some(p),
                None => view.parse_new_params(&np)?,
            },
        };
        let has_new_parameters = new_params.is_some();
        if new_params.is_some() {
            self.parameters = new_params;
        }

        let accumulate = match au.started {
            Some(a) => a,
            None => handler.frame_start(&FrameStart {
                timestamp: au.timestamp,
                ctx: &au.start_ctx,
                loss: au.loss,
                is_random_access_point: au.meta.is_random_access_point,
                is_disposable: false,
                has_new_parameters,
                parameters: self
                    .parameters
                    .as_ref()
                    .map(|p| ParametersRef::Video(&p.generic_parameters)),
            }),
        };
        au.delivery
            .deliver(&self.nals, &self.pieces, None, buf, handler);

        handler.frame_end(&mut FrameEnd {
            timestamp: au.timestamp,
            start_ctx: &au.start_ctx,
            end_ctx,
            loss: au.loss,
            is_random_access_point: au.meta.is_random_access_point,
            is_disposable: false,
            has_new_parameters,
            body: FrameBody::H265(FrameEndBody {
                au: (accumulate == Accumulate::Yes && !au.trimmed).then_some(AuData {
                    nals: &self.nals,
                    pieces: &self.pieces,
                    buf,
                }),
                parameters: self.parameters.as_ref(),
                is_random_access_point: au.meta.is_random_access_point,
                has_new_parameters,
            }),
        });
        Ok(())
    }
}

/// The analyzer's state other than the current access unit, borrowed
/// separately from it.
struct AuView<'a> {
    framing: Framing,
    parameters: &'a Option<InternalParameters>,
    nals: &'a [Nal],
    pieces: &'a [BufRange],
}

impl AuView<'_> {
    /// Updates `au.meta` to reflect NALs completed since the last call.
    fn scan_meta<Ctx>(&self, au: &mut AuState<Ctx>, buf: &MarkBuf) {
        let scanned_nals = crate::to_usize(au.scanned_nals);
        let mut piece_idx = match scanned_nals {
            0 => 0,
            i => crate::to_usize(self.nals[i - 1].next_piece_idx),
        };
        let meta = &mut au.meta;
        for nal in &self.nals[scanned_nals..] {
            let next_piece_idx = crate::to_usize(nal.next_piece_idx);
            let nal_pieces = &self.pieces[piece_idx..next_piece_idx];
            if let Some(kind) = ParameterSetKind::of(nal.hdr) {
                let in_band = self.parameters.as_ref().map(|p| kind.in_band(p));
                let matches = |b: &[u8]| nal_matches(b, nal.hdr, nal_pieces, buf);
                let copy = || to_bytes(nal.hdr, nal.len, nal_pieces, buf);
                if meta.seen_vcl {
                    // A parameter set after the first slice is for a later
                    // picture. Either it's a repeat, or it has a different id
                    // than the active set and will be referred to later
                    // (H.265 sections cited):
                    // * a picture's slice segments all refer to the same PPS
                    //   id (section 7.4.7.1).
                    // * the active PPS's content can change only between
                    //   pictures, and the active VPS's and SPS's only between
                    //   coded video sequences (section 7.4.2.4.2).
                    let base = meta
                        .new_params
                        .as_ref()
                        .and_then(|np| np.get(kind))
                        .map(|b| &b[..])
                        .or(in_band);
                    NewParams::note(&mut meta.deferred, kind, base, matches, copy);
                } else {
                    NewParams::note(&mut meta.new_params, kind, in_band, matches, copy);
                }
            }
            match nal.hdr.unit_type().unit_type_class() {
                nal::UnitTypeClass::Vcl { irap } => {
                    meta.seen_vcl = true;
                    if !irap {
                        meta.is_random_access_point = false;
                    }
                }
                nal::UnitTypeClass::NonVcl => {}
            }
            meta.last_nal_hdr = Some(nal.hdr);
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
        InternalParameters::parse_vps_sps_pps(
            vps_nal,
            sps_nal,
            pps_nal,
            seen_extra_trailing_data,
            self.framing,
        )
        .map(Some)
    }

    /// Calls `frame_start` for a frame which is still in progress.
    ///
    /// The frame's metadata so far is provisional. In particular, parameters
    /// are parsed but not committed to `parameters` until the frame ends.
    fn start_frame<Ctx>(&self, au: &mut AuState<Ctx>, handler: &mut impl Handler<Ctx>) {
        let mut is_random_access_point = au.meta.is_random_access_point;
        if let Some(ip) = au.in_progress.as_ref()
            && matches!(
                ip.hdr.unit_type().unit_type_class(),
                nal::UnitTypeClass::Vcl { irap: false }
            )
        {
            is_random_access_point = false;
        }
        if let Some(np) = au.meta.new_params.as_mut()
            && np.parsed.is_none()
        {
            // On error, leave `parsed` empty; `finalize` will try again and
            // report the error.
            np.parsed = self.parse_new_params(np).ok().flatten();
        }
        let new_params = au
            .meta
            .new_params
            .as_ref()
            .and_then(|np| np.parsed.as_ref());
        au.started = Some(
            handler.frame_start(&FrameStart {
                timestamp: au.timestamp,
                ctx: &au.start_ctx,
                loss: au.loss,
                is_random_access_point,
                is_disposable: false,
                has_new_parameters: new_params.is_some(),
                parameters: new_params
                    .or(self.parameters.as_ref())
                    .map(|p| ParametersRef::Video(&p.generic_parameters)),
            }),
        );
    }
}

/// Logs information about each access unit.
/// Currently, "bad" access units (violating certain specification rules)
/// are logged at debug priority, and others are logged at trace priority.
fn log_access_unit<Ctx>(nals: &[Nal], au: &AuState<Ctx>) {
    let mut errs = String::new();
    if au.same_ts_as_prev {
        errs.push_str("\n* same timestamp as previous access unit");
    }
    validate_order(nals, &mut errs);
    if !errs.is_empty() {
        let mut nals_str = String::new();
        for (i, nal) in nals.iter().enumerate() {
            let _ = write!(&mut nals_str, "\n  {}: {:?}", i, nal.hdr);
        }
        debug!(
            "bad access unit at ts {}\nerrors are:{}\nNALs are:{}",
            au.timestamp, errs, nals_str
        );
    } else if log_enabled!(log::Level::Trace) {
        let mut nals_str = String::new();
        for (i, nal) in nals.iter().enumerate() {
            let _ = write!(&mut nals_str, "\n  {}: {:?}", i, nal.hdr);
        }
        trace!("access unit at ts {}; NALS are:{}", au.timestamp, nals_str);
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

/// Returns true iff the bytes of `nal` equal the bytes of `[hdr, ..data]`.
fn nal_matches(nal: &[u8], hdr: nal::Header, pieces: &[BufRange], buf: &MarkBuf) -> bool {
    if nal.first_chunk() != Some(&*hdr) {
        return false;
    }
    let mut nal_pos = 2;
    for piece in pieces {
        let new_pos = nal_pos + crate::to_usize(piece.len);
        if nal.len() < new_pos {
            return false;
        }
        let (s1, s2) = buf.split(piece.pos, crate::to_usize(piece.len)).slices();
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
        let (s1, s2) = buf.split(piece.pos, crate::to_usize(piece.len)).slices();
        out.extend_from_slice(s1);
        out.extend_from_slice(s2);
    }
    debug_assert_eq!(len, out.len());
    out.into()
}

#[cfg(test)]
mod tests {
    use super::Analyzer;
    use crate::buf::MarkBuf;
    use crate::codec::h26x::NalAnalyzer as _;
    use crate::codec::{Accumulate, FrameEnd, FrameStart, Handler, Loss};

    /// An event delivered to [`Events`].
    #[derive(Debug, PartialEq, Eq)]
    enum Event {
        Start,
        Data {
            first: bool,
            last: bool,
            bytes: Vec<u8>,
        },
        End,
        Loss,
    }

    /// Records every event, streaming (with [`Accumulate::No`]).
    #[derive(Default)]
    struct Events(Vec<Event>);

    impl Handler<u32> for Events {
        fn frame_start(&mut self, _: &FrameStart<'_, u32>) -> Accumulate {
            self.0.push(Event::Start);
            Accumulate::No
        }

        fn data(&mut self, data: &crate::codec::Data<'_>) {
            self.0.push(Event::Data {
                first: data.position.is_first(),
                last: data.position.is_last(),
                bytes: data.data.concat(),
            });
        }

        fn frame_end(&mut self, _: &mut FrameEnd<'_, u32>) {
            self.0.push(Event::End);
        }

        fn loss(&mut self, _: &Loss<'_, u32>) {
            self.0.push(Event::Loss);
        }
    }

    /// Appends `data` to `buf` as a transport would, returning its position.
    fn append_data(buf: &mut MarkBuf, data: &[u8]) -> u64 {
        let pos = buf.end();
        buf.extend(data);
        buf.advance_unparsed(buf.end());
        pos
    }

    fn ts() -> crate::Timestamp {
        crate::Timestamp::new(0, std::num::NonZeroU32::new(90_000).unwrap(), 0).unwrap()
    }

    /// Checks that `events` are a NAL unit's data, split into several
    /// chunks, with only the first marked first and the last marked last.
    fn assert_chunks(events: &[Event], nal: &[u8]) {
        assert!(
            events.len() > 1,
            "expected several chunks; got {}",
            events.len()
        );
        let mut bytes = Vec::new();
        for (i, e) in events.iter().enumerate() {
            let Event::Data {
                first,
                last,
                bytes: b,
            } = e
            else {
                panic!("unexpected event {e:?}");
            };
            assert_eq!(*first, i == 0);
            assert_eq!(*last, i == events.len() - 1);
            bytes.extend_from_slice(b);
        }
        assert!(bytes == nal, "chunks don't reassemble the NAL unit");
    }

    /// Shows how data is delivered: nothing on `start_nal`/`extend_nal`/
    /// `push_nal` alone; each [`Analyzer::stream_with`] call delivers what's new,
    /// including part of a NAL unit still in progress.
    #[test]
    fn streams_nal_fragments() {
        let mut buf = MarkBuf::new(64);
        let mut a = Analyzer::new();
        let mut e = Events::default();
        a.start_au(ts(), 0);
        for p in {
            use base64::Engine as _;
            let b64 = |s| base64::engine::general_purpose::STANDARD.decode(s).unwrap();
            [
                b64("QAEMAf//AWAAAAMAkAAAAwAAAwA/LAwAAgAAAwAoAAIAAgACgA=="),
                b64("QgEBAWAAAAMAkAAAAwAAAwA/oAUCAXFlLkkyS7I="),
                b64("RAHA8vAzJA=="),
            ]
        } {
            let pos = append_data(&mut buf, &p);
            a.push_nal(&buf, pos, p.len()).unwrap();
        }
        a.stream_with(&buf, &mut e);
        assert_eq!(e.0, [], "parameter sets alone don't start a frame");

        // An IDR slice, arriving in three fragments.
        const IDR: &[u8] = b"\x26\x01\x80idr slice data";
        let (f1, rest) = IDR.split_at(2 + 3);
        let (f2, f3) = rest.split_at(4);
        let (hdr, f1_body) = f1.split_at(2);
        a.start_nal(hdr, &buf, buf.end(), 0).unwrap();
        assert_eq!(e.0, [], "start_nal alone delivers nothing");
        a.stream_with(&buf, &mut e);
        let data = |first, last, bytes: &[u8]| Event::Data {
            first,
            last,
            bytes: bytes.to_vec(),
        };
        assert_eq!(e.0, [Event::Start, data(true, false, hdr)]);
        e.0.clear();
        let pos = append_data(&mut buf, f1_body);
        a.extend_nal(&buf, pos, f1_body.len()).unwrap();
        a.stream_with(&buf, &mut e);
        assert_eq!(e.0, [data(false, false, f1_body)]);
        assert!(
            !a.has_mark(),
            "delivered data is released under Accumulate::No"
        );
        e.0.clear();

        let pos = append_data(&mut buf, f2);
        a.extend_nal(&buf, pos, f2.len()).unwrap();
        a.stream_with(&buf, &mut e);
        assert_eq!(e.0, [data(false, false, f2)]);
        e.0.clear();

        let pos = append_data(&mut buf, f3);
        a.extend_nal(&buf, pos, f3.len()).unwrap();
        a.finish_nal().unwrap();
        assert_eq!(e.0, []);
        a.stream_with(&buf, &mut e);
        assert_eq!(e.0, [data(false, true, f3)]);
        e.0.clear();
        a.finish_au_with(&buf, &0, &mut e).unwrap();
        assert_eq!(e.0, [Event::End]);
        e.0.clear();

        // A large slice via `push_nal` is delivered in one chunk.
        let mut big = b"\x02\x01\x80".to_vec();
        big.extend((0..600_000).map(|i| (i % 251) as u8 | 1));
        a.start_au(ts(), 1);
        let pos = append_data(&mut buf, &big);
        a.push_nal(&buf, pos, big.len()).unwrap();
        assert_eq!(e.0, [], "push_nal alone delivers nothing");
        a.stream_with(&buf, &mut e);
        assert_eq!(e.0[0], Event::Start);
        assert_eq!(e.0[1..], [data(true, true, &big)]);
        e.0.clear();
        a.finish_au_with(&buf, &1, &mut e).unwrap();
        assert_eq!(e.0, [Event::End]);
        e.0.clear();

        // Many fragments delivered by one `stream` call are batched into
        // several chunks.
        a.start_au(ts(), 2);
        let (first, rest) = big.split_at(1000);
        let (hdr, body) = first.split_at(2);
        let pos = append_data(&mut buf, body);
        a.start_nal(hdr, &buf, pos, body.len()).unwrap();
        for frag in rest.chunks(rest.len() / 20 + 1) {
            let pos = append_data(&mut buf, frag);
            a.extend_nal(&buf, pos, frag.len()).unwrap();
        }
        a.finish_nal().unwrap();
        a.stream_with(&buf, &mut e);
        assert_eq!(e.0[0], Event::Start);
        assert_chunks(&e.0[1..], &big);
        e.0.clear();
        a.finish_au_with(&buf, &2, &mut e).unwrap();
        assert_eq!(e.0, [Event::End]);
        e.0.clear();

        // Ending an access unit mid-NAL is an error.
        a.start_au(ts(), 3);
        let pos = append_data(&mut buf, &big[2..10]);
        a.start_nal(&big[..2], &buf, pos, 10 - 2).unwrap();
        a.finish_au_with(&buf, &3, &mut e).unwrap_err();
        assert_eq!(e.0, []);
        assert!(a.is_idle());
    }
}
