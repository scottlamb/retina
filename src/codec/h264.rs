// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [H.264](https://www.itu.int/rec/T-REC-H.264-201906-I/en)-encoded video,
//! with RTP encoding as in [RFC 6184](https://tools.ietf.org/html/rfc6184).

use std::convert::TryFrom;
use std::fmt::Write;

use base64::Engine as _;
use bytes::{BufMut, Bytes, BytesMut};
use h264_reader::nal::sps::{SeqParameterSet, SpsError};
use h264_reader::nal::{NalHeader, UnitType};
use log::{debug, log_enabled, trace};

use crate::Error;
use crate::buf::{BufRange, Mark, MarkBuf};
use crate::codec::h26x::TolerantBitReader;
use crate::codec::{
    Accumulate, AllPixelDimensions, FrameBody, Loss, LossReason, VideoFrameEnd, VideoFrameStart,
    VideoHandler,
};
use crate::inputs::Input as _;
use crate::rtp::ReceivedPacketRef;

use super::VideoParameters;

/// Produce [`VideoParameters`] from SPS and PPS NAL units.
///
/// It's sometimes useful to "fix" a server's parameters, e.g.:
///
/// * adding missing pixel aspect ratio information to the SPS VUI so that
///   anamorphic video is displayed at the correct aspect ratio.
/// * adding missing bitstream restrictions such as `num_reorder_frames = 0`
///   that significantly reduce decode latency.
/// * removing garbage after the RBSP trailing bits.
///
/// Retina currently does not support directly making these changes itself, but
/// callers can use e.g. [`h264_reader`](https://crates.io/crates/h264_reader)
/// to rewrite the SPS, then use Retina's logic to repackage the parameters into
/// a [`VideoParameters`].
pub fn parameters_from_sps_and_pps(
    sps_nal: &[u8],
    pps_nal: &[u8],
) -> Result<VideoParameters, Error> {
    InternalParameters::parse_sps_and_pps(sps_nal, pps_nal, true)
        .map(|int| int.generic_parameters)
        .map_err(|s| wrap!(crate::error::ErrorInt::InvalidArgument(s)))
}

/// A [super::Depacketizer] implementation which finds access unit boundaries
/// and produces unfragmented NAL units as specified in [RFC
/// 6184](https://tools.ietf.org/html/rfc6184).
///
/// This inspects the contents of the NAL units only minimally, and largely for
/// logging. In particular, it doesn't completely enforce/verify compliance with
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
/// Annex B byte streams also allow additional `00` bytes before and after a
/// NAL unit, referred to as `zero_byte` and `trailing_zero_8bits`
/// respectively; this code discards those. Notably, H.264 section 7.4.1 says
/// "The last byte of the NAL unit shall not be equal to 0x00."
///
/// Currently, `00 00 01` is not understood as the very start of payload; the
/// first byte is expected to be a NAL header.
///
/// Finally, it errors on the sequence `00 00 02`, which is not allowed in
/// a single NAL or on an Annex B byte stream.
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

    /// In state `PreMark`, byte ranges of NAL bodies (excluding header bytes)
    /// referencing data in the shared [`MarkBuf`].
    /// Kept around (empty) in other states to re-use the backing allocation.
    pieces: Vec<BufRange>,

    /// In state `PreMark`, an entry for each NAL.
    /// Kept around (empty) in other states to re-use the backing allocation.
    nals: Vec<Nal>,

    /// True if we've seen a FU-A sequence where the NAL headers differ between
    /// fragments.
    seen_inconsistent_fu_a_nal_hdr: bool,

    /// True if we've seen a FU-A with both S and E bits set (a single-fragment
    /// FU-A, forbidden by RFC 6184 section 5.8).
    seen_single_fragment_fu_a: bool,

    /// The format used by the test-only `push_collect`/`pull` interface.
    #[cfg(test)]
    test_format: super::FrameFormat,
}

type Nal = super::h26x::Nal<NalHeader>;

/// An access unit that is currently being accumulated during `PreMark` state.
#[derive(Debug)]
struct AccessUnit<Ctx> {
    start_ctx: Ctx,
    end_ctx: Ctx,
    timestamp: crate::Timestamp,

    /// FU-A fragmentation unit state, if any.
    fu_a: Option<FuA>,

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

#[derive(Debug, Default)]
struct NewParams {
    sps: Option<Bytes>,
    pps: Option<Bytes>,

    /// Parameters parsed from `sps` and `pps` when the frame started, to be
    /// committed when it ends. Reset if another parameter set arrives.
    parsed: Option<InternalParameters>,
}

/// Metadata about an access unit, gathered as its NALs are scanned.
#[derive(Debug)]
struct FrameMeta {
    /// True unless a non-IDR slice has been seen.
    is_random_access_point: bool,

    /// True unless a NAL with `nal_ref_idc != 0` has been seen.
    is_disposable: bool,

    /// True if a VCL (slice) NAL has been seen.
    seen_vcl: bool,

    /// Parameter sets which differ from `Depacketizer::parameters`, if any.
    /// Boxed because they're rare, and `AccessUnit` moves on every packet.
    new_params: Option<Box<NewParams>>,

    /// Whether the first VCL NAL begins a picture, once known. If packets
    /// were lost just before this access unit and this isn't `Some(true)`,
    /// the access unit may be missing its beginning.
    first_vcl_starts_picture: Option<bool>,

    /// The header of the last complete NAL, for `can_end_au`.
    last_nal_hdr: Option<NalHeader>,

    /// Parameters set via [`VideoFrameStart::set_h264_parameters`], to be
    /// committed (after any in-band `new_params`) when the frame ends.
    param_override: Option<ParametersOverride>,
}

#[derive(Debug)]
struct FuA {
    initial_nal_header: h264_reader::nal::NalHeader,
    scanner: super::h26x::AnnexBScanner<[u8; 1]>,
    /// In-progress NAL state, persists across fragments.
    in_progress: Option<InProgressNal>,
}

/// Tracks an in-progress NAL being assembled via `NalHandler` calls.
#[derive(Debug)]
struct InProgressNal {
    hdr: h264_reader::nal::NalHeader,
    /// Total bytes of body data added to `pieces` so far. Excludes the header byte.
    pieces_bytes: usize,
}

/// `NalHandler` implementation for H.264 that accumulates pieces and NALs
/// into the `Depacketizer`'s storage.
struct H264NalHandler<'a> {
    pieces: &'a mut Vec<BufRange>,
    nals: &'a mut Vec<Nal>,
    in_progress: &'a mut Option<InProgressNal>,
}

impl super::h26x::NalHandler for H264NalHandler<'_> {
    type HeaderArray = [u8; 1];

    fn start(&mut self, header: [u8; 1]) -> Result<(), String> {
        let hdr =
            NalHeader::new(header[0]).map_err(|_| format!("bad NAL header {:02x}", header[0]))?;
        *self.in_progress = Some(InProgressNal {
            hdr,
            pieces_bytes: 0,
        });
        Ok(())
    }

    fn piece(&mut self, piece: BufRange) -> Result<(), String> {
        debug_assert!(piece.len > 0);
        let ip = self
            .in_progress
            .as_mut()
            .ok_or_else(|| "piece without start".to_string())?;
        ip.pieces_bytes += usize::from(piece.len);
        self.pieces.push(piece);
        Ok(())
    }

    fn end(&mut self) -> Result<(), String> {
        let ip = self
            .in_progress
            .take()
            .ok_or_else(|| "end without start".to_string())?;
        self.nals.push(Nal {
            hdr: ip.hdr,
            next_piece_idx: u32::try_from(self.pieces.len())
                .map_err(|_| "more than u32::MAX pieces!")?,
            len: u32::try_from(ip.pieces_bytes + 1) // +1 for the header byte
                .map_err(|_| "excessively long NAL")?,
        });
        Ok(())
    }
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

/// Scans an Annex B byte stream in a plain byte vector.
///
/// Calls `nal_fn` with a `Bytes` for each NAL found (stripping Annex B
/// separators and trailing zeros). Used for parsing sprop-parameter-sets
/// which are not in the ring buffer.
fn process_annex_b(
    data: Vec<u8>,
    mut nal_fn: impl FnMut(Bytes) -> Result<(), String>,
) -> Result<(), String> {
    if data.is_empty() {
        return Ok(());
    }
    let data = Bytes::from(data);
    let mut trailing_zeros: usize = 0;
    let mut nal_start: usize = 0;
    let mut i: usize = 0;
    while i < data.len() {
        if trailing_zeros == 0 {
            match memchr::memchr(0, &data[i..]) {
                Some(p) => {
                    i += p + 1;
                    trailing_zeros = 1;
                }
                None => break,
            }
        } else if trailing_zeros >= 2 && data[i] == 2 {
            return Err("forbidden sequence 00 00 02 in NAL".into());
        } else if trailing_zeros >= 2 && data[i] == 1 {
            let nal_end = i - trailing_zeros;
            if nal_end > nal_start {
                nal_fn(data.slice(nal_start..nal_end))?;
            }
            i += 1;
            nal_start = i;
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
    let nal_end = data.len() - trailing_zeros;
    if nal_end > nal_start {
        nal_fn(data.slice(nal_start..nal_end))?;
    }
    Ok(())
}

impl<Ctx: Clone> Depacketizer<Ctx> {
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
            #[cfg(test)]
            pending: Default::default(),
            mark: None,
            pieces: Vec::new(),
            nals: Vec::new(),
            parameters,
            seen_inconsistent_fu_a_nal_hdr: false,
            seen_single_fragment_fu_a: false,
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

    /// Discards the in-progress access unit's accumulated data and mark.
    fn discard_au(&mut self) {
        self.nals.clear();
        self.pieces.clear();
        self.mark = None;
    }

    pub(super) fn parameters(&self) -> Option<&VideoParameters> {
        self.parameters.as_ref().map(|p| &p.generic_parameters)
    }

    /// Returns the header of the NAL currently being assembled from FU-A
    /// fragments, if any.
    fn in_progress_hdr(au: &AccessUnit<Ctx>) -> Option<NalHeader> {
        au.fu_a.as_ref()?.in_progress.as_ref().map(|ip| ip.hdr)
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
            match nal.hdr.nal_unit_type() {
                UnitType::SeqParameterSet
                    if self
                        .parameters
                        .as_ref()
                        .map(|p| !nal_matches(p.in_band_sps(), nal.hdr, nal_pieces, buf))
                        .unwrap_or(true) =>
                {
                    let np = au.meta.new_params.get_or_insert_default();
                    np.sps = Some(to_bytes(nal.hdr, nal.len, nal_pieces, buf));
                    np.parsed = None;
                }
                UnitType::PicParameterSet
                    if self
                        .parameters
                        .as_ref()
                        .map(|p| !nal_matches(p.in_band_pps(), nal.hdr, nal_pieces, buf))
                        .unwrap_or(true) =>
                {
                    let np = au.meta.new_params.get_or_insert_default();
                    np.pps = Some(to_bytes(nal.hdr, nal.len, nal_pieces, buf));
                    np.parsed = None;
                }
                _ => {}
            }
            if is_vcl(nal.hdr) {
                au.meta.seen_vcl = true;
                au.meta
                    .first_vcl_starts_picture
                    .get_or_insert_with(|| super::h26x::starts_picture(nal_pieces, buf));
            }
            if is_non_idr_slice(nal.hdr) {
                au.meta.is_random_access_point = false;
            }
            if nal.hdr.nal_ref_idc() != 0 {
                au.meta.is_disposable = false;
            }
            au.meta.last_nal_hdr = Some(nal.hdr);
            piece_idx = next_piece_idx;
        }
        au.scanned_nals = u32::try_from(self.nals.len()).expect("NAL count fits in u32");
    }

    /// Parses new parameters, returning `None` if they're incomplete.
    fn parse_new_params(&self, np: &NewParams) -> Result<Option<InternalParameters>, String> {
        match (
            np.sps.as_deref(),
            np.pps.as_deref(),
            self.parameters.as_ref(),
        ) {
            (Some(sps_nal), Some(pps_nal), old_ip) => {
                let seen_extra_trailing_data =
                    old_ip.map(|o| o.seen_extra_trailing_data).unwrap_or(false);
                // TODO: could map this to a RtpPacketError more accurately.
                InternalParameters::parse_sps_and_pps(sps_nal, pps_nal, seen_extra_trailing_data)
                    .map(Some)
            }
            (Some(_), None, Some(old_ip)) | (None, Some(_), Some(old_ip)) => {
                let sps_nal = np.sps.as_deref().unwrap_or(&old_ip.sps_nal);
                let pps_nal = np.pps.as_deref().unwrap_or(&old_ip.pps_nal);
                // TODO: as above, could map this to a RtpPacketError more accurately.
                InternalParameters::parse_sps_and_pps(
                    sps_nal,
                    pps_nal,
                    old_ip.seen_extra_trailing_data,
                )
                .map(Some)
            }
            _ => Ok(None),
        }
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
        let mut is_disposable = au.meta.is_disposable;
        if let Some(hdr) = Self::in_progress_hdr(au) {
            if is_non_idr_slice(hdr) {
                is_random_access_point = false;
            }
            if hdr.nal_ref_idc() != 0 {
                is_disposable = false;
            }
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
        let mut param_override = None;
        au.started = Some(
            handler.frame_start(&mut VideoFrameStart {
                is_decodable: true,
                missing_prefix: au.loss > 0 && au.meta.first_vcl_starts_picture != Some(true),
                timestamp: au.timestamp,
                ctx: &au.start_ctx,
                is_random_access_point,
                is_disposable,
                has_new_parameters: new_params.is_some(),
                parameters: new_params
                    .or(self.parameters.as_ref())
                    .map(|p| &p.generic_parameters),
                param_override: Some(&mut param_override),
            }),
        );
        au.meta.param_override = param_override;
    }

    /// After scanning a packet, starts the frame if possible and delivers its data so far.
    fn stream(
        &mut self,
        au: &mut AccessUnit<Ctx>,
        buf: &MarkBuf,
        handler: &mut impl VideoHandler<Ctx>,
    ) {
        self.scan_meta(au, buf);
        let in_progress = Self::in_progress_hdr(au);
        if au.started.is_none() && (au.meta.seen_vcl || in_progress.is_some_and(is_vcl)) {
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
            if !au
                .fu_a
                .as_ref()
                .is_some_and(|fu_a| fu_a.scanner.has_deferred())
            {
                self.mark = None;
            }
        }
    }

    /// Supplies a new packet, delivering any resulting events to `handler`.
    pub(super) fn push(
        &mut self,
        pkt: &ReceivedPacketRef<'_, Ctx>,
        handler: &mut impl VideoHandler<Ctx>,
    ) {
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
        pkt: &ReceivedPacketRef<'_, Ctx>,
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
                    let loss = meta.continuity.loss_count();
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
                        if access_unit.fu_a.is_some() {
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
                            match access_unit.meta.last_nal_hdr {
                                Some(hdr) if can_end_au(hdr.nal_unit_type()) => {
                                    access_unit.end_ctx = meta.ctx.clone();
                                    self.finalize_access_unit(
                                        access_unit,
                                        "ts change",
                                        buf,
                                        handler,
                                    )?;
                                    AccessUnit::start(meta, 0, false)
                                }
                                Some(hdr) => {
                                    log::debug!(
                                        "Bogus mid-access unit timestamp change after {:?}",
                                        hdr
                                    );
                                    access_unit.timestamp.timestamp = meta.timestamp.timestamp;
                                    access_unit
                                }
                                None => {
                                    access_unit.timestamp.timestamp = meta.timestamp.timestamp;
                                    access_unit
                                }
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
                        pkts += meta.continuity.loss_count();
                        self.input_state = DepacketizerInputState::Loss { timestamp, pkts };
                        return Ok(());
                    }
                    AccessUnit::start(meta, pkts, false)
                }
            };

        let mark = meta.mark;
        let loss = meta.continuity.loss_count();
        let timestamp = meta.timestamp;

        if payload_len == 0 {
            return Err("Empty NAL".into());
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

        // https://tools.ietf.org/html/rfc6184#section-5.2
        let nal_header = payload.byte_at(0);
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
                self.scan_nals(payload_pos, payload_len, true, buf)?;
            }
            24 => {
                // STAP-A. https://tools.ietf.org/html/rfc6184#section-5.7.1
                if access_unit.fu_a.is_some() {
                    return Err("STAP-A NAL while FU-A fragment in progress".into());
                }
                let mut payload = payload;
                payload.advance(1);
                let mut pos = payload_pos + 1;
                while !payload.is_empty() {
                    if payload.len() < 3 {
                        return Err(format!(
                            "STAP-A has {} remaining bytes; expecting 2-byte length, non-empty NAL",
                            payload.len(),
                        ));
                    }
                    let nal_len = u16::from_be_bytes(payload.peek_array::<2>());
                    payload.advance(2);
                    pos += 2;
                    if nal_len == 0 {
                        return Err("zero length in STAP-A".into());
                    }
                    if usize::from(nal_len) > payload.len() {
                        return Err(format!(
                            "STAP-A too short: {} bytes remaining, expecting hdr + {nal_len}-byte NAL",
                            payload.len(),
                        ));
                    }
                    self.scan_nals(pos, nal_len, true, buf)?;
                    payload.advance(usize::from(nal_len));
                    pos += u64::from(nal_len);
                }
            }
            25..=27 | 29 => {
                return Err(format!(
                    "unimplemented/unexpected interleaved mode NAL ({nal_header:02x})",
                ));
            }
            28 => {
                // FU-A. https://tools.ietf.org/html/rfc6184#section-5.8
                if payload_len < 2 {
                    return Err(format!("FU-A len {payload_len} too short"));
                }
                let fu_header = payload.byte_at(1);
                let start = (fu_header & 0b10000000) != 0;
                let end = (fu_header & 0b01000000) != 0;
                let _reserved = (fu_header & 0b00100000) != 0;
                let nal_header =
                    NalHeader::new((nal_header & 0b011100000) | (fu_header & 0b00011111))
                        .expect("NalHeader is valid");
                let frag_pos = payload_pos + 2;
                let frag_len = payload_len - 2;
                if !end && mark {
                    return Err("FU-A pkt with MARK && !END".into());
                }
                match (start, access_unit.fu_a.take()) {
                    (true, Some(_)) => {
                        return Err("FU-A with start bit while frag in progress".into());
                    }
                    (true, None) => {
                        if end && !self.seen_single_fragment_fu_a {
                            // RFC 6184 section 5.8: "the Start bit and End bit MUST NOT both be
                            // set to one in the same FU header". Some cameras violate this by
                            // wrapping small NALs in a single-fragment FU-A.
                            // Tolerate by treating them as a complete NAL.
                            log::warn!(
                                "FU-A header {fu_header:02x} has both start and end bits set; \
                                 treating as a complete NAL. \
                                 Will not log about this again for this stream."
                            );
                            self.seen_single_fragment_fu_a = true;
                        }
                        // Create scanner with the reconstructed header pre-filled.
                        let mut fu_a = FuA {
                            initial_nal_header: nal_header,
                            scanner: super::h26x::AnnexBScanner::Pre {
                                cur: [u8::from(nal_header)],
                                bytes_read: 1,
                            },
                            in_progress: None,
                        };
                        fu_a.scanner.scan(
                            frag_pos,
                            buf.split(frag_pos, usize::from(frag_len)),
                            end,
                            &mut H264NalHandler {
                                pieces: &mut self.pieces,
                                nals: &mut self.nals,
                                in_progress: &mut fu_a.in_progress,
                            },
                        )?;
                        if !end {
                            access_unit.fu_a = Some(fu_a);
                        }
                    }
                    (false, Some(mut fu_a)) => {
                        if nal_header != fu_a.initial_nal_header
                            && !self.seen_inconsistent_fu_a_nal_hdr
                        {
                            log::warn!(
                                "FU-A has inconsistent NAL header: {:?} then {:?}; will not log about this again for this stream",
                                fu_a.initial_nal_header,
                                nal_header,
                            );
                            self.seen_inconsistent_fu_a_nal_hdr = true;
                        }
                        fu_a.scanner.scan(
                            frag_pos,
                            buf.split(frag_pos, usize::from(frag_len)),
                            end,
                            &mut H264NalHandler {
                                pieces: &mut self.pieces,
                                nals: &mut self.nals,
                                in_progress: &mut fu_a.in_progress,
                            },
                        )?;
                        if !end {
                            access_unit.fu_a = Some(fu_a);
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
                        return Err("FU-A has start bit unset while no frag in progress".into());
                    }
                }
            }
            _ => return Err(format!("bad nal header {nal_header:02x}")),
        }
        self.stream(&mut access_unit, buf, handler);
        self.input_state = if mark {
            match access_unit.meta.last_nal_hdr {
                Some(hdr) if can_end_au(hdr.nal_unit_type()) => {
                    access_unit.end_ctx = meta.ctx.clone();
                    self.finalize_access_unit(access_unit, "mark", buf, handler)?;
                    DepacketizerInputState::PostMark { timestamp, loss: 0 }
                }
                Some(hdr) => {
                    log::debug!("Bogus mid-access unit mark on {:?}", hdr);
                    access_unit.timestamp.timestamp = timestamp.timestamp;
                    DepacketizerInputState::PreMark(access_unit)
                }
                None => DepacketizerInputState::PreMark(access_unit),
            }
        } else {
            DepacketizerInputState::PreMark(access_unit)
        };
        Ok(())
    }

    /// Scans ring buffer data for NAL units using `AnnexBScanner`, splitting
    /// on Annex B separators. Used for single NAL and STAP-A payloads where
    /// the scanner is temporary.
    fn scan_nals(
        &mut self,
        frag_pos: u64,
        frag_len: u16,
        end: bool,
        buf: &MarkBuf,
    ) -> Result<(), String> {
        let mut scanner = super::h26x::AnnexBScanner::<[u8; 1]>::Pre {
            cur: [0u8; 1],
            bytes_read: 0,
        };
        let mut in_progress = None;
        scanner.scan(
            frag_pos,
            buf.split(frag_pos, usize::from(frag_len)),
            end,
            &mut H264NalHandler {
                pieces: &mut self.pieces,
                nals: &mut self.nals,
                in_progress: &mut in_progress,
            },
        )
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
        // params reflect the latest SPS/PPS.
        let new_params = match au.meta.new_params.take() {
            None => None,
            Some(mut np) => match np.parsed.take() {
                Some(p) => Some(p),
                None => self.parse_new_params(&np)?,
            },
        };
        let mut has_new_parameters = new_params.is_some();
        if new_params.is_some() {
            self.parameters = new_params;
        }

        let accumulate = match au.started {
            Some(a) => a,
            None => handler.frame_start(&mut VideoFrameStart {
                is_decodable: true,
                missing_prefix: au.loss > 0 && au.meta.first_vcl_starts_picture != Some(true),
                timestamp: au.timestamp,
                ctx: &au.start_ctx,
                is_random_access_point: au.meta.is_random_access_point,
                is_disposable: au.meta.is_disposable,
                has_new_parameters,
                parameters: self.parameters.as_ref().map(|p| &p.generic_parameters),
                param_override: Some(&mut au.meta.param_override),
            }),
        };
        if let Some(o) = au.meta.param_override.take() {
            self.parameters = Some(o.commit(self.parameters.as_ref()));
            has_new_parameters = true;
        }
        au.delivery
            .deliver(&self.nals, &self.pieces, None, buf, handler);

        handler.frame_end(&mut VideoFrameEnd {
            is_decodable: true,
            missing_prefix: au.loss > 0 && au.meta.first_vcl_starts_picture != Some(true),
            timestamp: au.timestamp,
            start_ctx: &au.start_ctx,
            end_ctx: &au.end_ctx,
            is_random_access_point: au.meta.is_random_access_point,
            is_disposable: au.meta.is_disposable,
            has_new_parameters,
            body: FrameBody::H264(FrameEndBody {
                au: (accumulate == Accumulate::Yes && !au.trimmed).then_some(AuData {
                    nals: &self.nals,
                    pieces: &self.pieces,
                    buf,
                }),
                parameters: &self.parameters,
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
    fn push_collect(&mut self, pkt: &ReceivedPacketRef<'_, crate::PacketContext>) {
        let mut pending = std::mem::take(&mut self.pending);
        pending.push(pkt, self.test_format, |c| self.push(pkt, c));
        self.pending = pending;
    }

    fn pull(&mut self) -> Option<Result<super::testutil::Item, String>> {
        self.pending.pull()
    }
}

/// Returns true if the given NAL is a VCL (slice) NAL.
fn is_vcl(hdr: NalHeader) -> bool {
    matches!(u8::from(hdr) & 0b11111, 1..=5)
}

/// Returns true if the given NAL is a VCL NAL which is not part of an IDR picture.
fn is_non_idr_slice(hdr: NalHeader) -> bool {
    matches!(u8::from(hdr) & 0b11111, 1..=4)
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

    /// Returns the parameters to prepend to the frame in the given format, if any.
    fn prepend_params(&self, format: super::FrameFormat) -> Option<&InternalParameters> {
        use super::ParameterSetInsertion;
        let prepend = self.is_random_access_point
            && match format.parameter_set_insertion {
                ParameterSetInsertion::EachKeyFrame => true,
                ParameterSetInsertion::OnChange => self.has_new_parameters,
                ParameterSetInsertion::Never => false,
            };
        if prepend {
            self.parameters.as_ref()
        } else {
            None
        }
    }

    pub(super) fn data_len(&self, format: super::FrameFormat) -> Option<usize> {
        let au = self.au.as_ref()?;
        let params_buf;
        let params: &[&[u8]] = match self.prepend_params(format) {
            Some(p) => {
                params_buf = [&p.sps_nal[..], &p.pps_nal[..]];
                &params_buf
            }
            None => &[],
        };
        Some(super::h26x::frame_len(au.nals, params))
    }

    pub(super) fn visit(
        &self,
        format: super::FrameFormat,
        visitor: &mut impl FnMut(&[u8]),
    ) -> bool {
        let Some(au) = self.au.as_ref() else {
            return false;
        };
        let params_buf;
        let params: &[&[u8]] = match self.prepend_params(format) {
            Some(p) => {
                params_buf = [&p.sps_nal[..], &p.pps_nal[..]];
                &params_buf
            }
            None => &[],
        };
        super::h26x::visit_frame(
            au.nals,
            au.pieces,
            au.buf,
            params,
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
///
/// We specifically prohibit this for the SPS, PPS, and SEI. Some cameras
/// incorrectly set the RTP marker bit and/or change the timestamp after these.
fn can_end_au(nal_unit_type: UnitType) -> bool {
    // H.264 section 7.4.1.2.3 specifies that SPS, PPS, and SEI NAL units
    // must precede the primary coded picture within an access unit. If any of
    // these appear after the last VCL NAL unit, they signal the start of a
    // new access unit rather than ending the current one. An access unit
    // containing only these non-VCL NAL types (with no VCL NAL) is not a
    // valid picture.
    !matches!(
        nal_unit_type,
        UnitType::SeqParameterSet | UnitType::PicParameterSet | UnitType::SEI
    )
}

impl<Ctx: Clone> AccessUnit<Ctx> {
    fn start(
        meta: &crate::rtp::ReceivedPacketMeta<Ctx>,
        additional_loss: u16,
        same_ts_as_prev: bool,
    ) -> Self {
        AccessUnit {
            start_ctx: meta.ctx.clone(),
            end_ctx: meta.ctx.clone(),
            timestamp: meta.timestamp,
            meta: FrameMeta {
                is_random_access_point: true,
                is_disposable: true,
                seen_vcl: false,
                new_params: None,
                first_vcl_starts_picture: None,
                last_nal_hdr: None,
                param_override: None,
            },
            scanned_nals: 0,
            started: None,
            delivery: Default::default(),
            trimmed: false,
            fu_a: None,

            // TODO: overflow?
            loss: meta.continuity.loss_count() + additional_loss,
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
            /* 6 */ UnitType::SEI
                if seen_vcl => {
                    errs.push_str("\n* SEI after VCL");
                }
            /* 9 */ UnitType::AccessUnitDelimiter
                if i != 0 => {
                    let _ = write!(errs, "\n* access unit delimiter must be first in AU; was preceded by {:?}",
                                nals[i-1].hdr);
                }
            /* 10 */ UnitType::EndOfSeq
                if !seen_vcl => {
                    errs.push_str("\n* end of sequence without VCL");
                }
            /* 11 */ UnitType::EndOfStream
                if i != nals.len() - 1 => {
                    errs.push_str("\n* end of stream NAL isn't last");
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
    generic_parameters: VideoParameters,

    /// The (single) SPS NAL.
    sps_nal: Bytes,

    /// The (single) PPS NAL.
    pps_nal: Bytes,

    seen_extra_trailing_data: bool,

    /// If set via [`crate::codec::VideoFrameStart::set_h264_parameters`], the in-band SPS and PPS
    /// which were overridden. Parameter sets received later are compared
    /// against these to detect changes, so that a camera repeating its
    /// original parameters doesn't undo the override.
    overridden: Option<Box<(Bytes, Bytes)>>,
}

/// Parameters set via [`VideoFrameStart::set_h264_parameters`], not yet committed.
#[derive(Debug)]
struct ParametersOverride(Box<InternalParameters>);

impl super::events::ParametersOverrideSlot for Option<ParametersOverride> {
    fn parameters(&self) -> Option<&VideoParameters> {
        self.as_ref().map(|o| &o.0.generic_parameters)
    }

    fn set_h264(&mut self, sps: &[u8], pps: &[u8]) -> Result<(), String> {
        let p = InternalParameters::parse_sps_and_pps(sps, pps, true)?;
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
            process_annex_b(part, &mut nal_fn)?;
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
        debug!("SPS {sps_hex}: {:#?}", sps);
        if sps_has_extra_trailing_data && !seen_extra_trailing_data {
            log::warn!(
                "Ignoring trailing data in SPS {sps_hex}; will not log about trailing data again for this stream."
            );
            seen_extra_trailing_data = true;
        }

        let all_pixel_dimensions = Self::all_pixel_dimensions(&sps)
            .map_err(|e| format!("SPS has invalid pixel dimensions: {e:?}"))?;

        let (decoder_config_record, sps_nal, pps_nal) = {
            // Create the AVCDecoderConfiguration, ISO/IEC 14496-15 section 5.2.4.1.
            // The beginning of the AVCDecoderConfiguration takes a few values from
            // the SPS (ISO/IEC 14496-10 section 7.3.2.1.1).
            let mut buf = BytesMut::with_capacity(11 + sps_nal.len() + pps_nal.len());
            buf.put_u8(1); // configurationVersion
            buf.extend(&sps_rbsp[0..=2]); // profile_idc . AVCProfileIndication
            // ...misc bits... . profile_compatibility
            // level_idc . AVCLevelIndication

            // Hardcode lengthSizeMinusOne to 3, matching 4-byte lengths.
            buf.put_u8(0xff);

            // Only support one SPS and PPS.
            // ffmpeg's ff_isom_write_avcc has the same limitation, so it's probably
            // fine. This next byte is a reserved 0b111 + a 5-bit # of SPSs (1).
            buf.put_u8(0xe1);
            buf.extend(
                &u16::try_from(sps_nal.len())
                    .map_err(|_| {
                        format!("SPS NAL is {} bytes long; must fit in u16", sps_nal.len())
                    })?
                    .to_be_bytes()[..],
            );
            let sps_nal_start = buf.len();
            buf.extend_from_slice(sps_nal);
            let sps_nal_end = buf.len();
            buf.put_u8(1); // # of PPSs.
            buf.extend(
                &u16::try_from(pps_nal.len())
                    .map_err(|_| {
                        format!("PPS NAL is {} bytes long; must fit in u16", pps_nal.len())
                    })?
                    .to_be_bytes()[..],
            );
            let pps_nal_start = buf.len();
            buf.extend_from_slice(pps_nal);
            let pps_nal_end = buf.len();
            assert_eq!(
                buf.len(),
                11 + (sps_nal_end - sps_nal_start) + (pps_nal_end - pps_nal_start)
            );

            let buf = buf.freeze();
            let sps_nal = buf.slice(sps_nal_start..sps_nal_end);
            let pps_nal = buf.slice(pps_nal_start..pps_nal_end);
            (buf, sps_nal, pps_nal)
        };

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
        Ok(InternalParameters {
            generic_parameters: VideoParameters {
                rfc6381_codec,
                all_pixel_dimensions,
                pixel_aspect_ratio,
                frame_rate,
                annex_b_parameter_sets: super::h26x::annex_b_parameter_sets(&[&sps_nal, &pps_nal]),
                decoder_config_record,
                codec: super::VideoParametersCodec::H264 {
                    sps: sps_nal.clone(),
                    pps: pps_nal.clone(),
                },
            },
            sps_nal,
            pps_nal,
            seen_extra_trailing_data,
            overridden: None,
        })
    }

    /// Returns the SPS as last received in-band (or via `sprop-parameter-sets`).
    fn in_band_sps(&self) -> &[u8] {
        self.overridden
            .as_ref()
            .map_or(&self.sps_nal[..], |o| &o.0[..])
    }

    /// Returns the PPS as last received in-band (or via `sprop-parameter-sets`).
    fn in_band_pps(&self) -> &[u8] {
        self.overridden
            .as_ref()
            .map_or(&self.pps_nal[..], |o| &o.1[..])
    }

    // XXX: copy'n'pasted'n'modified from `h264-reader`.
    fn all_pixel_dimensions(sps: &SeqParameterSet) -> Result<AllPixelDimensions, SpsError> {
        let coded_width: u16 = sps
            .pic_width_in_mbs_minus1
            .checked_add(1)
            .and_then(|w| w.checked_mul(16))
            .and_then(|w| w.try_into().ok())
            .ok_or(SpsError::FieldValueTooLarge {
                name: "pic_width_in_mbs_minus1",
                value: sps.pic_width_in_mbs_minus1,
            })?;
        use h264_reader::nal::sps::{ChromaFormat, FrameMbsFlags};
        let mul = match sps.frame_mbs_flags {
            FrameMbsFlags::Fields { .. } => 2,
            FrameMbsFlags::Frames => 1,
        };
        let vsub = if sps.chroma_info.chroma_format == ChromaFormat::YUV420 {
            1
        } else {
            0
        };
        let hsub = if sps.chroma_info.chroma_format == ChromaFormat::YUV420
            || sps.chroma_info.chroma_format == ChromaFormat::YUV422
        {
            1
        } else {
            0
        };

        let step_x = 1 << hsub;
        let step_y = mul << vsub;

        let coded_height: u16 = (sps.pic_height_in_map_units_minus1 + 1)
            .checked_mul(mul * 16)
            .and_then(|h| h.try_into().ok())
            .ok_or(SpsError::FieldValueTooLarge {
                name: "pic_height_in_map_units_minus1",
                value: sps.pic_height_in_map_units_minus1,
            })?;
        let coded = (coded_width, coded_height);
        if let Some(ref crop) = sps.frame_cropping {
            let left_offset = crop
                .left_offset
                .checked_mul(step_x)
                .and_then(|o| o.try_into().ok())
                .ok_or(SpsError::FieldValueTooLarge {
                    name: "left_offset",
                    value: crop.left_offset,
                })?;
            let right_offset = crop
                .right_offset
                .checked_mul(step_x)
                .and_then(|o| o.try_into().ok())
                .ok_or(SpsError::FieldValueTooLarge {
                    name: "right_offset",
                    value: crop.right_offset,
                })?;
            let top_offset = crop
                .top_offset
                .checked_mul(step_y)
                .and_then(|o| o.try_into().ok())
                .ok_or(SpsError::FieldValueTooLarge {
                    name: "top_offset",
                    value: crop.top_offset,
                })?;
            let bottom_offset = crop
                .bottom_offset
                .checked_mul(step_y)
                .and_then(|o| o.try_into().ok())
                .ok_or(SpsError::FieldValueTooLarge {
                    name: "bottom_offset",
                    value: crop.bottom_offset,
                })?;
            let display_width = coded_width
                .checked_sub(left_offset)
                .and_then(|w| w.checked_sub(right_offset));
            let display_height = coded_height
                .checked_sub(top_offset)
                .and_then(|w| w.checked_sub(bottom_offset));
            if let (Some(display_width), Some(display_height)) = (display_width, display_height) {
                Ok(AllPixelDimensions {
                    display: (display_width, display_height),
                    coded,
                })
            } else {
                Err(SpsError::CroppingError(crop.clone()))
            }
        } else {
            Ok(AllPixelDimensions {
                display: coded,
                coded,
            })
        }
    }
}

/// Returns true iff the bytes of `nal` equal the bytes of `[hdr, ..pieces]`.
fn nal_matches(nal: &[u8], hdr: NalHeader, pieces: &[BufRange], buf: &MarkBuf) -> bool {
    if nal.first() != Some(&u8::from(hdr)) {
        return false;
    }
    let mut nal_pos = 1;
    for piece in pieces {
        let (s1, s2) = buf.split(piece.pos, piece.len as usize).slices();
        let new_pos = nal_pos + piece.len as usize;
        if nal.len() < new_pos {
            return false;
        }
        let s1_end = nal_pos + s1.len();
        if s1[..] != nal[nal_pos..s1_end] {
            return false;
        }
        if !s2.is_empty() && s2[..] != nal[s1_end..new_pos] {
            return false;
        }
        nal_pos = new_pos;
    }
    nal_pos == nal.len()
}

/// Saves the given NAL to a contiguous `Bytes`.
fn to_bytes(hdr: NalHeader, len: u32, pieces: &[BufRange], buf: &MarkBuf) -> Bytes {
    let len = crate::to_usize(len);
    let mut out = Vec::with_capacity(len);
    out.push(hdr.into());
    for piece in pieces {
        let (s1, s2) = buf.split(piece.pos, piece.len as usize).slices();
        out.extend_from_slice(s1);
        out.extend_from_slice(s2);
    }
    debug_assert_eq!(len, out.len());
    out.into()
}

/// Packetizes H.264 NAL units per RFC 6184 packetization mode 1.
///
/// Emits single NAL unit packets, STAP-A aggregation packets (if enabled),
/// and FU-A fragments. See [`crate::codec::VideoPacketizer`].
pub(crate) type Packetizer = super::h26x::packetizer::Packetizer<PacketizeCodec>;

#[derive(Debug)]
pub(crate) enum PacketizeCodec {}

impl super::h26x::packetizer::Codec for PacketizeCodec {
    type Header = [u8; 1];
    type FuHeader = [u8; 2];
    const PARAMETER_SETS: usize = 2;

    fn parameter_sets(parameters: &VideoParameters) -> Option<Vec<Bytes>> {
        match parameters.codec_params() {
            super::VideoParametersCodec::H264 { sps, pps } => Some(vec![sps.clone(), pps.clone()]),
            _ => None,
        }
    }

    fn parameters(sets: &[&[u8]]) -> Result<VideoParameters, String> {
        let &[sps, pps] = sets else {
            unreachable!("expected SPS and PPS");
        };
        InternalParameters::parse_sps_and_pps(sps, pps, true).map(|p| p.generic_parameters)
    }

    fn payload_format(parameters: &VideoParameters, sets: &[Bytes]) -> super::PayloadFormat {
        let e = &base64::engine::general_purpose::STANDARD;
        let profile_level_id = parameters
            .rfc6381_codec()
            .strip_prefix("avc1.")
            .expect("H.264 codec string starts with avc1.");
        super::PayloadFormat::new("video", "H264", 90_000).with_fmtp(format!(
            "packetization-mode=1;profile-level-id={profile_level_id};sprop-parameter-sets={},{}",
            e.encode(&sets[0]),
            e.encode(&sets[1]),
        ))
    }

    fn parameter_set_index([hdr]: [u8; 1]) -> Option<usize> {
        match hdr & 0b1_1111 {
            7 => Some(0),
            8 => Some(1),
            _ => None,
        }
    }

    /// Type 0 is unspecified by H.264, and types 24–31 are unspecified by
    /// H.264 and used by RFC 6184 for aggregation and fragmentation packets.
    fn invalid_header([hdr]: [u8; 1]) -> Option<&'static str> {
        (!matches!(hdr & 0b1_1111, 1..=23)).then_some("invalid type")
    }

    /// Per RFC 6184 section 5.7.1, the F bit is the OR of the aggregated NALs'
    /// F bits, and the NRI is the maximum of their NRIs.
    fn aggregation_header([a]: [u8; 1], [b]: [u8; 1]) -> [u8; 1] {
        let f = (a | b) & 0b1000_0000;
        let nri = (a & 0b0110_0000).max(b & 0b0110_0000);
        [f | nri | 24]
    }

    fn fu_header([hdr]: [u8; 1], start: bool, end: bool) -> [u8; 2] {
        [
            (hdr & 0b1110_0000) | 28,
            u8::from(start) << 7 | u8::from(end) << 6 | (hdr & 0b1_1111),
        ]
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroU32;

    use bytes::Bytes;

    use crate::buf::MarkBuf;
    use crate::codec::testutil::Item;
    use crate::rtp::ReceivedPacketRef;
    use crate::testutil::TestPacket;
    use crate::testutil::{assert_eq_hex, assert_eq_hexes, init_logging};

    use super::*;

    #[test]
    fn depacketize() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA")).unwrap();
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
                // plain SEI packet.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, b"\x06plain".iter().copied());
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // STAP-A packet.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x18\x00\x09\x06stap-a 1\x00\x09\x06stap-a 2");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU-A packet (non-IDR slice, type 1), start.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x7c\x81fu-a start, ");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU-A packet, middle.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 3,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x7c\x01fu-a middle, ");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU-A packet, end.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 4,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x7c\x41fu-a end");
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            _ => panic!(),
        };
        assert_eq_hex!(
            frame.data(),
            b"\x00\x00\x00\x06\x06plain\
                     \x00\x00\x00\x09\x06stap-a 1\
                     \x00\x00\x00\x09\x06stap-a 2\
                     \x00\x00\x00\x22\x61fu-a start, fu-a middle, fu-a end"
        );
        assert!(!d.seen_inconsistent_fu_a_nal_hdr);
    }

    /// Test depacketizing when reserved bit is set on FU-A header.
    /// Longse CMSEKL800 on
    /// firmware KL8_1ND_BVD0L1A0T0Q0_A00038268_V2.0.10.241016_R2
    /// has been found to set this bit - however the resulting
    /// frame is fine.
    #[test]
    fn depacketize_reserved_bit_set() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA")).unwrap();
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
                // FU-A packet (non-IDR slice, type 1, reserved bit set), start.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x7c\xa1fu-a start, ");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU-A packet, middle.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 3,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x7c\x21fu-a middle, ");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU-A packet, end.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 4,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x7c\x61fu-a end");
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            _ => panic!(),
        };
        assert_eq_hex!(
            frame.data(),
            b"\x00\x00\x00\x22\x61fu-a start, fu-a middle, fu-a end"
        );
    }

    /// Test bad framing at the start of stream from a Reolink RLC-822A
    /// Reolink RLC-822A (IPC_523128M8MP) running firmware v3.0.0.177_21012101:
    /// suppress incorrect access unit changes after the SPS and PPS.
    #[test]
    fn depacketize_reolink_bad_framing_at_start() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
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
        {
            let pkt = TestPacket {
                // SPS with (incorrect) mark
                ctx: crate::PacketContext::dummy(),
                timestamp: ts1,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(
                &mut buf,
                *b"\x67\x64\x00\x33\xac\x15\x14\xa0\xa0\x2f\xf9\x50",
            );
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // PPS
                ctx: crate::PacketContext::dummy(),
                timestamp: ts1,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x68\xee\x3c\xb0");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // Slice layer without partitioning IDR.
                // This has a different timestamp than the SPS and PPS, even though
                // RFC 6184 section 5.1 says that "the timestamp must match that of
                // the primary coded picture of the access unit and that the marker
                // bit can only be set on the final packet of the access unit.""
                ctx: crate::PacketContext::dummy(),
                timestamp: ts2,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x65slice");
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            o => panic!("unexpected pull result {o:#?}"),
        };
        assert_eq_hex!(
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
        let mut buf = MarkBuf::new(65536);
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
        {
            let pkt = TestPacket {
                // Slice layer without partitioning non-IDR, representing the
                // last frame of the previous GOP.
                ctx: crate::PacketContext::dummy(),
                timestamp: ts1,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x01slice");
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            o => panic!("unexpected pull result {o:#?}"),
        };
        assert_eq_hex!(frame.data(), b"\x00\x00\x00\x06\x01slice");
        assert_eq!(frame.timestamp, ts1);
        {
            let pkt = TestPacket {
                // SPS with (incorrect) timestamp matching last frame.
                ctx: crate::PacketContext::dummy(),
                timestamp: ts1,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false, // correctly has no mark, unlike first SPS in stream.
                payload_type: 0,
            }
            .write(
                &mut buf,
                *b"\x67\x64\x00\x33\xac\x15\x14\xa0\xa0\x2f\xf9\x50",
            );
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // PPS, again with timestamp matching last frame.
                ctx: crate::PacketContext::dummy(),
                timestamp: ts1,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x68\xee\x3c\xb0");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // Slice layer without partitioning IDR. Now correct timestamp.
                ctx: crate::PacketContext::dummy(),
                timestamp: ts2,
                ssrc: 0,
                sequence_number: 3,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x65slice");
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            o => panic!("unexpected pull result {o:#?}"),
        };
        assert_eq_hex!(
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
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, Some("a=fmtp:96 packetization-mode=1;profile-level-id=4d002a;sprop-parameter-sets=Z00AKp2oHgCJ+WbgICAoAAADAAgAAAMAfCA=,aO48gA==")).unwrap();
        match d.parameters() {
            Some(v) => {
                assert_eq!(v.pixel_dimensions(), (1920, 1080));
            }
            o => panic!("{o:?}"),
        }
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        {
            let pkt = TestPacket { // new SPS.
            ctx: crate::PacketContext::dummy(),
            timestamp,
            ssrc: 0,
            sequence_number: 0,
            loss: 0,
            mark: false,
            payload_type: 0,
        }
            .write(&mut buf, *b"\x67\x4d\x40\x1e\x9a\x64\x05\x01\xef\xf3\x50\x10\x10\x14\x00\x00\x0f\xa0\x00\x01\x38\x80\x10");
            d.push_collect(&pkt)
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // same PPS again.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x68\xee\x3c\x80");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // dummy slice NAL to end the AU.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x65slice");
            d.push_collect(&pkt);
        }

        // By codec::Depacketizer::parameters's contract, it's unspecified what the depacketizer
        // parameters are set to between push and pull.

        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            o => panic!("unexpected pull result {o:#?}"),
        };

        // After pull, new_parameters and parameters() both reflect the change.
        assert!(frame.has_new_parameters);
        match d.parameters() {
            Some(v) => {
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
        let mut buf = MarkBuf::new(65536);
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
        {
            let pkt = TestPacket {
            // SPS
            ctx: crate::PacketContext::dummy(),
            timestamp,
            ssrc: 0,
            sequence_number: 0,
            loss: 0,
            mark: false,
            payload_type: 0,
        }
            .write(&mut buf, *b"\x67\x4d\x00\x28\xe9\x00\xf0\x04\x4f\xcb\x08\x00\x00\x1f\x48\x00\x07\x54\xe0\x20");
            d.push_collect(&pkt)
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // PPS
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x68\xea\x8f\x20");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // IDR slice
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x65idr slice");
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            _ => panic!(),
        };
        assert!(frame.has_new_parameters);
        assert!(d.parameters().is_some());
    }

    #[test]
    fn sps_with_extra_trailing_bytes() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        // https://github.com/scottlamb/retina/issues/102
        const PARAMS: &str = "packetization-mode=1;profile-level-id=640033";
        let mut d = super::Depacketizer::new(90_000, Some(PARAMS)).unwrap();
        assert!(d.parameters().is_none());

        // The stream should honor in-band parameters, even with an extra byte.
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        {
            let pkt = TestPacket {
            // SPS
            ctx: crate::PacketContext::dummy(),
            timestamp,
            ssrc: 0,
            sequence_number: 0,
            loss: 0,
            mark: false,
            payload_type: 0,
        }
            .write(&mut buf, *b"\x67\x64\x00\x33\xac\x15\x14\xa0\xa0\x3d\xa1\x00\x00\x04\xf6\x00\x00\x63\x38\x04\x04");
            d.push_collect(&pkt)
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // PPS
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x68\xee\x3c\xb0");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // IDR slice
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x65idr slice");
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
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

    // Expected frame data with inline SPS/PPS retained (default behavior).
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

    // Expected frame data with inline SPS/PPS stripped (MP4 mode).
    #[rustfmt::skip]
    static PREFIXED_NALS_STRIPPED: [u8; 16] = [
        // IDR slice
        0x00, 0x00, 0x00, 0x0c,
        0x65, b'i', b'd', b'r', b' ', b's', b'l', b'i', 0x00, 0x00, b'c', b'e',
    ];

    // Expected frame data in SIMPLE mode (Annex B framing, SPS/PPS prepended on key frame).
    #[rustfmt::skip]
    static ANNEX_B_NALS_SIMPLE: [u8; 48] = [
        // SPS
        0x00, 0x00, 0x00, 0x01,
        0x67, 0x64, 0x00, 0x33, 0xac, 0x15, 0x14, 0xa0, 0xa0, 0x3d, 0xa1,
        0x00, 0x00, 0x04, 0xf6, 0x00, 0x00, 0x63, 0x38, 0x04,
        // PPS
        0x00, 0x00, 0x00, 0x01,
        0x68, 0xee, 0x3c, 0xb0,
        // IDR slice
        0x00, 0x00, 0x00, 0x01,
        0x65, b'i', b'd', b'r', b' ', b's', b'l', b'i', 0x00, 0x00, b'c', b'e',
    ];

    /// Tests that the depacketizer can handle Annex B separators in a "single-NAL" unit type.
    ///
    /// One bit of nuance here is that the Annex B separation has to happen *before* the
    /// `can_end_au` logic, as the initial NAL unit type is one that can not end a NAL.
    #[test]
    fn parse_annex_b_single_nal() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d =
            super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=640033"))
                .unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        {
            let pkt = TestPacket {
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, ANNEX_B_NALS);
            d.push_collect(&pkt);
        }
        let Some(Ok(Item::Video(frame))) = d.pull() else {
            panic!();
        };
        assert_eq_hex!(frame.data(), &PREFIXED_NALS);
    }

    /// Tests that the depacketizer can handle Annex B separators in a FU-A unit,
    /// split across multiple packets.
    #[test]
    fn parse_annex_b_fu_a() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
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
                    timestamp: 0,
                    clock_rate: NonZeroU32::new(90_000).unwrap(),
                    start: 0,
                };
                let mut first_pkt = Vec::with_capacity(first_pkt_len + 1);
                first_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                first_pkt.push((ANNEX_B_NALS[0] & 0b0001_1111) | 0b1000_0000); // start
                first_pkt.extend_from_slice(&ANNEX_B_NALS[1..first_pkt_len]);
                println!("  pushing first pkt");
                {
                    let pkt = TestPacket {
                        ctx: crate::PacketContext::dummy(),
                        timestamp,
                        ssrc: 0,
                        sequence_number: 0,
                        loss: 0,
                        mark: false,
                        payload_type: 0,
                    }
                    .write(&mut buf, first_pkt);
                    d.push_collect(&pkt);
                }
                assert_eq!(d.pull(), None);
                if middle_pkt_len > 0 {
                    let mut middle_pkt = Vec::with_capacity(middle_pkt_len + 2);
                    middle_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                    middle_pkt.push(ANNEX_B_NALS[0] & 0b0001_1111); // middle
                    middle_pkt.extend_from_slice(
                        &ANNEX_B_NALS[first_pkt_len..first_pkt_len + middle_pkt_len],
                    );
                    println!("  pushing middle pkt");
                    {
                        let pkt = TestPacket {
                            ctx: crate::PacketContext::dummy(),
                            timestamp,
                            ssrc: 0,
                            sequence_number: 1,
                            loss: 0,
                            mark: false,
                            payload_type: 0,
                        }
                        .write(&mut buf, middle_pkt);
                        d.push_collect(&pkt);
                    }
                    assert_eq!(d.pull(), None);
                }
                let mut last_pkt =
                    Vec::with_capacity(ANNEX_B_NALS.len() - first_pkt_len - middle_pkt_len + 2);
                last_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                last_pkt.push((ANNEX_B_NALS[0] & 0b0001_1111) | 0b0100_0000); // end
                last_pkt.extend_from_slice(&ANNEX_B_NALS[first_pkt_len + middle_pkt_len..]);
                println!("  pushing last pkt");
                {
                    let pkt = TestPacket {
                        ctx: crate::PacketContext::dummy(),
                        timestamp,
                        ssrc: 0,
                        sequence_number: 2,
                        loss: 0,
                        mark: true,
                        payload_type: 0,
                    }
                    .write(&mut buf, last_pkt);
                    d.push_collect(&pkt);
                }
                println!("  pulling");
                let Some(Ok(Item::Video(frame))) = d.pull() else {
                    panic!();
                };
                assert_eq_hex!(frame.data(), &PREFIXED_NALS);
            }
        }
    }

    /// Like `parse_annex_b_fu_a` but with a small ring buffer that forces
    /// fragment data to wrap around the ring boundary. This exercises the
    /// two-slice path in `add_nals` (via `buf.slices` returning
    /// non-empty `s2`), including trailing zero handling across the wrap.
    #[test]
    fn parse_annex_b_fu_a_ring_wrap() {
        init_logging();
        // 64 is the smallest power-of-two that fits ANNEX_B_NALS (44 bytes)
        // plus FU-A overhead. We try all wrap offsets so that the ring
        // boundary falls at every possible position within the data.
        for wrap_offset in 1..ANNEX_B_NALS.len() {
            for first_pkt_len in 2..ANNEX_B_NALS.len() - 1 {
                let mut buf = MarkBuf::new(64);
                // Advance the write position so that FU-A data will wrap.
                // Write `wrap_offset` bytes of dummy data, then advance
                // unparsed past it so reclaim can free it.
                let fill = 64 - wrap_offset;
                buf.extend(&vec![0xAA; fill]);
                buf.advance_unparsed(buf.end());
                // Now the next write starts at position `fill` in the
                // 64-byte ring, so after `wrap_offset` bytes it wraps.

                let mut d = super::Depacketizer::new(
                    90_000,
                    Some("packetization-mode=1;profile-level-id=640033"),
                )
                .unwrap();
                let timestamp = crate::Timestamp {
                    timestamp: 0,
                    clock_rate: NonZeroU32::new(90_000).unwrap(),
                    start: 0,
                };
                let mut first_pkt = Vec::with_capacity(first_pkt_len + 2);
                first_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28);
                first_pkt.push((ANNEX_B_NALS[0] & 0b0001_1111) | 0b1000_0000);
                first_pkt.extend_from_slice(&ANNEX_B_NALS[1..first_pkt_len]);
                {
                    let pkt = TestPacket {
                        ctx: crate::PacketContext::dummy(),
                        timestamp,
                        ssrc: 0,
                        sequence_number: 0,
                        loss: 0,
                        mark: false,
                        payload_type: 0,
                    }
                    .write(&mut buf, first_pkt);
                    d.push_collect(&pkt);
                }
                assert_eq!(d.pull(), None);
                let mut last_pkt = Vec::with_capacity(ANNEX_B_NALS.len() - first_pkt_len + 2);
                last_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28);
                last_pkt.push((ANNEX_B_NALS[0] & 0b0001_1111) | 0b0100_0000);
                last_pkt.extend_from_slice(&ANNEX_B_NALS[first_pkt_len..]);
                {
                    let pkt = TestPacket {
                        ctx: crate::PacketContext::dummy(),
                        timestamp,
                        ssrc: 0,
                        sequence_number: 1,
                        loss: 0,
                        mark: true,
                        payload_type: 0,
                    }
                    .write(&mut buf, last_pkt);
                    d.push_collect(&pkt);
                }
                let Some(Ok(Item::Video(frame))) = d.pull() else {
                    panic!(
                        "wrap_offset={wrap_offset}, first_pkt_len={first_pkt_len}: \
                         expected VideoFrame"
                    );
                };
                assert_eq_hex!(frame.data(), &PREFIXED_NALS);
            }
        }
    }

    /// Like `parse_annex_b_single_nal` but with `strip_inline_parameters` enabled.
    #[test]
    fn parse_annex_b_single_nal_strip() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d =
            super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=640033"))
                .unwrap();
        d.set_frame_format(crate::codec::FrameFormat::MP4);
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        {
            let pkt = TestPacket {
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, ANNEX_B_NALS);
            d.push_collect(&pkt);
        }
        let Some(Ok(Item::Video(frame))) = d.pull() else {
            panic!();
        };
        assert_eq_hex!(frame.data(), &PREFIXED_NALS_STRIPPED);
    }

    /// Like `parse_annex_b_fu_a` but with `strip_inline_parameters` enabled.
    #[test]
    fn parse_annex_b_fu_a_strip() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        for first_pkt_len in 2..ANNEX_B_NALS.len() - 1 {
            for middle_pkt_len in [0, 1, 2, 3] {
                if first_pkt_len + middle_pkt_len >= ANNEX_B_NALS.len() {
                    continue;
                }
                let mut d = super::Depacketizer::new(
                    90_000,
                    Some("packetization-mode=1;profile-level-id=640033"),
                )
                .unwrap();
                d.set_frame_format(crate::codec::FrameFormat::MP4);
                let timestamp = crate::Timestamp {
                    timestamp: 0,
                    clock_rate: NonZeroU32::new(90_000).unwrap(),
                    start: 0,
                };
                let mut first_pkt = Vec::with_capacity(first_pkt_len + 1);
                first_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                first_pkt.push((ANNEX_B_NALS[0] & 0b0001_1111) | 0b1000_0000); // start
                first_pkt.extend_from_slice(&ANNEX_B_NALS[1..first_pkt_len]);
                {
                    let pkt = TestPacket {
                        ctx: crate::PacketContext::dummy(),
                        timestamp,
                        ssrc: 0,
                        sequence_number: 0,
                        loss: 0,
                        mark: false,
                        payload_type: 0,
                    }
                    .write(&mut buf, first_pkt);
                    d.push_collect(&pkt);
                }
                assert_eq!(d.pull(), None);
                if middle_pkt_len > 0 {
                    let mut middle_pkt = Vec::with_capacity(middle_pkt_len + 2);
                    middle_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                    middle_pkt.push(ANNEX_B_NALS[0] & 0b0001_1111); // continuation
                    middle_pkt.extend_from_slice(
                        &ANNEX_B_NALS[first_pkt_len..first_pkt_len + middle_pkt_len],
                    );
                    {
                        let pkt = TestPacket {
                            ctx: crate::PacketContext::dummy(),
                            timestamp,
                            ssrc: 0,
                            sequence_number: 1,
                            loss: 0,
                            mark: false,
                            payload_type: 0,
                        }
                        .write(&mut buf, middle_pkt);
                        d.push_collect(&pkt);
                    }
                    assert_eq!(d.pull(), None);
                }
                let mut last_pkt =
                    Vec::with_capacity(ANNEX_B_NALS.len() - first_pkt_len - middle_pkt_len + 2);
                last_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                last_pkt.push((ANNEX_B_NALS[0] & 0b0001_1111) | 0b0100_0000); // end
                last_pkt.extend_from_slice(&ANNEX_B_NALS[first_pkt_len + middle_pkt_len..]);
                {
                    let pkt = TestPacket {
                        ctx: crate::PacketContext::dummy(),
                        timestamp,
                        ssrc: 0,
                        sequence_number: 2,
                        loss: 0,
                        mark: true,
                        payload_type: 0,
                    }
                    .write(&mut buf, last_pkt);
                    d.push_collect(&pkt);
                }
                let Some(Ok(Item::Video(frame))) = d.pull() else {
                    panic!();
                };
                assert_eq_hex!(frame.data(), &PREFIXED_NALS_STRIPPED);
            }
        }
    }

    /// Like `parse_annex_b_single_nal` but with `FrameFormat::SIMPLE` (Annex B framing,
    /// parameter sets prepended on each key frame).
    #[test]
    fn parse_annex_b_single_nal_simple() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d =
            super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=640033"))
                .unwrap();
        d.set_frame_format(crate::codec::FrameFormat::SIMPLE);
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        {
            let pkt = TestPacket {
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, ANNEX_B_NALS);
            d.push_collect(&pkt);
        }
        let Some(Ok(Item::Video(frame))) = d.pull() else {
            panic!();
        };
        assert_eq_hex!(frame.data(), &ANNEX_B_NALS_SIMPLE);
    }

    #[test]
    fn allow_inconsistent_headers_between_fu_a() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, Some("profile-level-id=TQAf;packetization-mode=1;sprop-parameter-sets=J00AH+dAKALdgKUFBQXwAAADABAAAAMCiwEAAtxoAAIlUX//AoA=,KO48gA==")).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        {
            let pkt = TestPacket {
                // FU-A start fragment
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x3c\x81start of non-idr");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);

        {
            let pkt = TestPacket {
                // FU-A packet, end.
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x3c\x47a wild sps appeared");
            d.push_collect(&pkt);
        }
        // assert!(push_result.is_err());
        let Some(Ok(Item::Video(frame))) = d.pull() else {
            panic!();
        };
        assert_eq_hex!(
            frame.data(),
            &b"\x00\x00\x00\x24\x21start of non-idra wild sps appeared"
        );
        assert!(d.seen_inconsistent_fu_a_nal_hdr);
    }

    /// Tests that a FU-A with both S and E bits set is treated as a complete NAL
    /// rather than rejected. RFC 6184 section 5.8 forbids this, but some cameras
    /// send it anyway for small NALs.
    #[test]
    fn single_fragment_fu_a() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA")).unwrap();
        d.set_frame_format(crate::codec::FrameFormat {
            parameter_set_insertion: crate::codec::ParameterSetInsertion::Never,
            ..Default::default()
        });
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        assert!(!d.seen_single_fragment_fu_a);
        // FU-A with S=1 E=1 type=1 (non-IDR slice) — FU header 0xc1,
        // as observed in the wild.
        // FU indicator \x7c = F=0 NRI=3 type=28.
        let pkt = TestPacket {
            ctx: crate::PacketContext::dummy(),
            timestamp,
            ssrc: 0,
            sequence_number: 0,
            loss: 0,
            mark: true,
            payload_type: 0,
        }
        .write(&mut buf, *b"\x7c\xc1small nal");
        d.push_collect(&pkt);
        assert!(d.seen_single_fragment_fu_a);
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            o => panic!("unexpected pull result: {o:?}"),
        };
        // Reconstructed NAL: NRI=3 (from indicator) | type=1 (from FU hdr)
        // = 0x61, then payload. Length = 1 + 9 = 10 = 0x0a.
        assert_eq_hex!(frame.data(), b"\x00\x00\x00\x0a\x61small nal");
    }

    /// Tests that empty FU-A fragments (no payload bytes after the 2-byte header) are
    /// accepted and ignored, as some cameras send them.
    #[test]
    fn empty_fragment() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA")).unwrap();
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
                // FU-A packet (non-IDR slice, type 1), start (with data).
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x7c\x81start, ");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU-A packet, middle (empty payload after header).
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x7c\x01");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = TestPacket {
                // FU-A packet, end (with data).
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x7c\x41end");
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            _ => panic!(),
        };
        assert_eq_hex!(frame.data(), b"\x00\x00\x00\x0b\x61start, end");
    }

    /// Tests the `process_annex_b` function in isolation.
    #[test]
    fn annex_b_parsing() {
        init_logging();

        // Essentially empty inputs.
        process_annex_b(vec![], |_| panic!()).unwrap();
        process_annex_b(vec![0x00], |_| panic!()).unwrap();
        process_annex_b(vec![0x00, 0x00, 0x01], |_| panic!()).unwrap();
        process_annex_b(vec![0x00, 0x00, 0x00, 0x01], |_| panic!()).unwrap();

        // Single NAL unit.
        let mut nals: Vec<Bytes> = vec![];
        process_annex_b(vec![1, 2, 3, 4], |nal| {
            nals.push(nal);
            Ok(())
        })
        .unwrap();
        assert_eq_hexes!(nals, [Bytes::from_static(&[1, 2, 3, 4])]);
        nals.clear();
        process_annex_b(vec![0, 0, 1, 1, 2, 3, 4], |nal| {
            nals.push(nal);
            Ok(())
        })
        .unwrap();
        assert_eq_hexes!(nals, [Bytes::from_static(&[1, 2, 3, 4])]);
        nals.clear();
        process_annex_b(vec![1, 2, 3, 4, 0, 0, 1], |nal| {
            nals.push(nal);
            Ok(())
        })
        .unwrap();
        assert_eq_hexes!(nals, [Bytes::from_static(&[1, 2, 3, 4])]);

        // Error path.
        assert_eq!(
            process_annex_b(vec![1, 2, 3, 4, 0, 0, 1], |_| { Err("asdf".into()) }),
            Err("asdf".into()),
        );

        // Multiple NAL units.
        nals.clear();
        process_annex_b(vec![0, 0, 1, 1, 0, 0, 1, 2, 3, 4], |nal| {
            nals.push(nal);
            Ok(())
        })
        .unwrap();
        assert_eq_hexes!(
            nals,
            [Bytes::from_static(&[1]), Bytes::from_static(&[2, 3, 4])]
        );
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
                // FU-A packet, start.
                ctx: crate::PacketContext::dummy(),
                timestamp: timestamp0,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x7c\x86fu-a start, ");
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
                // plain non-IDR slice packet.
                ctx: crate::PacketContext::dummy(),
                timestamp: timestamp1,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .write(&mut buf, *b"\x01plain");
            d.push_collect(&pkt);
        }
        match d.pull() {
            Some(Err(e)) => assert_eq!(
                e,
                "timestamp changed from 0 (mod-2^32: 0), npt 0.000 to 1 (mod-2^32: 1), npt 0.000 in the middle of a fragmented NAL"
            ),
            _ => panic!(),
        }
        let Some(Ok(Item::Video(f))) = d.pull() else {
            panic!()
        };
        assert_eq_hex!(f.data(), b"\x00\x00\x00\x06\x01plain");
        assert_eq!(d.pull(), None);
    }

    /// Test that a SEI NAL with the mark bit set doesn't end an access unit.
    ///
    /// The LV-IP22IR40DVBL camera (and others using the same firmware, which
    /// identifies itself as `H264DVR 1.0`) sends SPS, PPS, and SEI as
    /// individual RTP packets each with the mark bit set, all at the same
    /// timestamp as the following IDR slice. The SEI contains a single
    /// reserved message (payload type 229). Per H.264 section 7.4.1.2.3,
    /// SEI NAL units precede the primary coded picture, so they should not
    /// end an access unit.
    ///
    /// See <https://github.com/scottlamb/moonfire-nvr/issues/352>.
    #[test]
    fn depacketize_sei_with_mark() {
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = super::Depacketizer::new(
            90_000,
            Some(
                "packetization-mode=1;profile-level-id=4d002a;\
                  sprop-parameter-sets=Z00AKpWoHgCJ+WEAAAMAAQAAAwAyhA==,aO48gA==",
            ),
        )
        .unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };

        // SPS with (incorrect) mark.
        {
            let pkt = TestPacket {
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 96,
            }
            .write(
                &mut buf,
                *b"\x67\x4d\x00\x2a\x95\xa8\x1e\x00\x89\xf9\x61\
                       \x00\x00\x03\x00\x01\x00\x00\x03\x00\x32\x84",
            );
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);

        // PPS with (incorrect) mark.
        {
            let pkt = TestPacket {
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: true,
                payload_type: 96,
            }
            .write(&mut buf, *b"\x68\xee\x3c\x80");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);

        // SEI (reserved payload type 229) with (incorrect) mark.
        {
            let pkt = TestPacket {
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 96,
            }
            .write(&mut buf, *b"\x06\xe5\x01\xa7\x80");
            d.push_collect(&pkt);
        }
        assert_eq!(d.pull(), None);

        // IDR slice with mark (correct this time).
        {
            let pkt = TestPacket {
                ctx: crate::PacketContext::dummy(),
                timestamp,
                ssrc: 0,
                sequence_number: 3,
                loss: 0,
                mark: true,
                payload_type: 96,
            }
            .write(&mut buf, *b"\x65slice");
            d.push_collect(&pkt);
        }
        let frame = match d.pull() {
            Some(Ok(Item::Video(frame))) => frame,
            o => panic!("unexpected pull result {o:#?}"),
        };
        assert_eq_hex!(
            frame.data(),
            b"\x00\x00\x00\x16\x67\x4d\x00\x2a\x95\xa8\x1e\x00\x89\xf9\x61\
              \x00\x00\x03\x00\x01\x00\x00\x03\x00\x32\x84\
              \x00\x00\x00\x04\x68\xee\x3c\x80\
              \x00\x00\x00\x05\x06\xe5\x01\xa7\x80\
              \x00\x00\x00\x06\x65slice"
        );
        assert!(frame.is_random_access_point());
        assert_eq!(d.pull(), None);
    }

    /// Helper: writes payload into `buf`, then pushes to depacketizer with a handler.
    #[allow(clippy::too_many_arguments)]
    fn push_events(
        d: &mut Depacketizer<crate::PacketContext>,
        buf: &mut MarkBuf,
        sequence_number: u16,
        timestamp: i64,
        mark: bool,
        loss: u16,
        payload: &[u8],
        h: &mut crate::codec::events::testutil::Recorder,
    ) {
        let meta = crate::rtp::ReceivedPacketMeta {
            ctx: crate::PacketContext::dummy(),
            timestamp: crate::Timestamp {
                timestamp,
                clock_rate: NonZeroU32::new(90_000).unwrap(),
                start: 0,
            },
            ssrc: 0,
            sequence_number,
            mark,
            continuity: crate::rtp::Continuity::from_loss(loss),
        };
        let pos = buf.end();
        buf.extend(payload);
        buf.advance_unparsed(buf.end());
        let pkt = ReceivedPacketRef::new(meta, buf, pos, payload.len() as u16);
        // As `crate::codec::VideoDepacketizer::push` does.
        crate::codec::report_packet_loss(&pkt, |l| {
            crate::codec::VideoHandler::<crate::PacketContext>::loss(h, l)
        });
        d.push(&pkt, h)
    }

    const EVENTS_FMTP: &str = "packetization-mode=1;profile-level-id=4d002a;\
                               sprop-parameter-sets=Z00AKpWoHgCJ+WEAAAMAAQAAAwAyhA==,aO48gA==";

    #[test]
    fn events_accumulate() {
        use crate::codec::events::testutil::{Event, Recorder, hex};
        use crate::codec::{Accumulate, Position};
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = Depacketizer::new(90_000, Some(EVENTS_FMTP)).unwrap();
        let mut h = Recorder::new(Accumulate::Yes);
        push_events(&mut d, &mut buf, 0, 0, false, 0, b"\x06plain", &mut h);
        push_events(
            &mut d,
            &mut buf,
            1,
            0,
            false,
            0,
            b"\x7c\x85fu-a start, ",
            &mut h,
        );
        push_events(&mut d, &mut buf, 2, 0, true, 0, b"\x7c\x45fu-a end", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::FrameStart {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                },
                Event::Data(Position::Complete, hex(b"\x06plain")),
                Event::Data(Position::Start, hex(b"\x65fu-a start, ")),
                Event::Data(Position::End, hex(b"fu-a end")),
                Event::FrameEnd {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                    data: Some(hex(
                        b"\x00\x00\x00\x06\x06plain\x00\x00\x00\x15\x65fu-a start, fu-a end"
                    )),
                },
            ]
        );

        // A disposable, non-IDR frame ended by a timestamp change.
        push_events(&mut d, &mut buf, 3, 1, false, 0, b"\x01slice", &mut h);
        push_events(&mut d, &mut buf, 4, 2, false, 0, b"\x01next", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::FrameStart {
                    is_random_access_point: false,
                    is_disposable: true,
                    has_new_parameters: false,
                },
                Event::Data(Position::Complete, hex(b"\x01slice")),
                Event::FrameEnd {
                    is_random_access_point: false,
                    is_disposable: true,
                    has_new_parameters: false,
                    data: Some(hex(b"\x00\x00\x00\x06\x01slice")),
                },
                // The next frame starts streaming immediately.
                Event::FrameStart {
                    is_random_access_point: false,
                    is_disposable: true,
                    has_new_parameters: false,
                },
                Event::Data(Position::Complete, hex(b"\x01next")),
            ]
        );
    }

    #[test]
    fn events_no_accumulate() {
        use crate::codec::events::testutil::{Event, Recorder, hex};
        use crate::codec::{Accumulate, Position};
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = Depacketizer::new(90_000, Some(EVENTS_FMTP)).unwrap();
        let mut h = Recorder::new(Accumulate::No);
        push_events(&mut d, &mut buf, 0, 0, true, 0, b"\x65slice", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::FrameStart {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                },
                Event::Data(Position::Complete, hex(b"\x65slice")),
                Event::FrameEnd {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                    data: None,
                },
            ]
        );
    }

    #[test]
    fn events_fu_a_interrupted_by_timestamp_change() {
        use crate::codec::events::testutil::{Event, Recorder, hex};
        use crate::codec::{Accumulate, LossReason, Position};
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = Depacketizer::new(90_000, Some(EVENTS_FMTP)).unwrap();
        let mut h = Recorder::new(Accumulate::Yes);
        push_events(&mut d, &mut buf, 0, 0, false, 0, b"\x7c\x85start", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::FrameStart {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                },
                Event::Data(Position::Start, hex(b"\x65start")),
            ]
        );
        push_events(&mut d, &mut buf, 1, 1, true, 0, b"\x41slice", &mut h);
        let events = h.take();
        assert!(
            matches!(&events[..], [Event::Loss(LossReason::Corrupt { .. }), ..]),
            "{events:#?}"
        );
        assert_eq!(
            events[1..],
            [
                Event::FrameStart {
                    is_random_access_point: false,
                    is_disposable: false,
                    has_new_parameters: false,
                },
                Event::Data(Position::Complete, hex(b"\x41slice")),
                Event::FrameEnd {
                    is_random_access_point: false,
                    is_disposable: false,
                    has_new_parameters: false,
                    data: Some(hex(b"\x00\x00\x00\x06\x41slice")),
                },
            ]
        );
    }

    /// Multi-slice pictures sent as single-NAL packets stream per packet;
    /// earlier non-VCL NALs are held until the first slice.
    #[test]
    fn events_stream_single_nal_slices() {
        use crate::codec::events::testutil::{Event, Recorder, hex};
        use crate::codec::{Accumulate, Position};
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = Depacketizer::new(90_000, Some(EVENTS_FMTP)).unwrap();
        let mut h = Recorder::new(Accumulate::Yes);
        push_events(&mut d, &mut buf, 0, 0, false, 0, b"\x06sei", &mut h);
        assert_eq!(h.take(), vec![]);
        push_events(&mut d, &mut buf, 1, 0, false, 0, b"\x65slice 1", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::FrameStart {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                },
                Event::Data(Position::Complete, hex(b"\x06sei")),
                Event::Data(Position::Complete, hex(b"\x65slice 1")),
            ]
        );
        push_events(&mut d, &mut buf, 2, 0, true, 0, b"\x65slice 2", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::Data(Position::Complete, hex(b"\x65slice 2")),
                Event::FrameEnd {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                    data: Some(hex(b"\x00\x00\x00\x04\x06sei\
                          \x00\x00\x00\x08\x65slice 1\
                          \x00\x00\x00\x08\x65slice 2")),
                },
            ]
        );
    }

    /// A slice within a STAP-A starts the frame; parameter sets are omitted from `data`.
    #[test]
    fn events_stream_stap_a() {
        use crate::codec::events::testutil::{Event, Recorder, hex};
        use crate::codec::{Accumulate, Position};
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = Depacketizer::new(90_000, Some(EVENTS_FMTP)).unwrap();
        let mut h = Recorder::new(Accumulate::No);

        // STAP-A with the same SPS and PPS as in `EVENTS_FMTP`, then a slice.
        let mut stap_a = vec![0x18];
        for nal in [
            &b"\x67\x4d\x00\x2a\x95\xa8\x1e\x00\x89\xf9\x61\x00\x00\x03\x00\x01\x00\x00\x03\x00\x32\x84"[..],
            b"\x68\xee\x3c\x80",
            b"\x65slice 1",
        ] {
            stap_a.extend_from_slice(&(nal.len() as u16).to_be_bytes());
            stap_a.extend_from_slice(nal);
        }
        push_events(&mut d, &mut buf, 0, 0, false, 0, &stap_a, &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::FrameStart {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                },
                Event::Data(Position::Complete, hex(b"\x65slice 1")),
            ]
        );
        assert!(d.mark.is_none(), "data should be released once delivered");
        push_events(&mut d, &mut buf, 1, 0, true, 0, b"\x65slice 2", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::Data(Position::Complete, hex(b"\x65slice 2")),
                Event::FrameEnd {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                    data: None,
                },
            ]
        );
    }

    /// New parameters are available at `frame_start` but not committed until `frame_end`.
    #[test]
    fn events_new_parameters() {
        use crate::codec::events::testutil::{Event, Recorder, hex};
        use crate::codec::{Accumulate, Position};
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = Depacketizer::new(90_000, None).unwrap();
        let mut h = Recorder::new(Accumulate::Yes);
        push_events(
            &mut d,
            &mut buf,
            0,
            0,
            false,
            0,
            b"\x67\x4d\x00\x2a\x95\xa8\x1e\x00\x89\xf9\x61\x00\x00\x03\x00\x01\x00\x00\x03\x00\x32\x84",
            &mut h,
        );
        push_events(
            &mut d,
            &mut buf,
            1,
            0,
            false,
            0,
            b"\x68\xee\x3c\x80",
            &mut h,
        );
        push_events(&mut d, &mut buf, 2, 0, false, 0, b"\x7c\x85start", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::FrameStart {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: true,
                },
                Event::Data(Position::Start, hex(b"\x65start")),
            ]
        );
        assert!(d.parameters().is_none());
        push_events(&mut d, &mut buf, 3, 0, true, 0, b"\x7c\x45 end", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::Data(Position::End, hex(b" end")),
                Event::FrameEnd {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: true,
                    data: Some(hex(b"\x00\x00\x00\x0a\x65start end")),
                },
            ]
        );
        assert!(d.parameters().is_some());
    }

    /// The `can_end_au` workaround for cameras which set MARK on SEI NALs
    /// must apply after streaming has begun.
    #[test]
    fn events_stream_sei_with_mark() {
        use crate::codec::events::testutil::{Event, Recorder, hex};
        use crate::codec::{Accumulate, Position};
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = Depacketizer::new(90_000, Some(EVENTS_FMTP)).unwrap();
        let mut h = Recorder::new(Accumulate::Yes);
        push_events(&mut d, &mut buf, 0, 0, false, 0, b"\x65slice 1", &mut h);
        push_events(&mut d, &mut buf, 1, 0, true, 0, b"\x06sei", &mut h);
        push_events(&mut d, &mut buf, 2, 0, true, 0, b"\x65slice 2", &mut h);
        let events = h.take();
        assert_eq!(
            events,
            vec![
                Event::FrameStart {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                },
                Event::Data(Position::Complete, hex(b"\x65slice 1")),
                Event::Data(Position::Complete, hex(b"\x06sei")),
                Event::Data(Position::Complete, hex(b"\x65slice 2")),
                Event::FrameEnd {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                    data: Some(hex(b"\x00\x00\x00\x08\x65slice 1\
                          \x00\x00\x00\x04\x06sei\
                          \x00\x00\x00\x08\x65slice 2")),
                },
            ]
        );
    }

    /// Under `Accumulate::No`, a fragmented NAL occupies about one packet of buffer.
    #[test]
    fn events_stream_releases_buffer() {
        use crate::codec::events::testutil::{Event, Recorder, hex};
        use crate::codec::{Accumulate, Position};
        init_logging();
        let mut buf = MarkBuf::new(64);
        let mut d = Depacketizer::new(90_000, Some(EVENTS_FMTP)).unwrap();
        let mut h = Recorder::new(Accumulate::No);
        push_events(&mut d, &mut buf, 0, 0, false, 0, b"\x7c\x85start", &mut h);
        for i in 1..100 {
            push_events(
                &mut d,
                &mut buf,
                i,
                0,
                false,
                0,
                b"\x7c\x05 middle.......",
                &mut h,
            );
            assert!(d.mark.is_none());
            assert_eq!(
                h.take().last(),
                Some(&Event::Data(Position::Middle, hex(b" middle.......")))
            );
        }
        push_events(&mut d, &mut buf, 100, 0, true, 0, b"\x7c\x45 end", &mut h);
        assert_eq!(buf.capacity(), 64, "buffer should not have grown");
        assert_eq!(
            h.take(),
            vec![
                Event::Data(Position::End, hex(b" end")),
                Event::FrameEnd {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                    data: None,
                },
            ]
        );
    }

    /// Packet loss mid-frame abandons it with a `loss` event.
    #[test]
    fn events_loss_mid_frame() {
        use crate::codec::events::testutil::{Event, Recorder, hex};
        use crate::codec::{Accumulate, LossReason, Position};
        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = Depacketizer::new(90_000, Some(EVENTS_FMTP)).unwrap();
        let mut h = Recorder::new(Accumulate::Yes);
        push_events(&mut d, &mut buf, 0, 0, false, 0, b"\x7c\x85start", &mut h);
        push_events(&mut d, &mut buf, 2, 0, true, 1, b"\x7c\x45 end", &mut h);
        push_events(&mut d, &mut buf, 3, 1, true, 0, b"\x41slice", &mut h);
        assert_eq!(
            h.take(),
            vec![
                Event::FrameStart {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                },
                Event::Data(Position::Start, hex(b"\x65start")),
                Event::Loss(LossReason::PacketLoss { packets: 1 }),
                Event::FrameStart {
                    is_random_access_point: false,
                    is_disposable: false,
                    has_new_parameters: false,
                },
                Event::Data(Position::Complete, hex(b"\x41slice")),
                Event::FrameEnd {
                    is_random_access_point: false,
                    is_disposable: false,
                    has_new_parameters: false,
                    data: Some(hex(b"\x00\x00\x00\x06\x41slice")),
                },
            ]
        );
    }

    /// `VideoFrameStart::set_h264_parameters` overrides parameters, surviving
    /// repeats of the in-band parameters it replaced.
    #[test]
    fn set_h264_parameters() {
        use crate::codec::{Accumulate, FrameFormat, VideoFrameEnd, VideoFrameStart, VideoHandler};
        const SPS_A: &[u8] = b"\x67\x4d\x00\x2a\x95\xa8\x1e\x00\x89\xf9\x61\x00\x00\x03\x00\x01\x00\x00\x03\x00\x32\x84";
        const PPS_A: &[u8] = b"\x68\xee\x3c\x80";
        const SPS_B: &[u8] = b"\x67\x64\x00\x1e\xac\x2c\x6a\x82\xc0\xf6\x9b\x82\x80\x82\xa0\x00\x00\x03\x00\x20\x00\x00\x03\x03\xd0\x80";
        const PPS_B: &[u8] = b"\x68\xee\x31\xb2\x1b";

        /// Records `(has_new_parameters at start, SPS at start, has_new_parameters at end, data)`.
        #[derive(Default)]
        struct Overrider {
            overridden: bool,
            frames: Vec<(bool, Vec<u8>, bool, Vec<u8>)>,
            start: Option<(bool, Vec<u8>)>,
        }
        fn sps(p: Option<&crate::codec::VideoParameters>) -> Vec<u8> {
            match p.unwrap().codec_params() {
                crate::codec::VideoParametersCodec::H264 { sps, .. } => sps.to_vec(),
                _ => unreachable!(),
            }
        }
        impl VideoHandler<crate::PacketContext> for Overrider {
            fn frame_start(
                &mut self,
                fs: &mut VideoFrameStart<'_, crate::PacketContext>,
            ) -> Accumulate {
                if !self.overridden {
                    fs.set_h264_parameters(SPS_B, PPS_B).unwrap();
                    self.overridden = true;
                }
                self.start = Some((fs.has_new_parameters(), sps(fs.parameters())));
                Accumulate::Yes
            }
            fn frame_end(&mut self, fe: &mut VideoFrameEnd<'_, crate::PacketContext>) {
                let (start_new, start_sps) = self.start.take().unwrap();
                let data = fe.complete_frame(FrameFormat::default()).unwrap();
                self.frames
                    .push((start_new, start_sps, fe.has_new_parameters(), data));
            }
        }

        init_logging();
        let mut buf = MarkBuf::new(65536);
        let mut d = Depacketizer::new(90_000, Some(EVENTS_FMTP)).unwrap();
        let mut h = Overrider::default();
        let mut push = |d: &mut Depacketizer<_>, seq: u16, ts: i64, mark: bool, payload: &[u8]| {
            let meta = crate::rtp::ReceivedPacketMeta {
                ctx: crate::PacketContext::dummy(),
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
        let mut expected_frame = Vec::new();
        for nal in [SPS_B, PPS_B, b"\x65slice"] {
            expected_frame.extend_from_slice(&(nal.len() as u32).to_be_bytes());
            expected_frame.extend_from_slice(nal);
        }
        for (i, ts) in [0, 1].into_iter().enumerate() {
            let seq = 3 * i as u16;
            push(&mut d, seq, ts, false, SPS_A);
            push(&mut d, seq + 1, ts, false, PPS_A);
            push(&mut d, seq + 2, ts, true, b"\x65slice");
        }
        assert_eq!(
            h.frames,
            vec![
                // overridden
                (true, SPS_B.to_vec(), true, expected_frame.clone()),
                // in-band SPS_A doesn't undo override
                (false, SPS_B.to_vec(), false, expected_frame),
            ]
        );
        let Some(v) = d.parameters() else { panic!() };
        let crate::codec::VideoParametersCodec::H264 { sps, .. } = v.codec_params() else {
            panic!()
        };
        assert_eq!(&sps[..], SPS_B);
    }
}

#[cfg(test)]
mod packetizer_tests {
    use std::num::NonZeroU32;

    use super::*;
    use crate::codec::{
        FrameInfo, PacketizeOptions, ParameterSetInsertion, Payload, PayloadSink, Position,
    };
    use crate::testutil::HexDebug;

    const SPS: &[u8] =
        b"\x67\x4d\x00\x2a\x95\xa8\x1e\x00\x89\xf9\x61\x00\x00\x03\x00\x01\x00\x00\x03\x00\x32\x84";
    const PPS: &[u8] = b"\x68\xee\x3c\x80";

    /// A payload as recorded by `Recorder`: `(mark, frame_start, data)`.
    type Recorded = (bool, bool, HexDebug);

    #[derive(Default)]
    struct Recorder {
        payloads: Vec<Recorded>,
        discontinuities: usize,
        congested: bool,
    }

    impl Recorder {
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

        fn discontinuity(&mut self) {
            self.discontinuities += 1;
        }

        fn congested(&self) -> bool {
            self.congested
        }
    }

    fn rec(mark: bool, frame_start: bool, data: &[u8]) -> Recorded {
        (mark, frame_start, HexDebug(data.to_vec()))
    }

    fn packetizer(
        max_payload_size: u16,
        parameter_set_insertion: ParameterSetInsertion,
    ) -> Packetizer {
        let params = parameters_from_sps_and_pps(SPS, PPS).unwrap();
        Packetizer::new(
            &params,
            PacketizeOptions::default()
                .max_payload_size(max_payload_size)
                .parameter_set_insertion(parameter_set_insertion),
        )
        .unwrap()
    }

    fn frame(ts: i64, is_random_access_point: bool) -> FrameInfo {
        FrameInfo::new(crate::Timestamp::new(ts, NonZeroU32::new(90_000).unwrap(), 0).unwrap())
            .with_random_access_point(is_random_access_point)
    }

    /// Parameter sets and small NALs are aggregated into a STAP-A.
    #[test]
    fn stap_a() {
        let mut p = packetizer(1400, ParameterSetInsertion::EachKeyFrame);
        let mut r = Recorder::default();
        p.start_frame(frame(0, true), &mut r);
        p.push_unit(Position::Complete, &[b"\x06sei"], &mut r);
        p.push_unit(Position::Complete, &[b"\x65", b"idr"], &mut r);
        assert_eq!(r.take(), []); // held until the frame's end.
        p.end_frame(&mut r);
        let mut expected = vec![0x78]; // STAP-A with NRI of the SPS.
        for nal in [SPS, PPS, b"\x06sei", b"\x65idr"] {
            expected.extend_from_slice(&(nal.len() as u16).to_be_bytes());
            expected.extend_from_slice(nal);
        }
        assert_eq!(r.take(), [rec(true, true, &expected)]);

        // No parameter sets for a non-key frame; a lone NAL goes in a single NAL unit packet.
        p.start_frame(frame(1, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x41p"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, true, b"\x41p")]);
    }

    /// Fragments are delivered as soon as they're known not to be last,
    /// referencing the input; the final fragment is held for the marker bit.
    #[test]
    fn fu_a_streaming() {
        let mut p = packetizer(6, ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Start, &[b"\x41abc"], &mut r);
        assert_eq!(r.take(), []); // might still fit in a single NAL unit packet.
        p.push_unit(Position::Middle, &[b"defghij"], &mut r);
        assert_eq!(
            r.take(),
            [
                rec(false, true, b"\x5c\x81abcd"),
                rec(false, false, b"\x5c\x01efgh")
            ]
        );
        p.push_unit(Position::End, &[b""], &mut r);
        assert_eq!(r.take(), []);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, false, b"\x5c\x41ij")]);
    }

    /// A NAL which exactly fits isn't fragmented; one byte more is.
    #[test]
    fn fu_a_boundary() {
        let mut p = packetizer(4, ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x41abc"], &mut r);
        p.push_unit(Position::Complete, &[b"\x41abcd"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(
            r.take(),
            [
                rec(false, true, b"\x41abc"),
                rec(false, false, b"\x5c\x81ab"),
                rec(true, false, b"\x5c\x41cd"),
            ]
        );
    }

    /// NAL types which would be mistaken for aggregation or fragmentation
    /// packets are discarded by `push_unit`, including any continuation chunks.
    #[test]
    fn invalid_nal_type() {
        let mut p = packetizer(100, ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x7cx"], &mut r); // type 28 (FU-A)
        p.push_unit(Position::Start, &[b"\x00x"], &mut r); // type 0
        p.push_unit(Position::End, &[b"yz"], &mut r);
        p.push_unit(Position::Complete, &[b"\x41p"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, true, b"\x41p")]);
    }

    /// `push_frame` rejects invalid NAL types without delivering anything.
    #[test]
    fn push_frame_invalid_nal_type() {
        let mut p = packetizer(100, ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        let e = p
            .push_frame(
                frame(0, false),
                crate::codec::h26x::Framing::FourByteLength,
                b"\x00\x00\x00\x02\x41p\x00\x00\x00\x02\x7cx",
                &mut r,
            )
            .unwrap_err();
        assert!(e.to_string().contains("invalid type"), "{e}");
        assert_eq!(r.take(), []);
    }

    fn disposable(mut f: FrameInfo) -> FrameInfo {
        f.is_disposable = true;
        f
    }

    /// Congestion mid-fragment truncates the NAL: the fragment which would
    /// have been delivered next becomes its last, with the F bit set, and
    /// ends the frame. Frames are then dropped until a random access point.
    #[test]
    fn throttle_fu_a() {
        let mut p = packetizer(6, ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Start, &[b"\x41abc"], &mut r);
        p.push_unit(Position::Middle, &[b"defghij"], &mut r);
        assert_eq!(
            r.take(),
            [
                rec(false, true, b"\x5c\x81abcd"),
                rec(false, false, b"\x5c\x01efgh")
            ]
        );
        r.congested = true;
        p.push_unit(Position::Middle, &[b"klmn"], &mut r);
        p.push_unit(Position::End, &[b"op"], &mut r);
        p.push_unit(Position::Complete, &[b"\x41q"], &mut r);
        assert_eq!(r.take(), []);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, false, b"\xdc\x41ijkl")]);

        // Uncongested, but awaiting a random access point.
        r.congested = false;
        p.start_frame(frame(1, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x41r"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), []);
        p.start_frame(frame(2, true), &mut r);
        p.push_unit(Position::Complete, &[b"\x65s"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, true, b"\x65s")]);
        assert_eq!(r.discontinuities, 0);
    }

    /// Congestion before a NAL that isn't yet fragmenting truncates it to a
    /// single NAL unit packet.
    #[test]
    fn throttle_before_first_fragment() {
        let mut p = packetizer(4, ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Start, &[b"\x41ab"], &mut r);
        r.congested = true;
        p.push_unit(Position::End, &[b"cdef"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, true, b"\xc1abc")]);
    }

    /// Congestion at a NAL boundary truncates the next NAL to its header. A
    /// disposable frame's loss doesn't affect later frames.
    #[test]
    fn throttle_nal_boundary() {
        let mut p = packetizer(1400, ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        p.start_frame(disposable(frame(0, false)), &mut r);
        p.push_unit(Position::Complete, &[b"\x01a"], &mut r);
        r.congested = true;
        p.push_unit(Position::Start, &[b"\x01b"], &mut r);
        p.push_unit(Position::End, &[b"c"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(
            r.take(),
            [rec(false, true, b"\x01a"), rec(true, false, b"\x81")]
        );
        r.congested = false;
        p.start_frame(frame(1, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x41d"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, true, b"\x41d")]);
    }

    /// Congestion at a frame's start drops it entirely, and parameter sets
    /// are still inserted at the next frame sent.
    #[test]
    fn throttle_frame_start() {
        let mut p = packetizer(1400, ParameterSetInsertion::OnChange);
        let mut r = Recorder::default();
        p.set_parameters(&parameters_from_sps_and_pps(SPS, b"\x68\xee\x3c\x81").unwrap())
            .unwrap();
        r.congested = true;
        p.start_frame(frame(0, true), &mut r);
        p.push_unit(Position::Complete, &[b"\x65a"], &mut r);
        p.end_frame(&mut r);
        p.start_frame(disposable(frame(1, false)), &mut r);
        p.push_unit(Position::Complete, &[b"\x01b"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), []);
        r.congested = false;
        p.start_frame(frame(2, true), &mut r);
        p.push_unit(Position::Complete, &[b"\x65c"], &mut r);
        p.end_frame(&mut r);
        let r = r.take();
        assert_eq!(r.len(), 1);
        assert!(r[0].0 && r[0].1);
        assert_eq!(r[0].2.0[0] & 0x1f, 24, "STAP-A with parameter sets");
    }

    /// A discontinuity abandons the frame, dropping held data, then drops
    /// frames until the next random access point.
    #[test]
    fn discontinuity() {
        let mut p = packetizer(1400, ParameterSetInsertion::Never);
        let mut r = Recorder::default();
        p.start_frame(frame(0, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x41p"], &mut r);
        p.discontinuity(&mut r);
        p.end_frame(&mut r); // no-op after a discontinuity.
        assert_eq!(r.take(), []);
        assert_eq!(r.discontinuities, 1);
        p.start_frame(frame(1, false), &mut r);
        p.push_unit(Position::Complete, &[b"\x41q"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), []); // may depend on the lost data.
        p.start_frame(frame(2, true), &mut r);
        p.push_unit(Position::Complete, &[b"\x65r"], &mut r);
        p.end_frame(&mut r);
        assert_eq!(r.take(), [rec(true, true, b"\x65r")]);
    }

    /// Misuse of `push_unit` and `end_frame` is tolerated rather than panicking.
    #[test]
    fn misuse() {
        let mut p = packetizer(1400, ParameterSetInsertion::Never);
        let mut r = Recorder::default();

        // Outside a frame: discarded.
        p.push_unit(Position::Complete, &[b"\x41x"], &mut r);

        p.start_frame(frame(0, false), &mut r);

        // Continuing a unit which wasn't started: discarded.
        p.push_unit(Position::Middle, &[b"x"], &mut r);
        p.push_unit(Position::End, &[b"x"], &mut r);

        // Starting a unit while another is in progress ends the other.
        p.push_unit(Position::Start, &[b"\x41a"], &mut r);
        p.push_unit(Position::Start, &[b"\x41b"], &mut r);

        // Ending the frame mid-unit ends the unit.
        p.end_frame(&mut r);
        assert_eq!(
            r.take(),
            [rec(true, true, b"\x58\x00\x02\x41a\x00\x02\x41b")]
        );
    }

    /// Payloads carry their position within the frame, and the frame's
    /// properties.
    #[test]
    fn payload_metadata() {
        #[derive(Default)]
        struct Meta(Vec<(Position, bool, bool)>);
        impl PayloadSink for Meta {
            fn payload(&mut self, p: &Payload<'_>) {
                assert_eq!(p.mark(), p.position().is_last());
                self.0
                    .push((p.position(), p.is_random_access_point(), p.is_disposable()));
            }
        }
        let mut p = packetizer(4, ParameterSetInsertion::Never);
        let mut m = Meta::default();
        p.start_frame(frame(0, true), &mut m);
        p.push_unit(Position::Complete, &[b"\x65abcdef"], &mut m); // three FU-As.
        p.end_frame(&mut m);
        p.start_frame(frame(1, false).with_disposable(true), &mut m);
        p.push_unit(Position::Complete, &[b"\x01p"], &mut m);
        p.end_frame(&mut m);
        assert_eq!(
            m.0,
            [
                (Position::Start, true, false),
                (Position::Middle, true, false),
                (Position::End, true, false),
                (Position::Complete, false, true),
            ]
        );
    }

    /// The payload format is available from the parameters alone.
    #[test]
    fn payload_format_from_parameters() {
        let p = packetizer(1400, ParameterSetInsertion::Never);
        assert_eq!(p.parameters().payload_format(), Some(p.payload_format()));
    }

    /// `push_frame` splits Annex B data and takes over in-band parameter sets.
    #[test]
    fn push_frame_annex_b() {
        const SPS_B: &[u8] = b"\x67\x64\x00\x1e\xac\x2c\x6a\x82\xc0\xf6\x9b\x82\x80\x82\xa0\x00\x00\x03\x00\x20\x00\x00\x03\x03\xd0\x80";
        const PPS_B: &[u8] = b"\x68\xee\x31\xb2\x1b";
        let mut p = packetizer(1400, ParameterSetInsertion::OnChange);
        let mut r = Recorder::default();
        let mut data = Vec::new();
        for nal in [SPS_B, PPS_B, b"\x65idr"] {
            data.extend_from_slice(b"\x00\x00\x00\x01");
            data.extend_from_slice(nal);
        }
        data.extend_from_slice(b"\x00\x00"); // trailing_zero_8bits
        p.push_frame(
            frame(0, true),
            crate::codec::h26x::Framing::AnnexB,
            &data,
            &mut r,
        )
        .unwrap();
        let mut expected = vec![0x78];
        for nal in [SPS_B, PPS_B, b"\x65idr"] {
            expected.extend_from_slice(&(nal.len() as u16).to_be_bytes());
            expected.extend_from_slice(nal);
        }
        assert_eq!(r.take(), [rec(true, true, &expected)]);
        assert!(
            p.payload_format()
                .fmtp()
                .unwrap()
                .contains("profile-level-id=64001E")
        );

        // Repeated parameter sets aren't a change, so they aren't inserted.
        p.push_frame(
            frame(1, true),
            crate::codec::h26x::Framing::AnnexB,
            &data,
            &mut r,
        )
        .unwrap();
        assert_eq!(r.take(), [rec(true, true, b"\x65idr")]);

        assert!(
            p.push_frame(
                frame(2, false),
                crate::codec::h26x::Framing::AnnexB,
                b"\x41p",
                &mut r
            )
            .is_err()
        );
    }
}
