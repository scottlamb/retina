// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [H.264](https://www.itu.int/rec/T-REC-H.264-201906-I/en)-encoded video,
//! with RTP encoding as in [RFC 6184](https://tools.ietf.org/html/rfc6184).

use std::fmt::Write;
use std::{collections::VecDeque, convert::TryFrom};

use base64::Engine as _;
use bytes::{Buf, BufMut, Bytes, BytesMut};
use h264_reader::nal::sps::{SeqParameterSet, SpsError};
use h264_reader::nal::{NalHeader, UnitType};
use log::{debug, log_enabled, trace};

use crate::Error;
use crate::buf::{BufRange, Mark, MarkBuf, PacketRef};
use crate::codec::{AllPixelDimensions, DepacketizeError};
use crate::inputs::Input as _;
use crate::{
    Timestamp,
    codec::h26x::TolerantBitReader,
    rtp::{ReceivedPacket, ReceivedPacketBuilder},
};

use super::{CodecItem, VideoFrame, VideoParameters};

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
    framing: super::h26x::Framing,
) -> Result<VideoParameters, Error> {
    InternalParameters::parse_sps_and_pps(sps_nal, pps_nal, true, framing)
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
pub(crate) struct Depacketizer {
    input_state: DepacketizerInputState,

    /// Completed items ready to be pulled.
    pending: VecDeque<Result<VideoFrame, DepacketizeError>>,

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

    /// Output format controlling NAL framing and parameter set insertion.
    frame_format: super::FrameFormat,
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

    /// FU-A fragmentation unit state, if any.
    fu_a: Option<FuA>,

    /// RTP packets lost as this access unit was starting.
    loss: u16,

    same_ts_as_prev: bool,
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
            pending: VecDeque::with_capacity(1),
            mark: None,
            pieces: Vec::new(),
            nals: Vec::new(),
            parameters,
            seen_inconsistent_fu_a_nal_hdr: false,
            seen_single_fragment_fu_a: false,
            frame_format: Default::default(),
        })
    }

    /// Sets the frame format for output assembly.
    ///
    /// If existing parameters were parsed with a different framing, they are
    /// re-parsed to produce the correct `extra_data` format.
    pub(super) fn set_frame_format(&mut self, format: super::FrameFormat) {
        self.frame_format = format;

        // Re-parse existing parameters so extra_data matches the new framing.
        if let Some(ref ip) = self.parameters {
            // Re-parse is infallible here—these params were already successfully
            // parsed once—so unwrap via expect.
            self.parameters = Some(
                InternalParameters::parse_sps_and_pps(
                    &ip.sps_nal,
                    &ip.pps_nal,
                    ip.seen_extra_trailing_data,
                    format.h26x_framing,
                )
                .expect("re-parse of previously valid SPS/PPS should not fail"),
            );
        }
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

    pub(super) fn parameters(&self) -> Option<super::ParametersRef<'_>> {
        self.parameters
            .as_ref()
            .map(|p| super::ParametersRef::Video(&p.generic_parameters))
    }

    pub(super) fn push(&mut self, pkt: &PacketRef<'_>) -> Result<(), String> {
        let r = self.push_inner(pkt);

        // Several error paths within `push_inner` just use the `?` operator to bail out with
        // `input_state` at `New` when they encounter a problem mid-access unit. Restore
        // the invariant so the caller can try to recover after error.
        if !matches!(self.input_state, DepacketizerInputState::PreMark(_)) {
            self.discard_au();
        }
        r
    }

    fn push_inner(&mut self, pkt: &PacketRef<'_>) -> Result<(), String> {
        let meta = pkt.meta;
        let payload_pos = pkt.payload_pos();
        let payload_len = pkt.payload_len();
        let buf = pkt.buf();
        // Push shouldn't be called until pull is exhausted.
        if let Some(p) = self.pending.front() {
            panic!("push with data already pending: {p:?}");
        }

        let mut access_unit =
            match std::mem::replace(&mut self.input_state, DepacketizerInputState::New) {
                DepacketizerInputState::New => {
                    debug_assert!(self.nals.is_empty());
                    debug_assert!(self.pieces.is_empty());
                    AccessUnit::start(&meta, 0, false)
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
                        AccessUnit::start(&meta, 0, false)
                    } else if access_unit.timestamp.timestamp != meta.timestamp.timestamp {
                        if access_unit.fu_a.is_some() {
                            self.pending.push_back(Err(DepacketizeError {
                                pkt_ctx: meta.ctx,
                                ssrc: meta.ssrc,
                                sequence_number: meta.sequence_number,
                                description: format!(
                                "timestamp changed from {} to {} in the middle of a fragmented NAL",
                                access_unit.timestamp,
                                meta.timestamp),
                            }));
                            self.discard_au();
                            AccessUnit::start(&meta, 0, false)
                        } else {
                            match self.nals.last() {
                                Some(n) if can_end_au(n.hdr.nal_unit_type()) => {
                                    access_unit.end_ctx = meta.ctx;
                                    let f =
                                        self.finalize_access_unit(access_unit, "ts change", buf)?;
                                    self.pending.push_back(Ok(f));
                                    AccessUnit::start(&meta, 0, false)
                                }
                                Some(n) => {
                                    log::debug!(
                                        "Bogus mid-access unit timestamp change after {:?}",
                                        n.hdr
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
                    AccessUnit::start(&meta, loss, state_ts.timestamp == meta.timestamp.timestamp)
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
                    AccessUnit::start(&meta, pkts, false)
                }
            };

        let ctx = meta.ctx;
        let mark = meta.mark;
        let loss = meta.loss;
        let timestamp = meta.timestamp;

        if payload_len == 0 {
            return Err("Empty NAL".into());
        }

        // Pin the payload data in the ring buffer.
        if self.mark.is_none() {
            self.mark = Some(pkt.mark());
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
        self.input_state = if mark {
            match self.nals.last() {
                Some(n) if can_end_au(n.hdr.nal_unit_type()) => {
                    access_unit.end_ctx = ctx;
                    let f = self.finalize_access_unit(access_unit, "mark", buf)?;
                    self.pending.push_back(Ok(f));
                    DepacketizerInputState::PostMark { timestamp, loss: 0 }
                }
                Some(n) => {
                    log::debug!("Bogus mid-access unit mark on {:?}", n.hdr);
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

    pub(super) fn pull(&mut self) -> Option<Result<CodecItem, DepacketizeError>> {
        self.pending
            .pop_front()
            .map(|r| r.map(CodecItem::VideoFrame))
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

    fn finalize_access_unit(
        &mut self,
        au: AccessUnit,
        reason: &str,
        buf: &MarkBuf,
    ) -> Result<VideoFrame, String> {
        use super::{ParameterSetInsertion, h26x::Framing};

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
                UnitType::SeqParameterSet
                    if self
                        .parameters
                        .as_ref()
                        .map(|p| !nal_matches(&p.sps_nal[..], nal.hdr, nal_pieces, buf))
                        .unwrap_or(true) =>
                {
                    new_sps = Some(to_bytes(nal.hdr, nal.len, nal_pieces, buf));
                }
                UnitType::PicParameterSet
                    if self
                        .parameters
                        .as_ref()
                        .map(|p| !nal_matches(&p.pps_nal[..], nal.hdr, nal_pieces, buf))
                        .unwrap_or(true) =>
                {
                    new_pps = Some(to_bytes(nal.hdr, nal.len, nal_pieces, buf));
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
            // Always strip inline parameter sets; they're handled via
            // ParameterSetInsertion and the canonical copy in self.parameters.
            if !matches!(
                nal.hdr.nal_unit_type(),
                UnitType::SeqParameterSet | UnitType::PicParameterSet
            ) {
                retained_len += 4usize + crate::to_usize(nal.len);
            }
            piece_idx = next_piece_idx;
        }

        // Update parameters before building the frame, so prepended params
        // reflect the latest SPS/PPS.
        let has_new_parameters = match (
            new_sps.as_deref(),
            new_pps.as_deref(),
            self.parameters.as_ref(),
        ) {
            (Some(sps_nal), Some(pps_nal), old_ip) => {
                let seen_extra_trailing_data =
                    old_ip.map(|o| o.seen_extra_trailing_data).unwrap_or(false);
                // TODO: could map this to a RtpPacketError more accurately.
                self.parameters = Some(InternalParameters::parse_sps_and_pps(
                    sps_nal,
                    pps_nal,
                    seen_extra_trailing_data,
                    self.frame_format.h26x_framing,
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
                    self.frame_format.h26x_framing,
                )?);
                true
            }
            _ => false,
        };

        // Determine whether to prepend parameter sets.
        let prepend_params = is_random_access_point
            && match self.frame_format.parameter_set_insertion {
                ParameterSetInsertion::EachKeyFrame => true,
                ParameterSetInsertion::OnChange => has_new_parameters,
                ParameterSetInsertion::Never => false,
            };
        if prepend_params && let Some(ref p) = self.parameters {
            // 4-byte prefix + SPS NAL + 4-byte prefix + PPS NAL
            retained_len += 4 + p.sps_nal.len() + 4 + p.pps_nal.len();
        }

        let mut data = Vec::with_capacity(retained_len);

        // Prepend parameter sets if requested.
        if prepend_params && let Some(ref p) = self.parameters {
            for param_nal in [&p.sps_nal, &p.pps_nal] {
                let prefix = match self.frame_format.h26x_framing {
                    Framing::FourByteLength => (param_nal.len() as u32).to_be_bytes(),
                    Framing::AnnexB => super::h26x::ANNEX_B_START_CODE,
                };
                data.extend_from_slice(&prefix);
                data.extend_from_slice(param_nal);
            }
        }

        // Write non-parameter-set NALs with the configured framing.
        piece_idx = 0;
        for nal in &self.nals {
            let next_piece_idx = crate::to_usize(nal.next_piece_idx);
            let nal_pieces = &self.pieces[piece_idx..next_piece_idx];
            if !matches!(
                nal.hdr.nal_unit_type(),
                UnitType::SeqParameterSet | UnitType::PicParameterSet
            ) {
                let prefix = match self.frame_format.h26x_framing {
                    Framing::FourByteLength => nal.len.to_be_bytes(),
                    Framing::AnnexB => super::h26x::ANNEX_B_START_CODE,
                };
                data.extend_from_slice(&prefix);
                data.push(nal.hdr.into());
                let mut actual_len = 1usize;
                for piece in nal_pieces {
                    debug_assert!(piece.len > 0);
                    let (s1, s2) = buf.split(piece.pos, usize::from(piece.len)).slices();
                    data.extend_from_slice(s1);
                    data.extend_from_slice(s2);
                    actual_len += piece.len as usize;
                }
                debug_assert_eq!(crate::to_usize(nal.len), actual_len);
            }
            piece_idx = next_piece_idx;
        }
        debug_assert_eq!(retained_len, data.len());
        self.nals.clear();
        self.pieces.clear();
        self.mark = None;

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

impl AccessUnit {
    fn start(meta: &crate::rtp::PacketMeta, additional_loss: u16, same_ts_as_prev: bool) -> Self {
        AccessUnit {
            start_ctx: meta.ctx,
            end_ctx: meta.ctx,
            timestamp: meta.timestamp,
            stream_id: meta.stream_id,
            fu_a: None,

            // TODO: overflow?
            loss: meta.loss + additional_loss,
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
        Self::parse_sps_and_pps(
            &sps_nal,
            &pps_nal,
            false,
            super::h26x::Framing::FourByteLength,
        )
    }

    fn parse_sps_and_pps(
        sps_nal: &[u8],
        pps_nal: &[u8],
        mut seen_extra_trailing_data: bool,
        framing: super::h26x::Framing,
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
            log::warn!(
                "Ignoring trailing data in SPS {sps_hex}; will not log about trailing data again for this stream."
            );
            seen_extra_trailing_data = true;
        }

        let all_pixel_dimensions = Self::all_pixel_dimensions(&sps)
            .map_err(|e| format!("SPS has invalid pixel dimensions: {e:?}"))?;

        let (extra_data, sps_nal, pps_nal) = match framing {
            super::h26x::Framing::FourByteLength => {
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
            }
            super::h26x::Framing::AnnexB => {
                // Annex B: start code prefix + SPS + start code prefix + PPS.
                let mut buf = BytesMut::with_capacity(8 + sps_nal.len() + pps_nal.len());
                buf.extend_from_slice(&super::h26x::ANNEX_B_START_CODE);
                let sps_nal_start = buf.len();
                buf.extend_from_slice(sps_nal);
                let sps_nal_end = buf.len();
                buf.extend_from_slice(&super::h26x::ANNEX_B_START_CODE);
                let pps_nal_start = buf.len();
                buf.extend_from_slice(pps_nal);
                let pps_nal_end = buf.len();

                let buf = buf.freeze();
                let sps_nal = buf.slice(sps_nal_start..sps_nal_end);
                let pps_nal = buf.slice(pps_nal_start..pps_nal_end);
                (buf, sps_nal, pps_nal)
            }
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
                extra_data,
                codec: super::VideoParametersCodec::H264 {
                    sps: sps_nal.clone(),
                    pps: pps_nal.clone(),
                },
            },
            sps_nal,
            pps_nal,
            seen_extra_trailing_data,
        })
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
    use std::num::NonZeroU32;

    use bytes::Bytes;

    use crate::buf::{MarkBuf, PacketRef};
    use crate::codec::CodecItem;
    use crate::rtp::ReceivedPacketBuilder;
    use crate::testutil::{assert_eq_hex, assert_eq_hexes, init_logging};

    use super::*;

    /// Helper: writes payload into `buf`, then pushes to depacketizer.
    fn push_via_buf(
        d: &mut Depacketizer,
        meta: crate::rtp::PacketMeta,
        payload: &[u8],
        buf: &mut MarkBuf,
    ) -> Result<(), String> {
        let pos = buf.end();
        buf.extend(payload);
        buf.advance_unparsed(buf.end());
        d.push(&PacketRef::new(meta, buf, pos, payload.len() as u16))
    }

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
            let pkt = ReceivedPacketBuilder {
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
                // FU-A packet (non-IDR slice, type 1), start.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x7c\x81fu-a start, ")
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
            .build(*b"\x7c\x01fu-a middle, ")
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
            .build(*b"\x7c\x41fu-a end")
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
            let pkt = ReceivedPacketBuilder {
                // FU-A packet (non-IDR slice, type 1, reserved bit set), start.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x7c\xa1fu-a start, ")
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
            .build(*b"\x7c\x21fu-a middle, ")
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
            .build(*b"\x7c\x61fu-a end")
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
            let pkt = ReceivedPacketBuilder {
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
            let pkt = ReceivedPacketBuilder {
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
            o => panic!("unexpected pull result {o:#?}"),
        };
        assert_eq_hex!(frame.data(), b"\x00\x00\x00\x06\x01slice");
        assert_eq!(frame.timestamp, ts1);
        {
            let pkt = ReceivedPacketBuilder {
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
        {
            let pkt = ReceivedPacketBuilder { // new SPS.
            ctx: crate::PacketContext::dummy(),
            stream_id: 0,
            timestamp,
            ssrc: 0,
            sequence_number: 0,
            loss: 0,
            mark: false,
            payload_type: 0,
        }.build(*b"\x67\x4d\x40\x1e\x9a\x64\x05\x01\xef\xf3\x50\x10\x10\x14\x00\x00\x0f\xa0\x00\x01\x38\x80\x10").unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
            .unwrap()
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = ReceivedPacketBuilder {
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
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();

        // By codec::Depacketizer::parameters's contract, it's unspecified what the depacketizer
        // parameters are set to between push and pull.

        let frame = match d.pull() {
            Some(Ok(CodecItem::VideoFrame(frame))) => frame,
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
            let pkt = ReceivedPacketBuilder {
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
        ).unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
            .unwrap()
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = ReceivedPacketBuilder {
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
            let pkt = ReceivedPacketBuilder {
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
        ).unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
            .unwrap()
        }
        assert_eq!(d.pull(), None);
        {
            let pkt = ReceivedPacketBuilder {
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
            let pkt = ReceivedPacketBuilder {
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
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        let Some(Ok(CodecItem::VideoFrame(frame))) = d.pull() else {
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
                    let pkt = ReceivedPacketBuilder {
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
                if middle_pkt_len > 0 {
                    let mut middle_pkt = Vec::with_capacity(middle_pkt_len + 2);
                    middle_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                    middle_pkt.push(ANNEX_B_NALS[0] & 0b0001_1111); // middle
                    middle_pkt.extend_from_slice(
                        &ANNEX_B_NALS[first_pkt_len..first_pkt_len + middle_pkt_len],
                    );
                    println!("  pushing middle pkt");
                    {
                        let pkt = ReceivedPacketBuilder {
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
                }
                let mut last_pkt =
                    Vec::with_capacity(ANNEX_B_NALS.len() - first_pkt_len - middle_pkt_len + 2);
                last_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                last_pkt.push((ANNEX_B_NALS[0] & 0b0001_1111) | 0b0100_0000); // end
                last_pkt.extend_from_slice(&ANNEX_B_NALS[first_pkt_len + middle_pkt_len..]);
                println!("  pushing last pkt");
                {
                    let pkt = ReceivedPacketBuilder {
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
                    .unwrap();
                    push_via_buf(
                        &mut d,
                        crate::rtp::PacketMeta::from_received(&pkt),
                        pkt.payload(),
                        &mut buf,
                    )
                }
                .unwrap();
                println!("  pulling");
                let Some(Ok(CodecItem::VideoFrame(frame))) = d.pull() else {
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
                    let pkt = ReceivedPacketBuilder {
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
                let mut last_pkt = Vec::with_capacity(ANNEX_B_NALS.len() - first_pkt_len + 2);
                last_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28);
                last_pkt.push((ANNEX_B_NALS[0] & 0b0001_1111) | 0b0100_0000);
                last_pkt.extend_from_slice(&ANNEX_B_NALS[first_pkt_len..]);
                {
                    let pkt = ReceivedPacketBuilder {
                        ctx: crate::PacketContext::dummy(),
                        stream_id: 0,
                        timestamp,
                        ssrc: 0,
                        sequence_number: 1,
                        loss: 0,
                        mark: true,
                        payload_type: 0,
                    }
                    .build(last_pkt)
                    .unwrap();
                    push_via_buf(
                        &mut d,
                        crate::rtp::PacketMeta::from_received(&pkt),
                        pkt.payload(),
                        &mut buf,
                    )
                }
                .unwrap();
                let Some(Ok(CodecItem::VideoFrame(frame))) = d.pull() else {
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
            let pkt = ReceivedPacketBuilder {
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
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        let Some(Ok(CodecItem::VideoFrame(frame))) = d.pull() else {
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
                    let pkt = ReceivedPacketBuilder {
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
                if middle_pkt_len > 0 {
                    let mut middle_pkt = Vec::with_capacity(middle_pkt_len + 2);
                    middle_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                    middle_pkt.push(ANNEX_B_NALS[0] & 0b0001_1111); // continuation
                    middle_pkt.extend_from_slice(
                        &ANNEX_B_NALS[first_pkt_len..first_pkt_len + middle_pkt_len],
                    );
                    {
                        let pkt = ReceivedPacketBuilder {
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
                }
                let mut last_pkt =
                    Vec::with_capacity(ANNEX_B_NALS.len() - first_pkt_len - middle_pkt_len + 2);
                last_pkt.push((ANNEX_B_NALS[0] & 0b1110_0000) | 28); // FU-A indicator
                last_pkt.push((ANNEX_B_NALS[0] & 0b0001_1111) | 0b0100_0000); // end
                last_pkt.extend_from_slice(&ANNEX_B_NALS[first_pkt_len + middle_pkt_len..]);
                {
                    let pkt = ReceivedPacketBuilder {
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
                    .unwrap();
                    push_via_buf(
                        &mut d,
                        crate::rtp::PacketMeta::from_received(&pkt),
                        pkt.payload(),
                        &mut buf,
                    )
                }
                .unwrap();
                let Some(Ok(CodecItem::VideoFrame(frame))) = d.pull() else {
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
            let pkt = ReceivedPacketBuilder {
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
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        let Some(Ok(CodecItem::VideoFrame(frame))) = d.pull() else {
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
            let pkt = ReceivedPacketBuilder {
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
                // FU-A packet, end.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x3c\x47a wild sps appeared")
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        // assert!(push_result.is_err());
        let Some(Ok(CodecItem::VideoFrame(frame))) = d.pull() else {
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
        push_via_buf(
            &mut d,
            crate::rtp::PacketMeta {
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
            },
            b"\x7c\xc1small nal",
            &mut buf,
        )
        .unwrap();
        assert!(d.seen_single_fragment_fu_a);
        let frame = match d.pull() {
            Some(Ok(CodecItem::VideoFrame(frame))) => frame,
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
            let pkt = ReceivedPacketBuilder {
                // FU-A packet (non-IDR slice, type 1), start (with data).
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x7c\x81start, ")
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
                // FU-A packet, middle (empty payload after header).
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x7c\x01")
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
                // FU-A packet, end (with data).
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x7c\x41end")
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
            let pkt = ReceivedPacketBuilder {
                // FU-A packet, start.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp: timestamp0,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: false,
                payload_type: 0,
            }
            .build(*b"\x7c\x86fu-a start, ")
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
        {
            let pkt = ReceivedPacketBuilder {
                // plain non-IDR slice packet.
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp: timestamp1,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 0,
            }
            .build(*b"\x01plain")
            .unwrap();
            push_via_buf(
                &mut d,
                crate::rtp::PacketMeta::from_received(&pkt),
                pkt.payload(),
                &mut buf,
            )
        }
        .unwrap();
        match d.pull() {
            Some(Err(e)) => assert_eq!(
                e.description,
                "timestamp changed from 0 (mod-2^32: 0), npt 0.000 to 1 (mod-2^32: 1), npt 0.000 in the middle of a fragmented NAL"
            ),
            _ => panic!(),
        }
        let Some(Ok(CodecItem::VideoFrame(f))) = d.pull() else {
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
            let pkt = ReceivedPacketBuilder {
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 0,
                loss: 0,
                mark: true,
                payload_type: 96,
            }
            .build(
                *b"\x67\x4d\x00\x2a\x95\xa8\x1e\x00\x89\xf9\x61\
                       \x00\x00\x03\x00\x01\x00\x00\x03\x00\x32\x84",
            )
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

        // PPS with (incorrect) mark.
        {
            let pkt = ReceivedPacketBuilder {
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 1,
                loss: 0,
                mark: true,
                payload_type: 96,
            }
            .build(*b"\x68\xee\x3c\x80")
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

        // SEI (reserved payload type 229) with (incorrect) mark.
        {
            let pkt = ReceivedPacketBuilder {
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 2,
                loss: 0,
                mark: true,
                payload_type: 96,
            }
            .build(*b"\x06\xe5\x01\xa7\x80")
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

        // IDR slice with mark (correct this time).
        {
            let pkt = ReceivedPacketBuilder {
                ctx: crate::PacketContext::dummy(),
                stream_id: 0,
                timestamp,
                ssrc: 0,
                sequence_number: 3,
                loss: 0,
                mark: true,
                payload_type: 96,
            }
            .build(*b"\x65slice")
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
}
