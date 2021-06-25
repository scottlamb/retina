// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [H.264](https://www.itu.int/rec/T-REC-H.264-201906-I/en)-encoded video.

use std::convert::TryFrom;

use bytes::{Buf, BufMut, Bytes, BytesMut};
use failure::{bail, format_err, Error};
use h264_reader::nal::{NalHeader, UnitType};
use log::debug;

use crate::client::rtp::Packet;

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

    parameters: InternalParameters,

    /// In state `PreMark`, pieces of NALs, excluding their header bytes.
    /// Kept around (empty) in other states to re-use the backing allocation.
    pieces: Vec<Bytes>,

    /// In state `PreMark`, an entry for each NAL.
    /// Kept around (empty) in other states to re-use the backing allocation.
    nals: Vec<Nal>,
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
    start_ctx: crate::Context,
    end_ctx: crate::Context,
    timestamp: crate::Timestamp,
    stream_id: usize,

    /// True iff currently processing a FU-A.
    in_fu_a: bool,

    /// RTP packets lost as this access unit was starting.
    loss: u16,
}

#[derive(Debug)]
#[allow(clippy::clippy::large_enum_variant)]
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
    ) -> Result<Self, Error> {
        if clock_rate != 90_000 {
            bail!("H.264 clock rate must always be 90000");
        }

        // TODO: the spec doesn't require out-of-band parameters, so we shouldn't either.
        let format_specific_params = format_specific_params
            .ok_or_else(|| format_err!("H.264 depacketizer expects out-of-band parameters"))?;
        Ok(Depacketizer {
            input_state: DepacketizerInputState::New,
            pending: None,
            pieces: Vec::new(),
            nals: Vec::new(),
            parameters: InternalParameters::parse_format_specific_params(format_specific_params)?,
        })
    }

    pub(super) fn parameters(&self) -> Option<&super::Parameters> {
        Some(&self.parameters.generic_parameters)
    }

    pub(super) fn push(&mut self, pkt: Packet) -> Result<(), Error> {
        // Push shouldn't be called until pull is exhausted.
        if let Some(p) = self.pending.as_ref() {
            panic!("push with data already pending: {:?}", p);
        }

        let seq = pkt.sequence_number;
        let mut access_unit = match std::mem::replace(
            &mut self.input_state,
            DepacketizerInputState::New,
        ) {
            DepacketizerInputState::New => {
                debug_assert!(self.nals.is_empty());
                debug_assert!(self.pieces.is_empty());
                AccessUnit::start(&pkt, 0)
            }
            DepacketizerInputState::PreMark(mut access_unit) => {
                if pkt.loss > 0 {
                    if access_unit.timestamp.timestamp == pkt.timestamp.timestamp {
                        // Loss within this access unit. Ignore until mark or new timestamp.
                        self.nals.clear();
                        self.pieces.clear();
                        self.input_state = if pkt.mark {
                            DepacketizerInputState::PostMark {
                                timestamp: pkt.timestamp,
                                loss: pkt.loss,
                            }
                        } else {
                            DepacketizerInputState::Loss {
                                timestamp: pkt.timestamp,
                                pkts: pkt.loss,
                            }
                        };
                        return Ok(());
                    }
                    // A suffix of a previous access unit was lost; discard it.
                    // A prefix of the new one may have been lost; try parsing.
                    AccessUnit::start(&pkt, 0)
                } else if access_unit.timestamp.timestamp != pkt.timestamp.timestamp {
                    if !access_unit.in_fu_a {
                        bail!("Timestamp changed from {} to {} in the middle of a fragmented NAL at seq={:04x} {:#?}", access_unit.timestamp, pkt.timestamp, seq, &pkt.rtsp_ctx);
                    }
                    access_unit.end_ctx = pkt.rtsp_ctx;
                    self.pending = Some(self.finalize_access_unit(access_unit)?);
                    AccessUnit::start(&pkt, 0)
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
                if state_ts.timestamp == pkt.timestamp.timestamp {
                    bail!("Received packet with timestamp {} after marked packet with same timestamp at seq={:04x} {:#?}", pkt.timestamp, seq, &pkt.rtsp_ctx);
                }
                AccessUnit::start(&pkt, loss)
            }
            DepacketizerInputState::Loss {
                timestamp,
                mut pkts,
            } => {
                debug_assert!(self.nals.is_empty());
                debug_assert!(self.pieces.is_empty());
                if pkt.timestamp.timestamp == timestamp.timestamp {
                    pkts += pkt.loss;
                    self.input_state = DepacketizerInputState::Loss { timestamp, pkts };
                    return Ok(());
                }
                AccessUnit::start(&pkt, pkts)
            }
        };

        let mut data = pkt.payload;
        if data.is_empty() {
            bail!("Empty NAL at RTP seq {:04x}, {:#?}", seq, &pkt.rtsp_ctx);
        }
        // https://tools.ietf.org/html/rfc6184#section-5.2
        let nal_header = data[0];
        if (nal_header >> 7) != 0 {
            bail!(
                "NAL header has F bit set at seq {:04x} {:#?}",
                seq,
                &pkt.rtsp_ctx
            );
        }
        data.advance(1); // skip the header byte.
        match nal_header & 0b11111 {
            1..=23 => {
                if access_unit.in_fu_a {
                    bail!(
                        "Non-fragmented NAL while fragment in progress seq {:04x} {:#?}",
                        seq,
                        &pkt.rtsp_ctx
                    );
                }
                let len = u32::try_from(data.len()).expect("data len < u16::MAX") + 1;
                let next_piece_idx = self.add_piece(data)?;
                self.nals.push(Nal {
                    hdr: NalHeader::new(nal_header).expect("header w/o F bit set is valid"),
                    next_piece_idx,
                    len,
                });
            }
            24 => {
                // STAP-A. https://tools.ietf.org/html/rfc6184#section-5.7.1
                loop {
                    if data.remaining() < 2 {
                        bail!(
                            "STAP-A has {} remaining bytes while expecting 2-byte length",
                            data.remaining()
                        );
                    }
                    let len = data.get_u16();
                    //let len = usize::from(data.get_u16());
                    if len == 0 {
                        bail!("zero length in STAP-A");
                    }
                    let hdr =
                        NalHeader::new(data[0]).map_err(|_| format_err!("bad header in STAP-A"))?;
                    match data.remaining().cmp(&usize::from(len)) {
                        std::cmp::Ordering::Less => bail!(
                            "STAP-A too short: {} bytes remaining, expecting {}-byte NAL",
                            data.remaining(),
                            len
                        ),
                        std::cmp::Ordering::Equal => {
                            data.advance(1);
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
                            piece.advance(1);
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
            25..=27 | 29 => bail!(
                "unimplemented NAL (header 0x{:02x}) at seq {:04x} {:#?}",
                nal_header,
                seq,
                &pkt.rtsp_ctx
            ),
            28 => {
                // FU-A. https://tools.ietf.org/html/rfc6184#section-5.8
                if data.len() < 2 {
                    bail!("FU-A is too short at seq {:04x} {:#?}", seq, &pkt.rtsp_ctx);
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
                    bail!(
                        "Invalid FU-A header {:08b} at seq {:04x} {:#?}",
                        fu_header,
                        seq,
                        &pkt.rtsp_ctx
                    );
                }
                let u32_len = u32::try_from(data.len()).expect("RTP packet len must be < u16::MAX");
                match (start, access_unit.in_fu_a) {
                    (true, true) => bail!(
                        "FU-A with start bit while frag in progress at seq {:04x} {:#?}",
                        seq,
                        &pkt.rtsp_ctx
                    ),
                    (true, false) => {
                        self.add_piece(data)?;
                        self.nals.push(Nal {
                            hdr: nal_header,
                            next_piece_idx: u32::MAX, // should be overwritten later.
                            len: 1 + u32_len,
                        });
                        access_unit.in_fu_a = true;
                    }
                    (false, true) => {
                        let pieces = self.add_piece(data)?;
                        let nal = self.nals.last_mut().expect("nals non-empty while in fu-a");
                        if u8::from(nal_header) != u8::from(nal.hdr) {
                            bail!(
                                "FU-A has inconsistent NAL type: {:?} then {:?} at {:02x} {:?}",
                                nal.hdr,
                                nal_header,
                                seq,
                                &pkt.rtsp_ctx
                            );
                        }
                        nal.len += u32_len;
                        if end {
                            nal.next_piece_idx = pieces;
                            access_unit.in_fu_a = false;
                        } else if pkt.mark {
                            bail!(
                                "FU-A with MARK and no END at seq {:04x} {:#?}",
                                seq,
                                pkt.rtsp_ctx
                            );
                        }
                    }
                    (false, false) => {
                        if pkt.loss > 0 {
                            self.input_state = DepacketizerInputState::Loss {
                                timestamp: pkt.timestamp,
                                pkts: pkt.loss,
                            };
                            return Ok(());
                        }
                        bail!(
                            "FU-A with start bit unset while no frag in progress at {:04x} {:#?}",
                            seq,
                            &pkt.rtsp_ctx
                        );
                    }
                }
            }
            _ => bail!(
                "bad nal header {:0x} at seq {:04x} {:#?}",
                nal_header,
                seq,
                &pkt.rtsp_ctx
            ),
        }
        self.input_state = if pkt.mark {
            access_unit.end_ctx = pkt.rtsp_ctx;
            self.pending = Some(self.finalize_access_unit(access_unit)?);
            DepacketizerInputState::PostMark {
                timestamp: pkt.timestamp,
                loss: 0,
            }
        } else {
            DepacketizerInputState::PreMark(access_unit)
        };
        Ok(())
    }

    pub(super) fn pull(&mut self) -> Result<Option<super::CodecItem>, Error> {
        Ok(self.pending.take().map(super::CodecItem::VideoFrame))
    }

    /// Adds a piece to `self.pieces`, erroring if it becomes absurdly large.
    fn add_piece(&mut self, piece: Bytes) -> Result<u32, Error> {
        self.pieces.push(piece);
        u32::try_from(self.pieces.len()).map_err(|_| format_err!("more than u32::MAX pieces!"))
    }

    fn finalize_access_unit(&mut self, au: AccessUnit) -> Result<VideoFrame, Error> {
        let mut piece_idx = 0;
        let mut retained_len = 0usize;
        let mut is_random_access_point = false;
        let mut is_disposable = true;
        let mut new_sps = None;
        let mut new_pps = None;
        for nal in &self.nals {
            let next_piece_idx = usize::try_from(nal.next_piece_idx).expect("u32 fits in usize");
            let nal_pieces = &self.pieces[piece_idx..next_piece_idx];
            match nal.hdr.nal_unit_type() {
                UnitType::SeqParameterSet => {
                    if !matches(&self.parameters.sps_nal[..], nal.hdr, nal_pieces) {
                        new_sps = Some(to_bytes(nal.hdr, nal.len, nal_pieces));
                    }
                }
                UnitType::PicParameterSet => {
                    if !matches(&self.parameters.pps_nal[..], nal.hdr, nal_pieces) {
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
        for nal in &self.nals {
            let next_piece_idx = usize::try_from(nal.next_piece_idx).expect("u32 fits in usize");
            let nal_pieces = &self.pieces[piece_idx..next_piece_idx];
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
        let data = Bytes::from(data);
        self.nals.clear();
        self.pieces.clear();

        let new_parameters = if new_sps.is_some() || new_pps.is_some() {
            let sps_nal = new_sps.as_deref().unwrap_or(&self.parameters.sps_nal);
            let pps_nal = new_pps.as_deref().unwrap_or(&self.parameters.pps_nal);
            self.parameters = InternalParameters::parse_sps_and_pps(sps_nal, pps_nal)?;
            match self.parameters.generic_parameters {
                super::Parameters::Video(ref p) => Some(p.clone()),
                _ => unreachable!(),
            }
        } else {
            None
        };
        Ok(VideoFrame {
            new_parameters,
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

impl AccessUnit {
    fn start(pkt: &crate::client::rtp::Packet, additional_loss: u16) -> Self {
        AccessUnit {
            start_ctx: pkt.rtsp_ctx,
            end_ctx: pkt.rtsp_ctx,
            timestamp: pkt.timestamp,
            stream_id: pkt.stream_id,
            in_fu_a: false,

            // TODO: overflow?
            loss: pkt.loss + additional_loss,
        }
    }
}

#[derive(Clone, Debug)]
struct InternalParameters {
    generic_parameters: super::Parameters,

    /// The (single) SPS NAL.
    sps_nal: Bytes,

    /// The (single) PPS NAL.
    pps_nal: Bytes,
}

impl InternalParameters {
    /// Parses metadata from the `format-specific-params` of a SDP `fmtp` media attribute.
    fn parse_format_specific_params(format_specific_params: &str) -> Result<Self, Error> {
        let mut sprop_parameter_sets = None;
        for p in format_specific_params.split(';') {
            let (key, value) = p.trim().split_once('=').unwrap();
            if key == "sprop-parameter-sets" {
                sprop_parameter_sets = Some(value);
            }
        }
        let sprop_parameter_sets = sprop_parameter_sets.ok_or_else(|| {
            format_err!("no sprop-parameter-sets in H.264 format-specific-params")
        })?;

        let mut sps_nal = None;
        let mut pps_nal = None;
        for nal in sprop_parameter_sets.split(',') {
            let nal =
                base64::decode(nal).map_err(|_| format_err!("NAL has invalid base64 encoding"))?;
            if nal.is_empty() {
                bail!("empty NAL");
            }
            let header = h264_reader::nal::NalHeader::new(nal[0])
                .map_err(|_| format_err!("bad NAL header {:0x}", nal[0]))?;
            match header.nal_unit_type() {
                UnitType::SeqParameterSet => {
                    if sps_nal.is_some() {
                        bail!("multiple SPSs");
                    }
                    sps_nal = Some(nal);
                }
                UnitType::PicParameterSet => {
                    if pps_nal.is_some() {
                        bail!("multiple PPSs");
                    }
                    pps_nal = Some(nal);
                }
                _ => bail!("only SPS and PPS expected in parameter sets"),
            }
        }
        let sps_nal = sps_nal.ok_or_else(|| format_err!("no sps"))?;
        let pps_nal = pps_nal.ok_or_else(|| format_err!("no pps"))?;

        // GW security GW4089IP leaves Annex B start codes at the end of both
        // SPS and PPS in the sprop-parameter-sets. Leaving them in means
        // there's an immediate parameter change (from in-band parameters) once
        // the first frame is received. Strip them out.
        let sps_nal = sps_nal
            .strip_suffix(b"\x00\x00\x00\x01")
            .unwrap_or(&sps_nal);
        let pps_nal = pps_nal
            .strip_suffix(b"\x00\x00\x00\x01")
            .unwrap_or(&pps_nal);
        Self::parse_sps_and_pps(sps_nal, pps_nal)
    }

    fn parse_sps_and_pps(sps_nal: &[u8], pps_nal: &[u8]) -> Result<InternalParameters, Error> {
        let sps_rbsp = h264_reader::rbsp::decode_nal(&sps_nal[1..]);
        if sps_rbsp.len() < 4 {
            bail!("bad sps");
        }
        let rfc6381_codec = format!(
            "avc1.{:02X}{:02X}{:02X}",
            sps_rbsp[0], sps_rbsp[1], sps_rbsp[2]
        );
        let sps = h264_reader::nal::sps::SeqParameterSet::from_bytes(&sps_rbsp)
            .map_err(|e| format_err!("Bad SPS: {:?}", e))?;
        debug!("sps: {:#?}", &sps);

        let pixel_dimensions = sps
            .pixel_dimensions()
            .map_err(|e| format_err!("SPS has invalid pixel dimensions: {:?}", e))?;

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
        avc_decoder_config.extend(&u16::try_from(sps_nal.len())?.to_be_bytes()[..]);
        let sps_nal_start = avc_decoder_config.len();
        avc_decoder_config.extend_from_slice(sps_nal);
        let sps_nal_end = avc_decoder_config.len();
        avc_decoder_config.put_u8(1); // # of PPSs.
        avc_decoder_config.extend(&u16::try_from(pps_nal.len())?.to_be_bytes()[..]);
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
            generic_parameters: super::Parameters::Video(super::VideoParameters {
                rfc6381_codec,
                pixel_dimensions,
                pixel_aspect_ratio,
                frame_rate,
                extra_data: avc_decoder_config,
            }),
            sps_nal,
            pps_nal,
        })
    }
}

/// Returns true iff the bytes of `nal` equal the bytes of `[hdr, ..data]`.
fn matches(nal: &[u8], hdr: NalHeader, pieces: &[Bytes]) -> bool {
    if nal.is_empty() || nal[0] != u8::from(hdr) {
        return false;
    }
    let mut nal_pos = 1;
    for piece in pieces {
        let new_pos = nal_pos + piece.len();
        if nal.len() < new_pos {
            return false;
        }
        if &piece[..] != &nal[nal_pos..new_pos] {
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

#[cfg(test)]
mod tests {
    use std::num::NonZeroU32;

    use bytes::Bytes;

    use crate::{client::rtp::Packet, codec::CodecItem};

    #[test]
    fn depacketize() {
        let mut d = super::Depacketizer::new(90_000, Some("packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA")).unwrap();
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(Packet {
            // plain SEI packet.
            rtsp_ctx: crate::Context::dummy(),
            stream_id: 0,
            timestamp,
            sequence_number: 0,
            loss: 0,
            mark: false,
            payload: Bytes::from_static(b"\x06plain"),
        })
        .unwrap();
        assert!(d.pull().unwrap().is_none());
        d.push(Packet {
            // STAP-A packet.
            rtsp_ctx: crate::Context::dummy(),
            stream_id: 0,
            timestamp,
            sequence_number: 1,
            loss: 0,
            mark: false,
            payload: Bytes::from_static(b"\x18\x00\x09\x06stap-a 1\x00\x09\x06stap-a 2"),
        })
        .unwrap();
        assert!(d.pull().unwrap().is_none());
        d.push(Packet {
            // FU-A packet, start.
            rtsp_ctx: crate::Context::dummy(),
            stream_id: 0,
            timestamp,
            sequence_number: 2,
            loss: 0,
            mark: false,
            payload: Bytes::from_static(b"\x7c\x86fu-a start, "),
        })
        .unwrap();
        assert!(d.pull().unwrap().is_none());
        d.push(Packet {
            // FU-A packet, middle.
            rtsp_ctx: crate::Context::dummy(),
            stream_id: 0,
            timestamp,
            sequence_number: 3,
            loss: 0,
            mark: false,
            payload: Bytes::from_static(b"\x7c\x06fu-a middle, "),
        })
        .unwrap();
        assert!(d.pull().unwrap().is_none());
        d.push(Packet {
            // FU-A packet, end.
            rtsp_ctx: crate::Context::dummy(),
            stream_id: 0,
            timestamp,
            sequence_number: 4,
            loss: 0,
            mark: true,
            payload: Bytes::from_static(b"\x7c\x46fu-a end"),
        })
        .unwrap();
        let frame = match d.pull() {
            Ok(Some(CodecItem::VideoFrame(frame))) => frame,
            _ => panic!(),
        };
        assert_eq!(
            &frame.data()[..],
            b"\x00\x00\x00\x06\x06plain\
                     \x00\x00\x00\x09\x06stap-a 1\
                     \x00\x00\x00\x09\x06stap-a 2\
                     \x00\x00\x00\x22\x66fu-a start, fu-a middle, fu-a end"
        );
    }

    #[test]
    fn depacketize_parameter_change() {
        let mut d = super::Depacketizer::new(90_000, Some("a=fmtp:96 profile-level-id=420029; packetization-mode=1; sprop-parameter-sets=Z01AHppkBYHv/lBgYGQAAA+gAAE4gBA=,aO48gA==")).unwrap();
        match d.parameters() {
            Some(crate::codec::Parameters::Video(v)) => {
                assert_eq!(v.pixel_dimensions(), (704, 480));
            }
            _ => unreachable!(),
        }
        let timestamp = crate::Timestamp {
            timestamp: 0,
            clock_rate: NonZeroU32::new(90_000).unwrap(),
            start: 0,
        };
        d.push(Packet { // new SPS.
            rtsp_ctx: crate::Context::dummy(),
            stream_id: 0,
            timestamp,
            sequence_number: 0,
            loss: 0,
            mark: false,
            payload: Bytes::from_static(b"\x67\x4d\x40\x1e\x9a\x64\x05\x01\xef\xf3\x50\x10\x10\x14\x00\x00\x0f\xa0\x00\x01\x38\x80\x10"),
        }).unwrap();
        assert!(d.pull().unwrap().is_none());
        d.push(Packet {
            // same PPS again.
            rtsp_ctx: crate::Context::dummy(),
            stream_id: 0,
            timestamp,
            sequence_number: 1,
            loss: 0,
            mark: true,
            payload: Bytes::from_static(b"\x68\xee\x3c\x80"),
        })
        .unwrap();
        let frame = match d.pull() {
            Ok(Some(CodecItem::VideoFrame(frame))) => frame,
            _ => panic!(),
        };
        assert!(frame.new_parameters.is_some());
        let p = frame.new_parameters.unwrap();
        assert_eq!(p.pixel_dimensions(), (640, 480));
    }

    #[test]
    fn gw_security() {
        let params = super::InternalParameters::parse_format_specific_params(
            "packetization-mode=1;\
             profile-level-id=5046302;\
             sprop-parameter-sets=Z00AHpWoLQ9puAgICBAAAAAB,aO48gAAAAAE=",
        )
        .unwrap();
        assert_eq!(
            &params.sps_nal[..],
            b"\x67\x4d\x00\x1e\x95\xa8\x2d\x0f\x69\xb8\x08\x08\x08\x10"
        );
        assert_eq!(&params.pps_nal[..], b"\x68\xee\x3c\x80");
    }
}
