// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [H.264](https://www.itu.int/rec/T-REC-H.264-201906-I/en)-encoded video.

use std::convert::TryFrom;

use bytes::{Buf, BufMut, Bytes, BytesMut};
use failure::{bail, format_err, Error};
use h264_reader::nal::UnitType;
use log::debug;

use crate::client::rtp::Packet;

/// A [super::Depacketizer] implementation which finds access unit boundaries
/// and produces unfragmented NAL units as specified in [RFC
/// 6184](https://tools.ietf.org/html/rfc6184).
///
/// This doesn't inspect the contents of the NAL units, so it doesn't depend on or
/// verify compliance with H.264 section 7.4.1.2.3 "Order of NAL units and coded
/// pictures and association to access units".
///
/// Currently expects that the stream starts at an access unit boundary and has no lost packets.
#[derive(Debug)]
pub(crate) struct Depacketizer {
    input_state: DepacketizerInputState,
    pending: Option<AccessUnit>,
    parameters: InternalParameters,

    /// The largest fragment used. This is used for the buffer capacity on subsequent fragments, minimizing reallocation.
    frag_high_water: usize,
}

#[derive(Debug)]
struct AccessUnit {
    start_ctx: crate::Context,
    end_ctx: crate::Context,
    timestamp: crate::Timestamp,
    stream_id: usize,
    new_sps: Option<Bytes>,
    new_pps: Option<Bytes>,

    /// RTP packets lost as this access unit was starting.
    loss: u16,

    /// Currently we expect only a single slice NAL.
    picture: Option<Bytes>,
}

#[derive(Debug)]
struct PreMark {
    /// If a FU-A fragment is in progress, the buffer used to accumulate the NAL.
    frag_buf: Option<BytesMut>,

    access_unit: AccessUnit,
}

#[derive(Debug)]
#[allow(clippy::clippy::large_enum_variant)]
enum DepacketizerInputState {
    /// Not yet processing an access unit.
    New,

    Loss {
        timestamp: crate::Timestamp,
        pkts: u16,
    },

    /// Currently processing an access unit.
    /// This will be flushed after a marked packet or when receiving a later timestamp.
    PreMark(PreMark),

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
            frag_high_water: 0,
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

        // The rtp crate also has [H.264 depacketization
        // logic](https://docs.rs/rtp/0.2.2/rtp/codecs/h264/struct.H264Packet.html),
        // but it doesn't seem to match my use case. I want to iterate the NALs,
        // not re-encode them in Annex B format.
        let seq = pkt.sequence_number;
        let mut premark = match std::mem::replace(
            &mut self.input_state,
            DepacketizerInputState::New,
        ) {
            DepacketizerInputState::New => PreMark {
                access_unit: AccessUnit::start(&pkt),
                frag_buf: None,
            },
            DepacketizerInputState::PreMark(mut premark) => {
                if pkt.loss > 0 {
                    if premark.access_unit.timestamp.timestamp == pkt.timestamp.timestamp {
                        // Loss within this access unit. Ignore until mark or new timestamp.
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
                    PreMark {
                        access_unit: AccessUnit::start(&pkt),
                        frag_buf: None,
                    }
                } else {
                    if premark.access_unit.timestamp.timestamp != pkt.timestamp.timestamp {
                        if premark.frag_buf.is_some() {
                            bail!("Timestamp changed from {} to {} in the middle of a fragmented NAL at seq={:04x} {:#?}", premark.access_unit.timestamp, pkt.timestamp, seq, &pkt.rtsp_ctx);
                        }
                        premark.access_unit.end_ctx = pkt.rtsp_ctx;
                        self.pending = Some(std::mem::replace(
                            &mut premark.access_unit,
                            AccessUnit::start(&pkt),
                        ));
                    }
                    premark
                }
            }
            DepacketizerInputState::PostMark {
                timestamp: state_ts,
                loss,
            } => {
                if state_ts.timestamp == pkt.timestamp.timestamp {
                    bail!("Received packet with timestamp {} after marked packet with same timestamp at seq={:04x} {:#?}", pkt.timestamp, seq, &pkt.rtsp_ctx);
                }
                let mut access_unit = AccessUnit::start(&pkt);
                access_unit.loss += loss;
                PreMark {
                    access_unit,
                    frag_buf: None,
                }
            }
            DepacketizerInputState::Loss {
                timestamp,
                mut pkts,
            } => {
                if pkt.timestamp.timestamp == timestamp.timestamp {
                    pkts += pkt.loss;
                    self.input_state = DepacketizerInputState::Loss { timestamp, pkts };
                    return Ok(());
                }
                let mut access_unit = AccessUnit::start(&pkt);
                access_unit.loss += pkts;
                PreMark {
                    access_unit,
                    frag_buf: None,
                }
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
        match nal_header & 0b11111 {
            1..=23 => {
                if premark.frag_buf.is_some() {
                    bail!(
                        "Non-fragmented NAL while fragment in progress seq {:04x} {:#?}",
                        seq,
                        &pkt.rtsp_ctx
                    );
                }
                premark.access_unit.nal(&mut self.parameters, data)?;
            }
            24 => {
                // STAP-A. https://tools.ietf.org/html/rfc6184#section-5.7.1
                data.advance(1); // skip the header byte.
                loop {
                    if data.remaining() < 2 {
                        bail!(
                            "STAP-A has {} remaining bytes while expecting 2-byte length",
                            data.remaining()
                        );
                    }
                    let len = usize::from(data.get_u16());
                    match data.remaining().cmp(&len) {
                        std::cmp::Ordering::Less => bail!(
                            "STAP-A too short: {} bytes remaining, expecting {}-byte NAL",
                            data.remaining(),
                            len
                        ),
                        std::cmp::Ordering::Equal => {
                            premark.access_unit.nal(&mut self.parameters, data)?;
                            break;
                        }
                        std::cmp::Ordering::Greater => premark
                            .access_unit
                            .nal(&mut self.parameters, data.split_to(len))?,
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
                if data.len() < 3 {
                    bail!("FU-A is too short at seq {:04x} {:#?}", seq, &pkt.rtsp_ctx);
                }
                let fu_header = data[1];
                let start = (fu_header & 0b10000000) != 0;
                let end = (fu_header & 0b01000000) != 0;
                let reserved = (fu_header & 0b00100000) != 0;
                let nal_header = (nal_header & 0b011100000) | (fu_header & 0b00011111);
                if (start && end) || reserved {
                    bail!(
                        "Invalid FU-A header {:08b} at seq {:04x} {:#?}",
                        fu_header,
                        seq,
                        &pkt.rtsp_ctx
                    );
                }
                match (start, premark.frag_buf.take()) {
                    (true, Some(_)) => bail!(
                        "FU-A with start bit while frag in progress at seq {:04x} {:#?}",
                        seq,
                        &pkt.rtsp_ctx
                    ),
                    (true, None) => {
                        let mut frag_buf = BytesMut::with_capacity(std::cmp::max(
                            self.frag_high_water,
                            data.len() - 1,
                        ));
                        frag_buf.put_u8(nal_header);
                        data.advance(2);
                        frag_buf.put(data);
                        premark.frag_buf = Some(frag_buf);
                    }
                    (false, Some(mut frag_buf)) => {
                        if frag_buf[0] != nal_header {
                            bail!("FU-A has inconsistent NAL type: {:08b} then {:08b} at seq {:04x} {:#?}", frag_buf[0], nal_header, seq, &pkt.rtsp_ctx);
                        }
                        data.advance(2);
                        frag_buf.put(data);
                        if end {
                            self.frag_high_water = frag_buf.len();
                            premark
                                .access_unit
                                .nal(&mut self.parameters, frag_buf.freeze())?;
                        } else if pkt.mark {
                            bail!(
                                "FU-A with MARK and no END at seq {:04x} {:#?}",
                                seq,
                                pkt.rtsp_ctx
                            );
                        } else {
                            premark.frag_buf = Some(frag_buf);
                        }
                    }
                    (false, None) => {
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
            premark.access_unit.end_ctx = pkt.rtsp_ctx;
            self.pending = Some(premark.access_unit);
            DepacketizerInputState::PostMark {
                timestamp: pkt.timestamp,
                loss: 0,
            }
        } else {
            DepacketizerInputState::PreMark(premark)
        };
        Ok(())
    }

    pub(super) fn pull(&mut self) -> Result<Option<super::CodecItem>, Error> {
        let pending = match self.pending.take() {
            None => return Ok(None),
            Some(p) => p,
        };
        let new_parameters = if pending.new_sps.is_some() || pending.new_pps.is_some() {
            let sps_nal = pending
                .new_sps
                .as_deref()
                .unwrap_or(&self.parameters.sps_nal);
            let pps_nal = pending
                .new_pps
                .as_deref()
                .unwrap_or(&self.parameters.pps_nal);
            self.parameters = InternalParameters::parse_sps_and_pps(sps_nal, pps_nal)?;
            match self.parameters.generic_parameters {
                super::Parameters::Video(ref p) => Some(p.clone()),
                _ => unreachable!(),
            }
        } else {
            None
        };
        let picture = pending
            .picture
            .ok_or_else(|| format_err!("access unit has no picture"))?;
        let nal_header =
            h264_reader::nal::NalHeader::new(picture[0]).expect("nal header was previously valid");
        Ok(Some(super::CodecItem::VideoFrame(super::VideoFrame {
            start_ctx: pending.start_ctx,
            end_ctx: pending.end_ctx,
            loss: pending.loss,
            new_parameters,
            timestamp: pending.timestamp,
            stream_id: pending.stream_id,
            is_random_access_point: nal_header.nal_unit_type()
                == UnitType::SliceLayerWithoutPartitioningIdr,
            is_disposable: nal_header.nal_ref_idc() == 0,
            pos: 0,
            data_prefix: u32::try_from(picture.len()).unwrap().to_be_bytes(),
            data: picture,
        })))
    }
}

impl AccessUnit {
    fn start(pkt: &crate::client::rtp::Packet) -> Self {
        AccessUnit {
            start_ctx: pkt.rtsp_ctx,
            end_ctx: pkt.rtsp_ctx,
            timestamp: pkt.timestamp,
            stream_id: pkt.stream_id,
            loss: pkt.loss,
            new_sps: None,
            new_pps: None,
            picture: None,
        }
    }

    fn nal(&mut self, parameters: &mut InternalParameters, nal: Bytes) -> Result<(), Error> {
        if !nal.has_remaining() {
            bail!("empty NAL");
        }
        let nal_header = h264_reader::nal::NalHeader::new(nal[0])
            .map_err(|e| format_err!("bad NAL header 0x{:x}: {:#?}", nal[0], e))?;
        let unit_type = nal_header.nal_unit_type();
        match unit_type {
            UnitType::SeqParameterSet => {
                if self.new_sps.is_some() {
                    bail!("multiple SPSs in access unit");
                }
                if nal != parameters.sps_nal {
                    self.new_sps = Some(nal);
                }
            }
            UnitType::PicParameterSet => {
                if self.new_pps.is_some() {
                    bail!("multiple PPSs in access unit");
                }
                if nal != parameters.pps_nal {
                    self.new_pps = Some(nal);
                }
            }
            UnitType::SliceLayerWithoutPartitioningIdr
            | UnitType::SliceLayerWithoutPartitioningNonIdr => {
                if self.picture.is_some() {
                    bail!("currently expect only one picture NAL per access unit");
                }
                self.picture = Some(nal);
            }
            _ => {}
        }
        Ok(())
    }
}

/// Decodes a NAL unit (minus header byte) into its RBSP.
/// Stolen from h264-reader's src/avcc.rs. This shouldn't last long, see:
/// <https://github.com/dholroyd/h264-reader/issues/4>.
fn decode(encoded: &[u8]) -> Vec<u8> {
    struct NalRead(Vec<u8>);
    use h264_reader::nal::NalHandler;
    use h264_reader::Context;
    impl NalHandler for NalRead {
        type Ctx = ();
        fn start(&mut self, _ctx: &mut Context<Self::Ctx>, _header: h264_reader::nal::NalHeader) {}

        fn push(&mut self, _ctx: &mut Context<Self::Ctx>, buf: &[u8]) {
            self.0.extend_from_slice(buf)
        }

        fn end(&mut self, _ctx: &mut Context<Self::Ctx>) {}
    }
    let mut decode = h264_reader::rbsp::RbspDecoder::new(NalRead(vec![]));
    let mut ctx = Context::new(());
    decode.push(&mut ctx, encoded);
    let read = decode.into_handler();
    read.0
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
        let sps_rbsp = decode(&sps_nal[1..]);
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
                frame_rate = vui
                    .timing_info
                    .as_ref()
                    .and_then(|t| t.num_units_in_tick.checked_mul(2).map(|doubled| (doubled, t.time_scale)));
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

#[cfg(test)]
mod tests {
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
