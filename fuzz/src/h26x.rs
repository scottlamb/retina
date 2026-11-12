// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Structured fuzz input for the H.264 and H.265 depacketizers.
//!
//! Rather than having libFuzzer mutate raw RTP payload bytes, input is decoded
//! (via [`Arbitrary`]) into a sequence of typed packets: single NAL units,
//! aggregation packets, and fragmentation units, which are then serialized
//! into well-formed RTP payloads for the codec in question. This lets the
//! fuzzer cheaply explore *sequences* of packets (e.g. a fragment start
//! followed by an aggregation packet), which is where depacketizer state
//! machine bugs live and which raw-byte mutation struggles to reach because
//! coverage gives little signal for them. The [`Payload::Raw`] variant keeps
//! malformed payloads in scope.

use derive_more::Debug;
use libfuzzer_sys::Corpus;
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use pretty_hex::PrettyHex as _;
use std::num::NonZeroU32;

#[derive(Copy, Clone, Debug)]
pub enum Codec {
    H264,
    H265,
}

#[derive(Arbitrary, Debug)]
pub struct Pkt<'i> {
    pub ts_change: bool,
    pub mark: bool,
    pub loss: bool,
    pub payload: Payload<'i>,
}

#[derive(Arbitrary, Debug)]
pub enum Payload<'i> {
    /// A single NAL unit packet (H.264 types 1–23; H.265 types 0–47).
    Single(Nal<'i>),

    /// An aggregation packet (H.264 STAP-A; H.265 AP).
    Aggregation(Vec<Nal<'i>>),

    /// A fragmentation unit (H.264 FU-A; H.265 FU). `nal.body` is this fragment's data.
    Fragment {
        start: bool,
        end: bool,
        nal: Nal<'i>,
    },

    /// An arbitrary payload, to also cover malformed packets.
    Raw(#[debug("{:?}", _0.hex_conf(retina::testutil::NONASCII_HEX_CONFIG))] &'i [u8]),
}

#[derive(Arbitrary, Debug)]
pub struct Nal<'i> {
    /// Selects the NAL unit type; mapped into the valid range for the packet kind.
    pub unit_type: u8,

    /// Remaining header bits. H.264: `nal_ref_idc` from bits 5–6.
    /// H.265: `nuh_temporal_id_plus1` from bits 0–2 (forced non-zero);
    /// `nuh_layer_id` from bits 3–6 if bit 7 is set, else 0.
    pub hdr_bits: u8,

    #[debug("{:?}", body.hex_conf(retina::testutil::NONASCII_HEX_CONFIG))]
    pub body: &'i [u8],
}

impl Nal<'_> {
    /// Appends the NAL header with the given unit type.
    fn put_hdr(&self, codec: Codec, unit_type: u8, out: &mut Vec<u8>) {
        match codec {
            Codec::H264 => out.push((self.hdr_bits & 0b0110_0000) | (unit_type & 0b1_1111)),
            Codec::H265 => {
                let tid = 1 + (self.hdr_bits & 0b111) % 7;
                let layer_id = if self.hdr_bits & 0x80 != 0 {
                    (self.hdr_bits >> 3) & 0b1111
                } else {
                    0
                };
                out.push((unit_type & 0b11_1111) << 1); // layer_id < 32, so its high bit is 0.
                out.push(((layer_id & 0b1_1111) << 3) | tid);
            }
        }
    }

    /// Returns the unit type to use for a complete (single or aggregated) NAL.
    fn complete_unit_type(&self, codec: Codec) -> u8 {
        match codec {
            Codec::H264 => 1 + self.unit_type % 23,
            Codec::H265 => self.unit_type % 48,
        }
    }

    /// Appends the NAL in full (header + body).
    fn put_complete(&self, codec: Codec, out: &mut Vec<u8>) {
        self.put_hdr(codec, self.complete_unit_type(codec), out);
        out.extend_from_slice(self.body);
    }
}

impl Payload<'_> {
    pub fn serialize(&self, codec: Codec, out: &mut Vec<u8>) {
        out.clear();
        match self {
            Payload::Single(nal) => nal.put_complete(codec, out),
            Payload::Aggregation(nals) => {
                match codec {
                    Codec::H264 => {
                        let nri = nals.iter().map(|n| n.hdr_bits & 0b0110_0000).max();
                        out.push(nri.unwrap_or(0) | 24);
                    }
                    Codec::H265 => out.extend_from_slice(&[48 << 1, 1]),
                }
                for nal in nals {
                    let len_pos = out.len();
                    out.extend_from_slice(&[0, 0]);
                    nal.put_complete(codec, out);
                    let len = u16::try_from(out.len() - len_pos - 2).unwrap_or(u16::MAX);
                    out[len_pos..len_pos + 2].copy_from_slice(&len.to_be_bytes());
                }
            }
            Payload::Fragment { start, end, nal } => {
                let (indicator_type, inner_type) = match codec {
                    Codec::H264 => (28, nal.unit_type & 0b1_1111),
                    Codec::H265 => (49, nal.unit_type & 0b11_1111),
                };
                nal.put_hdr(codec, indicator_type, out);
                out.push((u8::from(*start) << 7) | (u8::from(*end) << 6) | inner_type);
                out.extend_from_slice(nal.body);
            }
            Payload::Raw(raw) => out.extend_from_slice(raw),
        }
    }
}

/// Runs the given packets through a depacketizer for `codec`, checking invariants throughout.
pub fn run(codec: Codec, pkts: Vec<Pkt<'_>>) -> Corpus {
    crate::init_logging();
    let (encoding, params) = match codec {
        Codec::H264 => (
            "h264",
            "packetization-mode=1;profile-level-id=64001E;sprop-parameter-sets=Z2QAHqwsaoLA9puCgIKgAAADACAAAAMD0IAA,aO4xshsA",
        ),
        Codec::H265 => (
            "h265",
            "profile-id=1;sprop-sps=QgEBAWAAAAMAsAAAAwAAAwBaoAWCAeFja5JFL83BQYFBAAADAAEAAAMADKE=;sprop-pps=RAHA8saNA7NA;sprop-vps=QAEMAf//AWAAAAMAsAAAAwAAAwBarAwAAAMABAAAAwAyqA==",
        ),
    };
    if matches!(codec, Codec::H264) && pkts.first().is_none_or(|p| p.ts_change) {
        return Corpus::Reject;
    }
    let mut depacketizer =
        retina::codec::Depacketizer::new("video", encoding, 90_000, None, Some(params)).unwrap();
    let mut timestamp = retina::Timestamp::new(0, NonZeroU32::new(90_000).unwrap(), 0).unwrap();
    let mut sequence_number: u16 = 0;
    let pkt_ctx = retina::PacketContext::dummy();
    let mut buf = retina::testutil::DepacketizeBuf::new(65536);
    let mut payload = Vec::new();
    for pkt in pkts {
        pkt.payload.serialize(codec, &mut payload);
        log::trace!(
            "pkt: {pkt:?} -> {:?}",
            payload.hex_conf(retina::testutil::NONASCII_HEX_CONFIG)
        );
        let Ok(_) = u16::try_from(payload.len()) else {
            return Corpus::Reject;
        };
        if pkt.loss {
            sequence_number = sequence_number.wrapping_add(1);
        }
        if pkt.ts_change {
            timestamp = timestamp.try_add(1).unwrap();
        }
        let meta = retina::rtp::PacketMeta {
            ctx: pkt_ctx,
            stream_id: 0,
            timestamp,
            ssrc: 0,
            sequence_number,
            loss: u16::from(pkt.loss),
            mark: pkt.mark,
        };
        if let Err(e) = buf.push(&mut depacketizer, meta, &payload) {
            log::info!("depacketizer push error: {e:?}");
            depacketizer.check_invariants();
            return Corpus::Keep;
        }
        depacketizer.check_invariants();
        while let Some(item) = depacketizer.pull() {
            depacketizer.check_invariants();
            match item {
                Ok(retina::codec::CodecItem::VideoFrame(f)) => {
                    if matches!(codec, Codec::H264) {
                        retina::testutil::validate_avcc_frame(f.data()).unwrap();
                    }
                }
                Ok(_) => unreachable!(),
                Err(e) => {
                    log::info!("depacketizer pull error: {e:?}");
                    return Corpus::Keep;
                }
            }
        }
        depacketizer.check_invariants();
        sequence_number = sequence_number.wrapping_add(1);
    }
    Corpus::Keep
}
