// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTP and RTCP handling; see [RFC 3550](https://datatracker.ietf.org/doc/html/rfc3550).

use bytes::{Buf, Bytes};
use log::trace;
use pretty_hex::PrettyHex;

use crate::client::PacketItem;
use crate::{Error, ErrorInt};

/// A received RTP packet.
pub struct Packet {
    pub ctx: crate::PacketContext,
    pub stream_id: usize,
    pub timestamp: crate::Timestamp,
    pub ssrc: u32,
    pub sequence_number: u16,

    /// Number of skipped sequence numbers since the last packet.
    ///
    /// In the case of the first packet on the stream, this may also report loss
    /// packets since the `RTP-Info` header's `seq` value. However, currently
    /// that header is not required to be present and may be ignored (see
    /// [`retina::client::PlayPolicy::ignore_zero_seq()`].)
    pub loss: u16,

    pub mark: bool,

    /// Guaranteed to be less than u16::MAX bytes.
    pub payload: Bytes,
}

impl std::fmt::Debug for Packet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Packet")
            .field("ctx", &self.ctx)
            .field("stream_id", &self.stream_id)
            .field("timestamp", &self.timestamp)
            .field("ssrc", &self.ssrc)
            .field("sequence_number", &self.sequence_number)
            .field("loss", &self.loss)
            .field("mark", &self.mark)
            .field("payload", &self.payload.hex_dump())
            .finish()
    }
}

/// An RTCP sender report.
#[derive(Debug)]
pub struct SenderReport {
    pub stream_id: usize,
    pub ctx: crate::PacketContext,
    pub timestamp: crate::Timestamp,
    pub ntp_timestamp: crate::NtpTimestamp,
}

/// RTP/RTCP demarshaller which ensures packets have the correct SSRC and
/// monotonically increasing SEQ. Unstable; exposed for benchmark.
///
/// When using UDP, skips and logs out-of-order packets. When using TCP,
/// fails on them.
///
/// This reports packet loss (via [Packet::loss]) but doesn't prohibit it
/// of more than `i16::MAX` which would be indistinguishable from non-monotonic sequence numbers.
/// Servers sometimes drop packets internally even when sending data via TCP.
///
/// At least [one camera](https://github.com/scottlamb/moonfire-nvr/wiki/Cameras:-Reolink#reolink-rlc-410-hardware-version-ipc_3816m)
/// sometimes sends data from old RTSP sessions over new ones. This seems like a
/// serious bug, and currently `InorderRtpParser` will error in this case,
/// although it'd be possible to discard the incorrect SSRC instead.
///
/// [RFC 3550 section 8.2](https://tools.ietf.org/html/rfc3550#section-8.2) says that SSRC
/// can change mid-session with a RTCP BYE message. This currently isn't handled. I'm
/// not sure it will ever come up with IP cameras.
#[doc(hidden)]
#[derive(Debug)]
pub struct InorderParser {
    ssrc: Option<u32>,
    next_seq: Option<u16>,
}

impl InorderParser {
    pub fn new(ssrc: Option<u32>, next_seq: Option<u16>) -> Self {
        Self { ssrc, next_seq }
    }

    pub fn rtp(
        &mut self,
        session_options: &super::SessionOptions,
        conn_ctx: &crate::ConnectionContext,
        pkt_ctx: &crate::PacketContext,
        timeline: &mut super::Timeline,
        stream_id: usize,
        mut data: Bytes,
    ) -> Result<Option<PacketItem>, Error> {
        let reader = rtp_rs::RtpReader::new(&data[..]).map_err(|e| {
            wrap!(ErrorInt::PacketError {
                conn_ctx: *conn_ctx,
                pkt_ctx: *pkt_ctx,
                stream_id,
                description: format!(
                    "corrupt RTP header while expecting seq={:04x?}: {:?}\n{:#?}",
                    &self.next_seq,
                    e,
                    data.hex_dump(),
                ),
            })
        })?;
        let sequence_number = u16::from_be_bytes([data[2], data[3]]); // I don't like rtsp_rs::Seq.
        let ssrc = reader.ssrc();
        let loss = sequence_number.wrapping_sub(self.next_seq.unwrap_or(sequence_number));
        if matches!(self.ssrc, Some(s) if s != ssrc) {
            bail!(ErrorInt::RtpPacketError {
                conn_ctx: *conn_ctx,
                pkt_ctx: *pkt_ctx,
                stream_id,
                ssrc,
                sequence_number,
                description: format!(
                    "Wrong ssrc; expecting ssrc={:08x?} seq={:04x?}",
                    self.ssrc, self.next_seq
                ),
            });
        }
        if loss > 0x80_00 {
            if matches!(session_options.transport, super::Transport::Tcp) {
                bail!(ErrorInt::RtpPacketError {
                    conn_ctx: *conn_ctx,
                    pkt_ctx: *pkt_ctx,
                    stream_id,
                    ssrc,
                    sequence_number,
                    description: format!(
                        "Out-of-order packet or large loss; expecting ssrc={:08x?} seq={:04x?}",
                        self.ssrc, self.next_seq
                    ),
                });
            } else {
                log::info!(
                    "Skipping out-of-order seq={:04x} when expecting ssrc={:08x?} seq={:04x?}",
                    sequence_number,
                    self.ssrc,
                    self.next_seq
                );
            }
        }
        let timestamp = match timeline.advance_to(reader.timestamp()) {
            Ok(ts) => ts,
            Err(description) => bail!(ErrorInt::RtpPacketError {
                conn_ctx: *conn_ctx,
                pkt_ctx: *pkt_ctx,
                stream_id,
                ssrc,
                sequence_number,
                description,
            }),
        };
        self.ssrc = Some(ssrc);
        let mark = reader.mark();
        let payload_range = crate::as_range(&data, reader.payload()).ok_or_else(|| {
            wrap!(ErrorInt::RtpPacketError {
                conn_ctx: *conn_ctx,
                pkt_ctx: *pkt_ctx,
                stream_id,
                ssrc,
                sequence_number,
                description: "empty payload".into(),
            })
        })?;
        data.truncate(payload_range.end);
        data.advance(payload_range.start);
        self.next_seq = Some(sequence_number.wrapping_add(1));
        Ok(Some(PacketItem::RtpPacket(Packet {
            ctx: *pkt_ctx,
            stream_id,
            timestamp,
            ssrc,
            sequence_number,
            loss,
            mark,
            payload: data,
        })))
    }

    pub fn rtcp(
        &mut self,
        pkt_ctx: &crate::PacketContext,
        timeline: &mut super::Timeline,
        stream_id: usize,
        data: Bytes,
    ) -> Result<Option<PacketItem>, String> {
        let mut sr = None;
        let mut i = 0;
        let mut data = &data[..];
        while !data.is_empty() {
            let (pkt, rest) = crate::rtcp::Packet::parse(data)?;
            data = rest;
            match pkt {
                crate::rtcp::Packet::SenderReport(pkt) => {
                    if i > 0 {
                        return Err("RTCP SR must be first in packet".into());
                    }
                    let timestamp =
                        timeline
                            .place(pkt.rtp_timestamp())
                            .map_err(|mut description| {
                                description.push_str(" in RTCP SR");
                                description
                            })?;

                    let ssrc = pkt.ssrc();
                    if matches!(self.ssrc, Some(s) if s != ssrc) {
                        return Err(format!(
                            "Expected ssrc={:08x?}, got RTCP SR ssrc={:08x}",
                            self.ssrc, ssrc
                        ));
                    }
                    self.ssrc = Some(ssrc);

                    sr = Some(SenderReport {
                        stream_id,
                        ctx: *pkt_ctx,
                        timestamp,
                        ntp_timestamp: pkt.ntp_timestamp(),
                    });
                }
                crate::rtcp::Packet::Unknown(pkt) => trace!("rtcp: pt {:?}", pkt.payload_type()),
            }
            i += 1;
        }
        Ok(sr.map(PacketItem::SenderReport))
    }
}
