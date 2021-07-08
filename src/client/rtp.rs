// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTP and RTCP handling; see [RFC 3550](https://datatracker.ietf.org/doc/html/rfc3550).

use bytes::{Buf, Bytes};
use log::debug;
use pretty_hex::PrettyHex;

use crate::client::PacketItem;
use crate::{Error, ErrorInt};

/// A received RTP packet.
pub struct Packet {
    pub ctx: crate::RtspMessageContext,
    pub channel_id: u8,
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
            .field("channel_id", &self.channel_id)
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
    pub ctx: crate::RtspMessageContext,
    pub timestamp: crate::Timestamp,
    pub ntp_timestamp: crate::NtpTimestamp,
}

/// RTP/RTCP demarshaller which ensures packets have the correct SSRC and
/// monotonically increasing SEQ. Unstable; exposed for benchmark.
///
/// This reports packet loss (via [Packet::loss]) but doesn't prohibit it, except for losses
/// of more than `i16::MAX` which would be indistinguishable from non-monotonic sequence numbers.
/// Servers sometimes drop packets internally even when sending data via TCP.
///
/// At least [one camera](https://github.com/scottlamb/moonfire-nvr/wiki/Cameras:-Reolink#reolink-rlc-410-hardware-version-ipc_3816m)
/// sometimes sends data from old RTSP sessions over new ones. This seems like a
/// serious bug, and currently `StrictSequenceChecker` will error in this case,
/// although it'd be possible to discard the incorrect SSRC instead.
///
/// [RFC 3550 section 8.2](https://tools.ietf.org/html/rfc3550#section-8.2) says that SSRC
/// can change mid-session with a RTCP BYE message. This currently isn't handled. I'm
/// not sure it will ever come up with IP cameras.
#[doc(hidden)]
#[derive(Debug)]
pub struct StrictSequenceChecker {
    ssrc: Option<u32>,
    next_seq: Option<u16>,
}

impl StrictSequenceChecker {
    pub fn new(ssrc: Option<u32>, next_seq: Option<u16>) -> Self {
        Self { ssrc, next_seq }
    }

    pub fn rtp(
        &mut self,
        conn_ctx: &crate::ConnectionContext,
        msg_ctx: &crate::RtspMessageContext,
        timeline: &mut super::Timeline,
        channel_id: u8,
        stream_id: usize,
        mut data: Bytes,
    ) -> Result<PacketItem, Error> {
        // Terrible hack to try to make sense of the GW Security GW4089IP's audio stream.
        // It appears to have one RTSP interleaved message wrapped in another. RTP and RTCP
        // packets can never start with '$', so this shouldn't interfere with well-behaved
        // servers.
        if data.len() > 4
            && data[0] == b'$'
            && usize::from(u16::from_be_bytes([data[2], data[3]])) <= data.len() - 4
        {
            log::debug!("stripping extra interleaved data header");
            data.advance(4);
            // also remove suffix? dunno.
        }

        let reader = rtp_rs::RtpReader::new(&data[..]).map_err(|e| {
            wrap!(ErrorInt::RtspDataMessageError {
                conn_ctx: *conn_ctx,
                msg_ctx: *msg_ctx,
                channel_id,
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
        let timestamp = match timeline.advance_to(reader.timestamp()) {
            Ok(ts) => ts,
            Err(description) => bail!(ErrorInt::RtpPacketError {
                conn_ctx: *conn_ctx,
                msg_ctx: *msg_ctx,
                channel_id,
                stream_id,
                ssrc,
                sequence_number,
                description,
            }),
        };
        let loss = sequence_number.wrapping_sub(self.next_seq.unwrap_or(sequence_number));
        if matches!(self.ssrc, Some(s) if s != ssrc) || loss > 0x80_00 {
            bail!(ErrorInt::RtpPacketError {
                conn_ctx: *conn_ctx,
                msg_ctx: *msg_ctx,
                channel_id,
                stream_id,
                ssrc,
                sequence_number,
                description: format!(
                    "Expected ssrc={:08x?} seq={:04x?}",
                    self.ssrc, self.next_seq
                ),
            });
        }
        self.ssrc = Some(ssrc);
        let mark = reader.mark();
        let payload_range = crate::as_range(&data, reader.payload()).ok_or_else(|| {
            wrap!(ErrorInt::RtpPacketError {
                conn_ctx: *conn_ctx,
                msg_ctx: *msg_ctx,
                channel_id,
                stream_id,
                ssrc,
                sequence_number,
                description: "empty payload".into(),
            })
        })?;
        data.truncate(payload_range.end);
        data.advance(payload_range.start);
        self.next_seq = Some(sequence_number.wrapping_add(1));
        Ok(PacketItem::RtpPacket(Packet {
            ctx: *msg_ctx,
            channel_id,
            stream_id,
            timestamp,
            ssrc,
            sequence_number,
            loss,
            mark,
            payload: data,
        }))
    }

    pub fn rtcp(
        &mut self,
        msg_ctx: &crate::RtspMessageContext,
        timeline: &mut super::Timeline,
        stream_id: usize,
        mut data: Bytes,
    ) -> Result<Option<PacketItem>, String> {
        use rtcp::packet::Packet;
        let mut sr = None;
        let mut i = 0;
        while !data.is_empty() {
            let h = match rtcp::header::Header::unmarshal(&data) {
                Err(e) => return Err(format!("corrupt RTCP header: {}", e)),
                Ok(h) => h,
            };
            let pkt_len = (usize::from(h.length) + 1) * 4;
            if pkt_len > data.len() {
                return Err(format!(
                    "RTCP packet length {} exceeds remaining data message length {}",
                    pkt_len,
                    data.len(),
                ));
            }
            let pkt = data.split_to(pkt_len);
            match h.packet_type {
                rtcp::header::PacketType::SenderReport => {
                    if i > 0 {
                        return Err("RTCP SR must be first in packet".into());
                    }
                    let pkt = rtcp::sender_report::SenderReport::unmarshal(&pkt)
                        .map_err(|e| format!("corrupt RTCP SR: {}", e))?;
                    let timestamp = timeline.place(pkt.rtp_time).map_err(|mut description| {
                        description.push_str(" in RTCP SR");
                        description
                    })?;

                    // TODO: verify ssrc.

                    sr = Some(SenderReport {
                        stream_id,
                        ctx: *msg_ctx,
                        timestamp,
                        ntp_timestamp: crate::NtpTimestamp(pkt.ntp_time),
                    });
                }
                /*rtcp::header::PacketType::SourceDescription => {
                    let pkt = rtcp::source_description::SourceDescription::unmarshal(&pkt)?;
                    debug!("rtcp source description: {:#?}", &pkt);
                },*/
                _ => debug!("rtcp: {:?}", h.packet_type),
            }
            i += 1;
        }
        Ok(sr.map(PacketItem::SenderReport))
    }
}
