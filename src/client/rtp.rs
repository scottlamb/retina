// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTP and RTCP handling; see [RFC 3550](https://datatracker.ietf.org/doc/html/rfc3550).

use bytes::{Buf, Bytes};
use log::{debug, trace};

use crate::client::PacketItem;
use crate::{ConnectionContext, Error, ErrorInt, PacketContext};

use super::{SessionOptions, Timeline};

/// A received RTP packet.
pub struct Packet {
    pub ctx: PacketContext,
    pub stream_id: usize,
    pub timestamp: crate::Timestamp,
    pub ssrc: u32,
    pub sequence_number: u16,

    /// Number of skipped sequence numbers since the last packet.
    ///
    /// In the case of the first packet on the stream, this may also report loss
    /// packets since the `RTP-Info` header's `seq` value. However, currently
    /// that header is not required to be present and may be ignored (see
    /// [`super::PlayOptions::ignore_zero_seq()`].)
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
            .field("payload", &crate::hex::LimitedHex::new(&self.payload, 64))
            .finish()
    }
}

/// An RTCP sender report.
#[derive(Debug)]
pub struct SenderReport {
    pub stream_id: usize,
    pub ctx: PacketContext,
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

    #[allow(clippy::too_many_arguments)]
    pub fn rtp(
        &mut self,
        session_options: &SessionOptions,
        tool: Option<&super::Tool>,
        conn_ctx: &ConnectionContext,
        pkt_ctx: &PacketContext,
        timeline: &mut Timeline,
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
                    crate::hex::LimitedHex::new(&data, 64),
                ),
            })
        })?;

        // Skip pt=50 packets, sent by at least Geovision cameras. I'm not sure
        // what purpose these serve, but they have the same sequence number as
        // the packet immediately before. In TCP streams, this can cause an
        // "Out-of-order packet or large loss" error. In UDP streams, if these
        // are delivered out of order, they will cause the more important other
        // packet with the same sequence number to be skipped.
        if reader.payload_type() == 50 {
            debug!("skipping pkt with invalid payload type 50");
            return Ok(None);
        }

        let sequence_number = u16::from_be_bytes([data[2], data[3]]); // I don't like rtsp_rs::Seq.
        let ssrc = reader.ssrc();
        let loss = sequence_number.wrapping_sub(self.next_seq.unwrap_or(sequence_number));
        if matches!(self.ssrc, Some(s) if s != ssrc) {
            if matches!(session_options.transport, super::Transport::Tcp) {
                super::note_stale_live555_data(tool, session_options);
            }
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
                return Ok(None);
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

    #[allow(clippy::too_many_arguments)]
    pub fn rtcp(
        &mut self,
        session_options: &SessionOptions,
        tool: Option<&super::Tool>,
        pkt_ctx: &PacketContext,
        timeline: &mut Timeline,
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
                        if matches!(session_options.transport, super::Transport::Tcp) {
                            super::note_stale_live555_data(tool, session_options);
                        }
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Checks dropping and logging Geovision's extra payload type 50 packets.
    /// On a GV-EBD4701 running V1.02_2021_04_08, these seem to appear after
    /// every IDR frame, with the same sequence number as the final packet in
    /// that frame.
    #[test]
    fn geovision_pt50_packet() {
        let mut timeline = Timeline::new(None, 90_000, None).unwrap();
        let mut parser = InorderParser::new(Some(0xd25614e), None);

        // Normal packet.
        match parser.rtp(
            &SessionOptions::default(),
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            rtp_rs::RtpPacketBuilder::new()
                .payload_type(105)
                .ssrc(0xd25614e)
                .sequence(0x1234.into())
                .timestamp(141000)
                .marked(true)
                .payload(b"foo")
                .build()
                .unwrap()
                .into(),
        ) {
            Ok(Some(PacketItem::RtpPacket(_))) => {}
            o => panic!("unexpected packet 1 result: {:#?}", o),
        }

        // Mystery pt=50 packet with same sequence number.
        match parser.rtp(
            &SessionOptions::default(),
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            rtp_rs::RtpPacketBuilder::new()
                .payload_type(50)
                .ssrc(0xd25614e)
                .sequence(0x1234.into())
                .timestamp(141000)
                .marked(true)
                .payload(b"bar")
                .build()
                .unwrap()
                .into(),
        ) {
            Ok(None) => {}
            o => panic!("unexpected packet 2 result: {:#?}", o),
        }
    }

    #[test]
    fn out_of_order() {
        let mut timeline = Timeline::new(None, 90_000, None).unwrap();
        let mut parser = InorderParser::new(Some(0xd25614e), None);

        let session_options = SessionOptions::default().transport(crate::client::Transport::Udp);
        match parser.rtp(
            &session_options,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            rtp_rs::RtpPacketBuilder::new()
                .payload_type(96)
                .ssrc(0xd25614e)
                .sequence(2.into())
                .timestamp(2)
                .marked(true)
                .payload(b"pkt 2")
                .build()
                .unwrap()
                .into(),
        ) {
            Ok(Some(PacketItem::RtpPacket(p))) => {
                assert_eq!(p.timestamp.elapsed(), 0);
            }
            o => panic!("unexpected packet 2 result: {:#?}", o),
        }

        match parser.rtp(
            &session_options,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            rtp_rs::RtpPacketBuilder::new()
                .payload_type(96)
                .ssrc(0xd25614e)
                .sequence(1.into())
                .timestamp(1)
                .marked(true)
                .payload(b"pkt 1")
                .build()
                .unwrap()
                .into(),
        ) {
            Ok(None) => {}
            o => panic!("unexpected packet 1 result: {:#?}", o),
        }

        match parser.rtp(
            &session_options,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            rtp_rs::RtpPacketBuilder::new()
                .payload_type(96)
                .ssrc(0xd25614e)
                .sequence(3.into())
                .timestamp(3)
                .marked(true)
                .payload(b"pkt 3")
                .build()
                .unwrap()
                .into(),
        ) {
            Ok(Some(PacketItem::RtpPacket(p))) => {
                // The missing timestamp shouldn't have adjusted time.
                assert_eq!(p.timestamp.elapsed(), 1);
            }
            o => panic!("unexpected packet 2 result: {:#?}", o),
        }
    }
}
