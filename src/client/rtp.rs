// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Client-specific RTP/RTCP handling atop [`crate::rtp::Receiver`]: camera
//! quirks, [`UnknownRtcpSsrcPolicy`], and errors with full context.

use std::time::Instant;

use bytes::Bytes;
use log::{debug, warn};

use super::Error;
use crate::rtcp::ReceivedCompoundPacket;
use crate::rtp::{PacketHeader, ReceiveError, ReceivedPacketMeta, Receiver, SsrcMatch};
use crate::{ErrorInt, PacketContext, PacketContextInner, StreamContext, StreamContextInner};

use super::UnknownRtcpSsrcPolicy;
use super::conn::ConnCore;

/// A set-up stream's [`Receiver`], plus the client policy applied to it.
#[derive(Debug)]
pub(crate) struct StreamReceiver {
    pub(crate) receiver: Receiver,
    unknown_rtcp_ssrc: UnknownRtcpSsrcPolicy,
    seen_unknown_rtcp_ssrc: bool,
}

/// If this is TCP, notes the unexpected SSRC may be due to the live555 bug.
fn note_stale_live555_data_if_tcp(
    conn: &ConnCore,
    stream_ctx: &StreamContext,
    pkt_ctx: &PacketContext,
    now: Instant,
) {
    if let (
        StreamContext(StreamContextInner::Tcp(stream_ctx)),
        PacketContext(PacketContextInner::Tcp { msg_ctx }),
    ) = (stream_ctx, pkt_ctx)
    {
        super::note_stale_live555_data(
            conn.tool.as_ref(),
            &conn.options,
            &conn.ctx,
            stream_ctx.rtp_channel_id,
            msg_ctx,
            now,
        );
    }
}

/// Returns true if the packet should be skipped entirely.
pub(crate) fn skip(header: &PacketHeader) -> bool {
    // Skip pt=50 packets, sent by at least Geovision cameras.
    if header.payload_type() == 50 {
        debug!("skipping pkt with invalid payload type 50");
        return true;
    }
    false
}

impl StreamReceiver {
    pub(crate) fn new(receiver: Receiver, unknown_rtcp_ssrc: UnknownRtcpSsrcPolicy) -> Self {
        Self {
            receiver,
            unknown_rtcp_ssrc,
            seen_unknown_rtcp_ssrc: false,
        }
    }

    /// Formats an error description for a failed [`PacketHeader::validate`].
    pub(crate) fn validate_error(
        &self,
        reason: crate::rtp::ParseError,
        pkt: crate::inputs::Split<'_>,
    ) -> String {
        format!(
            "corrupt RTP header; {:?}: {reason}\n{:#?}",
            self.receiver,
            crate::hex::LimitedHex::from_split(pkt, 64),
        )
    }

    /// Processes a pre-validated RTP header from the stream's reorderer,
    /// returning packet metadata.
    pub(crate) fn rtp(
        &mut self,
        conn: &ConnCore,
        stream_ctx: &StreamContext,
        pkt_ctx: &PacketContext,
        stream_id: usize,
        header: &PacketHeader,
        now: Instant,
    ) -> Result<ReceivedPacketMeta<PacketContext>, Error> {
        self.receiver.rtp(*pkt_ctx, header).map_err(|e| {
            if matches!(e, ReceiveError::WrongSsrc { .. }) {
                note_stale_live555_data_if_tcp(conn, stream_ctx, pkt_ctx, now);
            }
            wrap!(ErrorInt::RtpPacketError {
                conn_ctx: conn.ctx.clone(),
                pkt_ctx: *pkt_ctx,
                stream_ctx: stream_ctx.clone(),
                stream_id,
                ssrc: header.ssrc(),
                sequence_number: header.sequence_number(),
                description: format!("{e}; {:?}", self.receiver),
            })
        })
    }

    /// Processes an RTCP compound packet, returning `None` if it should be
    /// skipped per [`UnknownRtcpSsrcPolicy`].
    pub(crate) fn rtcp(
        &mut self,
        conn: &ConnCore,
        stream_ctx: &StreamContext,
        pkt_ctx: &PacketContext,
        stream_id: usize,
        data: Bytes,
        now: Instant,
    ) -> Result<Option<ReceivedCompoundPacket>, String> {
        let first_pkt = ReceivedCompoundPacket::validate(&data[..]).map_err(|e| e.to_string())?;
        let mut rtp_timestamp = None;
        if let Ok(Some(sr)) = first_pkt.as_sender_report() {
            let info = self
                .receiver
                .sender_report(&sr)
                .map_err(|e| e.to_string())?;
            rtp_timestamp = Some(info.timestamp);
            if let SsrcMatch::Mismatched { expected } = info.ssrc_match {
                match self.unknown_rtcp_ssrc {
                    UnknownRtcpSsrcPolicy::AbortSession => {
                        note_stale_live555_data_if_tcp(conn, stream_ctx, pkt_ctx, now);
                        return Err(format!(
                            "Expected ssrc={expected:08x}, got RTCP SR ssrc={:08x}",
                            info.ssrc
                        ));
                    }
                    UnknownRtcpSsrcPolicy::Default | UnknownRtcpSsrcPolicy::DropPackets => {
                        if !self.seen_unknown_rtcp_ssrc {
                            warn!(
                                "saw unknown rtcp ssrc {:08x}; rtp session has ssrc {expected:08x}",
                                info.ssrc
                            );
                            self.seen_unknown_rtcp_ssrc = true;
                        }
                        return Ok(None);
                    }
                    UnknownRtcpSsrcPolicy::ProcessPackets => {}
                }
            }
        }
        Ok(Some(ReceivedCompoundPacket {
            ctx: *pkt_ctx,
            stream_id,
            rtp_timestamp,
            raw: data,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Checks skipping Geovision's extra payload type 50 packets. On a
    /// GV-EBD4701 running V1.02_2021_04_08, these seem to appear after every
    /// IDR frame, with the same sequence number as the final packet in that
    /// frame.
    #[test]
    fn geovision_pt50_packet() {
        let pkt = crate::rtp::build_raw_rtp(0x1234, 141000, 105, 0xd25614e, true, *b"foo").unwrap();
        assert!(!skip(&PacketHeader::validate(&pkt[..]).unwrap().header));
        let pkt = crate::rtp::build_raw_rtp(0x1234, 141000, 50, 0xd25614e, true, *b"bar").unwrap();
        assert!(skip(&PacketHeader::validate(&pkt[..]).unwrap().header));
    }
}
