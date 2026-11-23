// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Client-specific RTP/RTCP handling atop [`crate::rtp::Receiver`]: logging
//! of dropped packets, the live555 stale session note, and
//! [`UnknownRtcpSsrcPolicy`].

use std::time::Instant;

use bytes::Bytes;
use log::{debug, trace, warn};

use crate::rtcp::ReceivedCompoundPacket;
use crate::rtp::{PacketHeader, Pushed, Receiver, ReceiverCounters};
use crate::{PacketContext, PacketContextInner, StreamContext, StreamContextInner};

use super::UnknownRtcpSsrcPolicy;
use super::conn::ConnCore;

/// A set-up stream's client policy and logging state, beside its
/// [`Receiver`].
#[derive(Debug)]
pub(crate) struct StreamPolicy {
    unknown_rtcp_ssrc: UnknownRtcpSsrcPolicy,
    seen_unknown_rtcp_ssrc: bool,

    /// Whether a packet has been dropped by the payload type filter, to warn
    /// about the first one only: a camera's audio comes fifty times a second.
    seen_filtered: bool,
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

/// Logs a packet the reorder buffer dropped: a warning the first time each
/// kind of drop happens on a stream, then only at debug level.
fn note_dropped(stream_i: usize, seq: u16, pushed: Pushed, c: ReceiverCounters) {
    let first = match pushed {
        Pushed::Late => c.late == 1,
        Pushed::Duplicate => c.duplicates == 1,
        Pushed::Stray => c.strays == 1,
        _ => false,
    };
    if first {
        warn!(
            "stream {stream_i}: dropping {pushed:?} seq={seq}; further such drops \
             are logged at debug level"
        );
    } else {
        debug!("stream {stream_i}: dropping {pushed:?} seq={seq}; {c:?}");
    }
}

impl StreamPolicy {
    pub(crate) fn new(unknown_rtcp_ssrc: UnknownRtcpSsrcPolicy) -> Self {
        Self {
            unknown_rtcp_ssrc,
            seen_unknown_rtcp_ssrc: false,
            seen_filtered: false,
        }
    }

    /// Logs the outcome of [`Receiver::push`], and notes a possible live555
    /// stale session on the first packet from an unselected source.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn pushed<T>(
        &mut self,
        receiver: &Receiver<T>,
        conn: &ConnCore,
        stream_ctx: &StreamContext,
        pkt_ctx: &PacketContext,
        stream_id: usize,
        header: &PacketHeader,
        pushed: Pushed,
        now: Instant,
    ) {
        match pushed {
            Pushed::Held => {}
            Pushed::Late | Pushed::Duplicate | Pushed::Stray => note_dropped(
                stream_id,
                header.sequence_number(),
                pushed,
                receiver.counters(),
            ),
            Pushed::Filtered | Pushed::FilteredRtcp => {
                if !std::mem::replace(&mut self.seen_filtered, true) {
                    warn!(
                        "skipping RTP packets whose payload type isn't one of stream \
                         {stream_id}'s SDP formats (e.g. another stream's on its channel): \
                         ssrc={:08x} pt={} rtcp={}; {receiver:?}; won't log further ones",
                        header.ssrc(),
                        header.payload_type(),
                        matches!(pushed, Pushed::FilteredRtcp),
                    );
                } else {
                    trace!(
                        "skipping RTP packet of another stream on stream {stream_id}'s \
                         channel: ssrc={:08x} pt={}",
                        header.ssrc(),
                        header.payload_type(),
                    );
                }
            }
            Pushed::Unselected { first: true } => {
                warn!(
                    "stream {stream_id}: ignoring RTP packets from ssrc={:08x} (starting at \
                     seq={}) while playing ssrc={:08x?}; won't log further ones from it",
                    header.ssrc(),
                    header.sequence_number(),
                    receiver.selected_ssrc(),
                );
                note_stale_live555_data_if_tcp(conn, stream_ctx, pkt_ctx, now);
            }
            Pushed::Unselected { first: false } => {
                trace!(
                    "stream {stream_id}: ignoring RTP packet from ssrc={:08x} seq={}",
                    header.ssrc(),
                    header.sequence_number(),
                );
            }
        }
    }

    /// Processes an RTCP compound packet, returning `None` if it should be
    /// skipped per [`UnknownRtcpSsrcPolicy`].
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn rtcp<T>(
        &mut self,
        receiver: &mut Receiver<T>,
        conn: &ConnCore,
        stream_ctx: &StreamContext,
        pkt_ctx: &PacketContext,
        stream_id: usize,
        data: Bytes,
        now: Instant,
    ) -> Result<Option<ReceivedCompoundPacket>, String> {
        let outcome = receiver.rtcp(&data[..], now).map_err(|e| e.to_string())?;
        if let Some(other) = outcome.other_source {
            match self.unknown_rtcp_ssrc {
                UnknownRtcpSsrcPolicy::AbortSession => {
                    note_stale_live555_data_if_tcp(conn, stream_ctx, pkt_ctx, now);
                    return Err(format!(
                        "Expected ssrc={:08x}, got RTCP SR ssrc={:08x}",
                        other.expected, other.ssrc
                    ));
                }
                UnknownRtcpSsrcPolicy::Default | UnknownRtcpSsrcPolicy::DropPackets => {
                    if !std::mem::replace(&mut self.seen_unknown_rtcp_ssrc, true) {
                        warn!(
                            "stream {stream_id}: saw unknown rtcp ssrc {:08x}; expected \
                             {:08x}",
                            other.ssrc, other.expected
                        );
                    }
                    return Ok(None);
                }
                UnknownRtcpSsrcPolicy::ProcessPackets => {}
            }
        }
        Ok(Some(ReceivedCompoundPacket {
            ctx: *pkt_ctx,
            stream_id,
            rtp_timestamp: outcome.rtp_timestamp,
            raw: data,
        }))
    }
}

/// Formats an error description for a failed [`PacketHeader::validate`].
pub(crate) fn validate_error<T>(
    receiver: &Receiver<T>,
    reason: &'static str,
    pkt: crate::inputs::Split<'_>,
) -> String {
    format!(
        "corrupt RTP header; {receiver:?}: {reason}\n{:#?}",
        crate::hex::LimitedHex::from_split(pkt, 64),
    )
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroU32;

    use super::*;
    use crate::ConnectionContext;
    use crate::client::SessionOptions;
    use crate::rtp::ReceiverOptions;

    /// RFC 3550 section 6.4.1: a sender report from SSRC `ssrc`, with RTP
    /// timestamp 1_000_000 and no report blocks.
    fn sender_report(ssrc: u32) -> Bytes {
        let mut sr = b"\x80\xc8\x00\x06".to_vec();
        sr.extend_from_slice(&ssrc.to_be_bytes());
        sr.extend_from_slice(b"\x00\x00\x00\x00\x00\x00\x00\x00");
        sr.extend_from_slice(b"\x00\x0f\x42\x40\x00\x00\x00\x00\x00\x00\x00\x00");
        Bytes::from(sr)
    }

    /// A sender report from an unexpected SSRC is dropped by default, and
    /// handed over under `UnknownRtcpSsrcPolicy::ProcessPackets`, but never
    /// placed on the timeline.
    #[test]
    fn stray_sender_report() {
        let conn = ConnCore::new(ConnectionContext::dummy(), SessionOptions::default());
        let mut receiver = Receiver::<()>::new(
            [96].into_iter().collect(),
            NonZeroU32::new(90_000).unwrap(),
            ReceiverOptions::default().ssrc(0x110),
        );
        let mut rtcp = |policy, ssrc| {
            StreamPolicy::new(policy).rtcp(
                &mut receiver,
                &conn,
                &StreamContext::dummy(),
                &PacketContext::dummy(),
                0,
                sender_report(ssrc),
                Instant::now(),
            )
        };

        assert!(
            rtcp(UnknownRtcpSsrcPolicy::Default, 0x111)
                .unwrap()
                .is_none()
        );
        assert!(rtcp(UnknownRtcpSsrcPolicy::AbortSession, 0x111).is_err());
        let pkt = rtcp(UnknownRtcpSsrcPolicy::ProcessPackets, 0x111)
            .unwrap()
            .unwrap();
        assert_eq!(pkt.rtp_timestamp(), None);

        // The expected source's report is placed.
        let pkt = rtcp(UnknownRtcpSsrcPolicy::Default, 0x110)
            .unwrap()
            .unwrap();
        assert_eq!(pkt.rtp_timestamp().unwrap().timestamp(), 1_000_000);
    }
}
