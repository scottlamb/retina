// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTP and RTCP handling; see [RFC 3550](https://datatracker.ietf.org/doc/html/rfc3550).

use bytes::Bytes;
use log::{debug, warn};

use crate::client::PacketItem;
use crate::rtcp::ReceivedCompoundPacket;
use crate::rtp::{PacketHeader, PacketMeta};
use crate::{
    ConnectionContext, Error, ErrorInt, PacketContext, PacketContextInner, StreamContext,
    StreamContextInner,
};

use super::{SessionOptions, Timeline, UnknownRtcpSsrcPolicy};

/// Describes how Retina formed its initial expectation for the stream's `ssrc` or `seq`.
#[derive(Copy, Clone, Debug)]
enum InitialExpectation {
    PlayResponseHeader,
    RtpPacket,
    RtcpPacket,
}

#[derive(Copy, Clone)]
struct Ssrc {
    init: InitialExpectation,
    ssrc: u32,
}

impl std::fmt::Debug for Ssrc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("Ssrc")
            .field("init", &self.init)
            .field("ssrc", &format_args!("0x{:08x}", self.ssrc))
            .finish()
    }
}

#[derive(Copy, Clone, Debug)]
struct Seq {
    init: InitialExpectation,
    next: u16,
}

/// RTP/RTCP demarshaller which ensures packets have the correct SSRC and
/// monotonically increasing SEQ. Unstable; exposed for benchmark.
///
/// When using UDP, skips and logs out-of-order packets. When using TCP,
/// fails on them.
///
/// This reports packet loss (via [ReceivedPacket::loss]) but doesn't prohibit it
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
#[doc(hidden)] // pub only for the benchmarks; not a stable API.
#[derive(Debug)]
pub struct InorderParser {
    ssrc: Option<Ssrc>,
    seq: Option<Seq>,

    /// Total RTP packets seen in this stream.
    seen_rtp_packets: u64,

    /// Total RTCP packets seen in this stream.
    seen_rtcp_packets: u64,

    unknown_rtcp_session: UnknownRtcpSsrcPolicy,
    seen_unknown_rtcp_session: bool,
}

fn note_stale_live555_data_if_tcp(
    tool: Option<&super::Tool>,
    session_options: &SessionOptions,
    conn_ctx: &crate::ConnectionContext,
    stream_ctx: &StreamContext,
    pkt_ctx: &PacketContext,
) {
    if let (
        StreamContext(StreamContextInner::Tcp(stream_ctx)),
        PacketContext(PacketContextInner::Tcp { msg_ctx }),
    ) = (stream_ctx, pkt_ctx)
    {
        super::note_stale_live555_data(
            tool,
            session_options,
            conn_ctx,
            stream_ctx.rtp_channel_id,
            msg_ctx,
        );
    }
}

impl InorderParser {
    pub fn new(
        ssrc: Option<u32>,
        next_seq: Option<u16>,
        unknown_rtcp_session: UnknownRtcpSsrcPolicy,
    ) -> Self {
        Self {
            ssrc: ssrc.map(|ssrc| Ssrc {
                init: InitialExpectation::PlayResponseHeader,
                ssrc,
            }),
            seq: next_seq.map(|next| Seq {
                init: InitialExpectation::PlayResponseHeader,
                next,
            }),
            seen_rtp_packets: 0,
            seen_rtcp_packets: 0,
            unknown_rtcp_session,
            seen_unknown_rtcp_session: false,
        }
    }

    /// Validates an RTP header and checks SSRC/sequence/timestamp ordering.
    ///
    /// Returns `Ok(Some((timestamp, loss)))` on success, `Ok(None)` if the
    /// packet should be skipped (e.g. pt=50 or out-of-order UDP).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn rtp_validate(
        &mut self,
        session_options: &SessionOptions,
        stream_ctx: &StreamContext,
        tool: Option<&super::Tool>,
        conn_ctx: &ConnectionContext,
        pkt_ctx: &PacketContext,
        timeline: &mut Timeline,
        stream_id: usize,
        header: &PacketHeader,
    ) -> Result<Option<(crate::Timestamp, u16)>, Error> {
        // Skip pt=50 packets, sent by at least Geovision cameras.
        if header.payload_type() == 50 {
            debug!("skipping pkt with invalid payload type 50");
            return Ok(None);
        }

        let sequence_number = header.sequence_number();
        let ssrc = header.ssrc();
        let loss =
            sequence_number.wrapping_sub(self.seq.map(|s| s.next).unwrap_or(sequence_number));
        if matches!(self.ssrc, Some(s) if s.ssrc != ssrc) {
            note_stale_live555_data_if_tcp(tool, session_options, conn_ctx, stream_ctx, pkt_ctx);
            bail!(ErrorInt::RtpPacketError {
                conn_ctx: *conn_ctx,
                pkt_ctx: *pkt_ctx,
                stream_ctx: stream_ctx.to_owned(),
                stream_id,
                ssrc,
                sequence_number,
                description: format!(
                    "wrong ssrc after {} RTP pkts + {} RTCP pkts; expecting ssrc={:?} seq={:?}",
                    self.seen_rtp_packets, self.seen_rtcp_packets, self.ssrc, self.seq,
                ),
            });
        } else if self.ssrc.is_none() {
            self.ssrc = Some(Ssrc {
                init: InitialExpectation::RtpPacket,
                ssrc,
            });
        }
        if loss > 0x80_00 {
            if matches!(stream_ctx.0, StreamContextInner::Tcp { .. }) {
                bail!(ErrorInt::RtpPacketError {
                    conn_ctx: *conn_ctx,
                    pkt_ctx: *pkt_ctx,
                    stream_ctx: stream_ctx.to_owned(),
                    stream_id,
                    ssrc,
                    sequence_number,
                    description: format!(
                        "Out-of-order packet or large loss; expecting ssrc={:08x?} seq={:?}",
                        self.ssrc, self.seq
                    ),
                });
            } else {
                log::info!(
                    "Skipping out-of-order seq={} when expecting ssrc={:08x?} seq={:?}",
                    sequence_number,
                    self.ssrc,
                    self.seq,
                );
                return Ok(None);
            }
        }
        let timestamp = match timeline.advance_to(header.timestamp()) {
            Ok(ts) => ts,
            Err(description) => bail!(ErrorInt::RtpPacketError {
                conn_ctx: *conn_ctx,
                pkt_ctx: *pkt_ctx,
                stream_ctx: stream_ctx.to_owned(),
                stream_id,
                ssrc,
                sequence_number,
                description,
            }),
        };
        self.seq = Some(Seq {
            init: self
                .seq
                .map(|s| s.init)
                .unwrap_or(InitialExpectation::RtpPacket),
            next: sequence_number.wrapping_add(1),
        });
        self.seen_rtp_packets += 1;
        Ok(Some((timestamp, loss)))
    }

    /// Formats an error description for a failed [`PacketHeader::validate`].
    pub(crate) fn validate_error(
        &self,
        reason: &'static str,
        pkt: crate::inputs::Split<'_>,
    ) -> String {
        format!(
            "corrupt RTP header while expecting seq={:?}: {:?}\n{:#?}",
            self.seq,
            reason,
            crate::hex::LimitedHex::from_split(pkt, 64),
        )
    }

    /// Processes a pre-validated RTP header, returning packet metadata.
    ///
    /// The caller is responsible for calling [`PacketHeader::validate`] first.
    #[allow(clippy::too_many_arguments)]
    pub fn rtp(
        &mut self,
        session_options: &SessionOptions,
        stream_ctx: &StreamContext,
        tool: Option<&super::Tool>,
        conn_ctx: &ConnectionContext,
        pkt_ctx: &PacketContext,
        timeline: &mut Timeline,
        stream_id: usize,
        header: &PacketHeader,
    ) -> Result<Option<PacketMeta>, Error> {
        let Some((timestamp, loss)) = self.rtp_validate(
            session_options,
            stream_ctx,
            tool,
            conn_ctx,
            pkt_ctx,
            timeline,
            stream_id,
            header,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(PacketMeta {
            ctx: *pkt_ctx,
            stream_id,
            timestamp,
            sequence_number: header.sequence_number(),
            ssrc: header.ssrc(),
            mark: header.mark(),
            loss,
        }))
    }

    #[allow(clippy::too_many_arguments)]
    pub fn rtcp(
        &mut self,
        session_options: &SessionOptions,
        stream_ctx: &StreamContext,
        tool: Option<&super::Tool>,
        conn_ctx: &ConnectionContext,
        pkt_ctx: &PacketContext,
        timeline: &mut Timeline,
        stream_id: usize,
        data: Bytes,
    ) -> Result<Option<PacketItem>, String> {
        let first_pkt = crate::rtcp::ReceivedCompoundPacket::validate(&data[..])?;
        let mut rtp_timestamp = None;
        if let Ok(Some(sr)) = first_pkt.as_sender_report() {
            rtp_timestamp = Some(timeline.place(sr.rtp_timestamp()).map_err(
                |mut description| {
                    description.push_str(" in RTCP SR");
                    description
                },
            )?);

            let ssrc = sr.ssrc();
            if matches!(self.ssrc, Some(s) if s.ssrc != ssrc) {
                match self.unknown_rtcp_session {
                    UnknownRtcpSsrcPolicy::AbortSession => {
                        note_stale_live555_data_if_tcp(
                            tool,
                            session_options,
                            conn_ctx,
                            stream_ctx,
                            pkt_ctx,
                        );
                        return Err(format!(
                            "Expected ssrc={:08x?}, got RTCP SR ssrc={:08x}",
                            self.ssrc, ssrc
                        ));
                    }
                    UnknownRtcpSsrcPolicy::Default | UnknownRtcpSsrcPolicy::DropPackets => {
                        if !self.seen_unknown_rtcp_session {
                            warn!(
                                "saw unknown rtcp ssrc {ssrc}; rtp session has ssrc {s:?}",
                                s = self.ssrc
                            );
                            self.seen_unknown_rtcp_session = true;
                        }
                        return Ok(None);
                    }
                    UnknownRtcpSsrcPolicy::ProcessPackets => {}
                }
            } else if self.ssrc.is_none()
                && !matches!(
                    self.unknown_rtcp_session,
                    UnknownRtcpSsrcPolicy::ProcessPackets
                )
            {
                self.ssrc = Some(Ssrc {
                    init: InitialExpectation::RtcpPacket,
                    ssrc,
                });
            }
        }
        self.seen_rtcp_packets += 1;
        Ok(Some(PacketItem::Rtcp(ReceivedCompoundPacket {
            ctx: *pkt_ctx,
            stream_id,
            rtp_timestamp,
            raw: data,
        })))
    }
}

#[cfg(test)]
mod tests {
    use std::net::{IpAddr, Ipv4Addr};

    use crate::client::UdpStreamContext;

    use super::*;

    /// Checks dropping and logging Geovision's extra payload type 50 packets.
    /// On a GV-EBD4701 running V1.02_2021_04_08, these seem to appear after
    /// every IDR frame, with the same sequence number as the final packet in
    /// that frame.
    #[test]
    fn geovision_pt50_packet() {
        let mut timeline = Timeline::new(None, 90_000, None).unwrap();
        let mut parser = InorderParser::new(Some(0xd25614e), None, UnknownRtcpSsrcPolicy::Default);
        let stream_ctx = StreamContext::dummy();

        // Normal packet.
        let pkt = crate::rtp::build_raw_rtp(0x1234, 141000, 105, 0xd25614e, true, *b"foo").unwrap();
        let (header, _payload_range) = PacketHeader::validate(&pkt[..]).unwrap();
        match parser.rtp(
            &SessionOptions::default(),
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            &header,
        ) {
            Ok(Some(_)) => {}
            o => panic!("unexpected packet 1 result: {o:#?}"),
        }

        // Mystery pt=50 packet with same sequence number.
        let pkt = crate::rtp::build_raw_rtp(0x1234, 141000, 50, 0xd25614e, true, *b"bar").unwrap();
        let (header, _payload_range) = PacketHeader::validate(&pkt[..]).unwrap();
        match parser.rtp(
            &SessionOptions::default(),
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            &header,
        ) {
            Ok(None) => {}
            o => panic!("unexpected packet 2 result: {o:#?}"),
        }
    }

    #[test]
    fn out_of_order() {
        let mut timeline = Timeline::new(None, 90_000, None).unwrap();
        let mut parser = InorderParser::new(Some(0xd25614e), None, UnknownRtcpSsrcPolicy::Default);
        let stream_ctx = StreamContext(StreamContextInner::Udp(UdpStreamContext {
            local_ip: IpAddr::V4(Ipv4Addr::UNSPECIFIED),
            peer_ip: IpAddr::V4(Ipv4Addr::UNSPECIFIED),
            local_rtp_port: 0,
            peer_rtp_port: 0,
        }));
        let session_options = SessionOptions::default();
        let pkt = crate::rtp::build_raw_rtp(2, 2, 96, 0xd25614e, true, *b"pkt 2").unwrap();
        let (header, _) = PacketHeader::validate(&pkt[..]).unwrap();
        match parser.rtp(
            &session_options,
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            &header,
        ) {
            Ok(Some(meta)) => {
                assert_eq!(meta.timestamp.elapsed(), 0);
            }
            o => panic!("unexpected packet 2 result: {o:#?}"),
        }

        let pkt = crate::rtp::build_raw_rtp(1, 1, 96, 0xd25614e, true, *b"pkt 1").unwrap();
        let (header, _) = PacketHeader::validate(&pkt[..]).unwrap();
        match parser.rtp(
            &session_options,
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            &header,
        ) {
            Ok(None) => {}
            o => panic!("unexpected packet 1 result: {o:#?}"),
        }

        let pkt = crate::rtp::build_raw_rtp(3, 3, 96, 0xd25614e, true, *b"pkt 3").unwrap();
        let (header, _) = PacketHeader::validate(&pkt[..]).unwrap();
        match parser.rtp(
            &session_options,
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            &header,
        ) {
            Ok(Some(meta)) => {
                // The missing timestamp shouldn't have adjusted time.
                assert_eq!(meta.timestamp.elapsed(), 1);
            }
            o => panic!("unexpected packet 2 result: {o:#?}"),
        }
    }
}
