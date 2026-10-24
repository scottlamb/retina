// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTP and RTCP handling; see [RFC 3550](https://datatracker.ietf.org/doc/html/rfc3550).

use bytes::Bytes;
use log::{debug, warn};

use crate::client::PacketItem;
use crate::rtcp::ReceivedCompoundPacket;
use crate::rtp::{PacketHeader, ReceivedPacketMeta};
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
    ) -> Result<Option<ReceivedPacketMeta<PacketContext>>, Error> {
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
        Ok(Some(ReceivedPacketMeta {
            ctx: *pkt_ctx,
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

/// RTP/RTCP marshaller for a stream that Retina sends, such as an ONVIF
/// audio backchannel.
///
/// Assigns the SSRC, sequence numbers, and a random timestamp offset as
/// described in [RFC 3550 section 5.1](https://datatracker.ietf.org/doc/html/rfc3550#section-5.1)
/// and generates RTCP sender reports (RFC 3550 section 6.4.1) with an SDES
/// `CNAME` (section 6.5.1), as required for every compound RTCP packet
/// (section 6.1).
#[derive(Debug)]
pub(crate) struct Sender {
    pub(super) ssrc: u32,
    pub(super) next_seq: u16,

    /// Added to the caller-supplied timestamps.
    pub(super) timestamp_offset: u32,

    /// The payload type: the first one offered in the SDP.
    payload_type: u8,

    /// The RTP clock rate from the SDP, used to extrapolate the sender
    /// report's RTP timestamp.
    clock_rate_hz: u32,

    /// The time the most recent RTP packet was sent and its RTP timestamp
    /// (offset included), or `None` before the first.
    ///
    /// Sender reports extrapolate the RTP timestamp from this anchor and the
    /// clock rate. Anchoring to the latest packet rather than the first keeps
    /// any drift between the caller's timestamps and the wall clock from
    /// accumulating over the session.
    anchor: Option<(tokio::time::Instant, u32)>,

    /// RTP packets sent so far, for the sender report.
    packet_count: u32,

    /// RTP payload octets sent so far, for the sender report.
    octet_count: u32,

    /// When to send the next sender report, or `None` to send one after the
    /// next RTP packet.
    ///
    /// Reports follow the receiver reports' schedule; see
    /// [`super::receiver_report::regular_interval`].
    ///
    /// The first report follows the first RTP packet without delay: [RFC 3550
    /// section 6.2](https://datatracker.ietf.org/doc/html/rfc3550#section-6.2)
    /// says that for unicast sessions "the delay before sending the initial
    /// compound RTCP packet MAY be zero".
    pub(super) next_report: Option<tokio::time::Instant>,

    pub(super) cname: Box<str>,
}

impl Sender {
    pub(crate) fn new(payload_type: u8, clock_rate_hz: u32) -> Self {
        use base64::Engine as _;
        use rand::Rng as _;
        let mut rng = rand::thread_rng();
        let cname_bytes: [u8; 12] = rng.r#gen();
        Self {
            ssrc: rng.r#gen(),
            next_seq: rng.r#gen(),
            timestamp_offset: rng.r#gen(),
            payload_type,
            clock_rate_hz,
            anchor: None,
            packet_count: 0,
            octet_count: 0,
            next_report: None,

            // RFC 7022 section 4.2 recommends a random 96-bit CNAME, base64-encoded.
            cname: base64::engine::general_purpose::STANDARD
                .encode(cname_bytes)
                .into_boxed_str(),
        }
    }

    /// Appends the RTP packet for `pkt`, sent at `now`, to `out` and updates
    /// counters.
    ///
    /// The caller has validated the payload length.
    pub(crate) fn write_rtp(
        &mut self,
        now: tokio::time::Instant,
        pkt: &crate::rtp::SendingPacket,
        out: &mut bytes::BytesMut,
    ) {
        let timestamp = pkt.timestamp.wrapping_add(self.timestamp_offset);
        self.anchor = Some((now, timestamp));
        out.extend_from_slice(&[
            2 << 6, // version=2, no padding, no extension, no CSRCs.
            (u8::from(pkt.mark) << 7) | self.payload_type,
        ]);
        out.extend_from_slice(&self.next_seq.to_be_bytes());
        out.extend_from_slice(&timestamp.to_be_bytes());
        out.extend_from_slice(&self.ssrc.to_be_bytes());
        out.extend_from_slice(&pkt.payload);
        self.next_seq = self.next_seq.wrapping_add(1);
        self.packet_count = self.packet_count.wrapping_add(1);

        // RFC 3550 section 6.4.1: the octet count wraps around.
        self.octet_count = self.octet_count.wrapping_add(pkt.payload.len() as u32);
    }

    /// Returns true if a sender report is due at `now`, after an RTP packet has been sent.
    pub(crate) fn report_due(&self, now: tokio::time::Instant) -> bool {
        self.next_report.is_none_or(|t| now >= t)
    }

    /// Returns the RTP timestamp corresponding to `now`.
    ///
    /// This extrapolates from the most recent packet sent, at the clock rate, as
    /// [RFC 3550 section 6.4.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.1)
    /// describes: the result need not match any packet's timestamp. It wraps
    /// like any RTP timestamp. Before the first packet, it's the timestamp
    /// offset.
    fn rtp_timestamp_at(&self, now: tokio::time::Instant) -> u32 {
        let Some((sent, sent_timestamp)) = self.anchor else {
            return self.timestamp_offset;
        };
        let elapsed = now.saturating_duration_since(sent);

        // Can't overflow: the nanoseconds fit in 94 bits and the clock rate in
        // 32. Truncating to 32 bits is the RTP timestamp's wraparound.
        let ticks = elapsed.as_nanos() * u128::from(self.clock_rate_hz) / 1_000_000_000;
        sent_timestamp.wrapping_add(ticks as u32)
    }

    /// Appends a compound RTCP packet (sender report and SDES `CNAME`) to `out`
    /// and schedules the next one.
    ///
    /// `now` and `ntp` are the current monotonic and wall times. RFC 3550
    /// section 6.4.1 says the report's NTP and RTP timestamps describe the same
    /// instant, which need not be when any packet was sampled. The RTP
    /// timestamp is extrapolated from the most recent packet sent; see
    /// [`Sender::rtp_timestamp_at`].
    pub(crate) fn write_sender_report(
        &mut self,
        now: tokio::time::Instant,
        ntp: crate::NtpTimestamp,
        out: &mut bytes::BytesMut,
    ) {
        // Sender report, RFC 3550 section 6.4.1, with no report blocks: Retina
        // receives nothing in this RTP session.
        out.extend_from_slice(&[
            2 << 6, // version=2, no padding, reception report count=0.
            200,    // packet type = SR.
            0,
            6, // length in 32-bit words minus one.
        ]);
        out.extend_from_slice(&self.ssrc.to_be_bytes());
        out.extend_from_slice(&ntp.0.to_be_bytes());
        out.extend_from_slice(&self.rtp_timestamp_at(now).to_be_bytes());
        out.extend_from_slice(&self.packet_count.to_be_bytes());
        out.extend_from_slice(&self.octet_count.to_be_bytes());

        super::receiver_report::write_sdes_cname(self.ssrc, &self.cname, out);
        self.next_report =
            Some(now + super::receiver_report::regular_interval(&mut rand::thread_rng()));
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
        let pkt =
            crate::client::build_raw_rtp(0x1234, 141000, 105, 0xd25614e, true, *b"foo").unwrap();
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
        let pkt =
            crate::client::build_raw_rtp(0x1234, 141000, 50, 0xd25614e, true, *b"bar").unwrap();
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

    /// Sender reports follow the first RTP packet, then come every 2.5–7.5
    /// seconds (RFC 3550 sections 6.2 and 6.3.1) while packets are sent.
    #[test]
    fn sender_report_schedule() {
        let mut sender = Sender::new(0, 8_000);
        let start = tokio::time::Instant::now();
        let pkt = crate::rtp::SendingPacket::new(0, 0, Bytes::from_static(b"x"));
        let mut out = bytes::BytesMut::new();
        sender.write_rtp(start, &pkt, &mut out);
        assert!(sender.report_due(start));
        sender.write_sender_report(start, crate::NtpTimestamp(0), &mut out);
        assert_eq!(out.len(), 13 + 28 + 28);
        assert!(!sender.report_due(start));
        // 5 s × [0.5, 1.5) / (e - 3/2) is about [2.0521, 6.1563) s.
        assert!(!sender.report_due(start + std::time::Duration::from_millis(2_052)));
        assert!(sender.report_due(start + std::time::Duration::from_millis(6_157)));
    }

    /// The sender report's RTP timestamp describes the instant the report is
    /// built, extrapolated at the clock rate (RFC 3550 section 6.4.1) from the
    /// most recent packet, so drift in the caller's timestamps doesn't
    /// accumulate. It wraps.
    #[test]
    fn sender_report_rtp_timestamp() {
        let mut sender = Sender::new(0, 8_000);
        sender.timestamp_offset = 0xffff_f000;
        let start = tokio::time::Instant::now();
        assert_eq!(sender.rtp_timestamp_at(start), 0xffff_f000);
        let mut out = bytes::BytesMut::new();
        sender.write_rtp(
            start,
            &crate::rtp::SendingPacket::new(0, 0x100, Bytes::from_static(b"x")),
            &mut out,
        );
        assert_eq!(sender.anchor, Some((start, 0xffff_f100)));

        // 500 ms at 8 kHz is 4,000 ticks, which wraps past 2^32.
        let later = start + std::time::Duration::from_millis(500);
        out.clear();
        sender.write_sender_report(later, crate::NtpTimestamp(0x1234), &mut out);
        assert_eq!(
            &out[8..20],
            b"\x00\x00\x00\x00\x00\x00\x12\x34\x00\x00\x00\xa0"
        );
        assert_eq!(
            sender.rtp_timestamp_at(start + std::time::Duration::from_micros(125)),
            0xffff_f101
        );

        // A packet sent then whose timestamp has drifted 160 ticks behind
        // becomes the new anchor.
        sender.write_rtp(
            later,
            &crate::rtp::SendingPacket::new(0, 0x1000, Bytes::from_static(b"x")),
            &mut out,
        );
        assert_eq!(sender.anchor, Some((later, 0)));
        assert_eq!(sender.rtp_timestamp_at(later), 0);
        assert_eq!(
            sender.rtp_timestamp_at(later + std::time::Duration::from_millis(250)),
            2_000
        );
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
        let pkt = crate::client::build_raw_rtp(2, 2, 96, 0xd25614e, true, *b"pkt 2").unwrap();
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

        let pkt = crate::client::build_raw_rtp(1, 1, 96, 0xd25614e, true, *b"pkt 1").unwrap();
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

        let pkt = crate::client::build_raw_rtp(3, 3, 96, 0xd25614e, true, *b"pkt 3").unwrap();
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
