// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTP and RTCP handling; see [RFC 3550](https://datatracker.ietf.org/doc/html/rfc3550).

use bytes::Bytes;
use log::{debug, warn, info};
use std::collections::BTreeMap;

use crate::client::PacketItem;
use crate::rtcp::ReceivedCompoundPacket;
use crate::rtp::{RawPacket, ReceivedPacket};
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
/// When using UDP, maintains a reorder buffer to handle out-of-order packets.
/// When using TCP, fails on out-of-order packets.
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
/// The maximum number of packets to hold in the reorder buffer
const MAX_REORDER_BUFFER_SIZE: usize = 32;

/// Maximum sequence number difference to consider as out-of-order
/// rather than a wrap-around or reset
const MAX_OUT_OF_ORDER_DIFF: u16 = 0x8000;

/// Structure to hold packets for reordering
#[derive(Debug)]
struct ReorderBuffer {
    /// Map of sequence number to buffered packet data
    packets: BTreeMap<u16, BufferedPacket>,
    
    /// Maximum buffer size
    max_size: usize,
}

/// Information about a buffered packet
#[derive(Debug)]
struct BufferedPacket {
    /// The packet data
    data: Bytes,
    
    /// Packet context
    pkt_ctx: PacketContext,
    
    /// Raw timestamp from the packet
    timestamp: u32,
}

impl ReorderBuffer {
    fn new(max_size: usize) -> Self {
        Self {
            packets: BTreeMap::new(),
            max_size,
        }
    }
    
    /// Add a packet to the buffer
    fn add(&mut self, seq: u16, data: Bytes, pkt_ctx: PacketContext, timestamp: u32) -> bool {
        // If buffer is full, don't add more packets
        if self.packets.len() >= self.max_size {
            return false;
        }
        
        self.packets.insert(seq, BufferedPacket { 
            data, 
            pkt_ctx,
            timestamp,
        });
        true
    }
    
    /// Get next packet if it matches the expected sequence number
    fn get_next(&mut self, next_seq: u16) -> Option<(Bytes, PacketContext, u32)> {
        if let Some(packet) = self.packets.remove(&next_seq) {
            Some((packet.data, packet.pkt_ctx, packet.timestamp))
        } else {
            None
        }
    }
    
    /// Count of packets in buffer
    fn len(&self) -> usize {
        self.packets.len()
    }
    
    /// Clear all packets older than the given sequence number
    fn clear_old_packets(&mut self, next_seq: u16) {
        let to_remove: Vec<_> = self.packets
            .keys()
            .filter(|&&seq| {
                // Calculate the distance, accounting for wrapping
                let diff = next_seq.wrapping_sub(seq);
                // If difference is large, it means the sequence is ahead of next_seq (out of order)
                // If difference is small, it means the sequence is behind next_seq (old packet)
                diff < MAX_OUT_OF_ORDER_DIFF
            })
            .copied()
            .collect();
        
        for seq in to_remove {
            self.packets.remove(&seq);
        }
    }
}

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
    
    /// Buffer for out-of-order packets in UDP mode
    reorder_buffer: ReorderBuffer,
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
            reorder_buffer: ReorderBuffer::new(MAX_REORDER_BUFFER_SIZE),
        }
    }
    
    /// Process any buffered packets that are ready to be delivered
    fn process_buffered_packets(
        &mut self,
        session_options: &SessionOptions,
        stream_ctx: &StreamContext,
        tool: Option<&super::Tool>,
        conn_ctx: &ConnectionContext,
        timeline: &mut Timeline,
        stream_id: usize,
    ) -> Result<Vec<PacketItem>, Error> {
        let mut results = Vec::new();
        
        if self.seq.is_none() {
            return Ok(results);
        }
        
        while let Some((data, pkt_ctx, _timestamp)) = self.reorder_buffer.get_next(self.seq.unwrap().next) {
            // Process the next packet from the buffer
            if let Some(packet_item) = self.process_packet(
                session_options, 
                stream_ctx, 
                tool, 
                conn_ctx, 
                &pkt_ctx, 
                timeline, 
                stream_id, 
                data,
            )? {
                results.push(packet_item);
            }
        }
        
        Ok(results)
    }
    
    /// Process a single RTP packet and update the sequence number
    fn process_packet(
        &mut self,
        session_options: &SessionOptions,
        stream_ctx: &StreamContext,
        tool: Option<&super::Tool>,
        conn_ctx: &ConnectionContext,
        pkt_ctx: &PacketContext,
        timeline: &mut Timeline,
        stream_id: usize,
        data: Bytes,
    ) -> Result<Option<PacketItem>, Error> {
        let (raw, payload_range) = RawPacket::new(data.clone()).map_err(|e| {
            wrap!(ErrorInt::PacketError {
                conn_ctx: *conn_ctx,
                stream_ctx: stream_ctx.to_owned(),
                pkt_ctx: *pkt_ctx,
                stream_id,
                description: format!(
                    "corrupt RTP header while expecting seq={:?}: {:?}\n{:#?}",
                    &self.seq,
                    e.reason,
                    crate::hex::LimitedHex::new(&e.data[..], 64),
                ),
            })
        })?;
        
        // Skip pt=50 packets, sent by at least Geovision cameras. I'm not sure
        // what purpose these serve, but they have the same sequence number as
        // the packet immediately before. In TCP streams, this can cause an
        // "Out-of-order packet or large loss" error. In UDP streams, if these
        // are delivered out of order, they will cause the more important other
        // packet with the same sequence number to be skipped.
        if raw.payload_type() == 50 {
            debug!("skipping pkt with invalid payload type 50");
            return Ok(None);
        }
        
        let sequence_number = raw.sequence_number();
        let ssrc = raw.ssrc();
        
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
        
        let timestamp = match timeline.advance_to(raw.timestamp()) {
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
        
        // Packet is valid - update the expected sequence number
        self.seq = Some(Seq {
            init: self
                .seq
                .map(|s| s.init)
                .unwrap_or(InitialExpectation::RtpPacket),
            next: sequence_number.wrapping_add(1),
        });
        self.seen_rtp_packets += 1;
        
        let loss = if let Some(expected_seq) = self.seq.map(|s| s.next.wrapping_sub(1)) {
            let loss = sequence_number.wrapping_sub(expected_seq);
            if loss > 0 && loss < MAX_OUT_OF_ORDER_DIFF {
                loss
            } else {
                0
            }
        } else {
            0
        };
        
        Ok(Some(PacketItem::Rtp(ReceivedPacket {
            ctx: *pkt_ctx,
            stream_id,
            timestamp,
            raw,
            payload_range,
            loss,
        })))
    }

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
        data: Bytes,
    ) -> Result<Option<PacketItem>, Error> {
        // Try to parse the packet first to verify it's valid and get the sequence number
        let parse_result = RawPacket::new(data.clone());
        if let Err(e) = &parse_result {
            return Err(wrap!(ErrorInt::PacketError {
                conn_ctx: *conn_ctx,
                stream_ctx: stream_ctx.to_owned(),
                pkt_ctx: *pkt_ctx,
                stream_id,
                description: format!(
                    "corrupt RTP header while expecting seq={:?}: {:?}\n{:#?}",
                    &self.seq,
                    e.reason,
                    crate::hex::LimitedHex::new(&e.data[..], 64),
                ),
            }));
        }
        
        let (raw, _) = parse_result.unwrap();
        
        // Skip pt=50 packets, sent by at least Geovision cameras.
        if raw.payload_type() == 50 {
            debug!("skipping pkt with invalid payload type 50");
            return Ok(None);
        }

        let sequence_number = raw.sequence_number();
        let ssrc = raw.ssrc();
        
        // Check SSRC consistency
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
        
        // Get the expected next sequence number if available
        let expected_seq = self.seq.map(|s| s.next);
        
        // If we have a sequence number and this is UDP
        if let Some(next_seq) = expected_seq {
            let is_udp = matches!(stream_ctx.0, StreamContextInner::Udp { .. });
            
            // Check if the packet is out of order
            let loss = sequence_number.wrapping_sub(next_seq);
            
            // If we're using TCP, fail on out-of-order packets
            if loss > MAX_OUT_OF_ORDER_DIFF && !is_udp {
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
            }
            
            // For UDP, handle out-of-order packets using the reorder buffer
            if is_udp {
                // If the packet is in order or we have not established a sequence yet
                if sequence_number == next_seq {
                    // This packet is the next expected one - process it directly
                    let result = self.process_packet(
                        session_options,
                        stream_ctx,
                        tool,
                        conn_ctx,
                        pkt_ctx,
                        timeline,
                        stream_id,
                        data,
                    )?;
                    
                    // Process any buffered packets that are now ready
                    let mut buffered_results = self.process_buffered_packets(
                        session_options,
                        stream_ctx,
                        tool,
                        conn_ctx,
                        timeline,
                        stream_id,
                    )?;
                    
                    // If we processed any buffered packets, log it
                    if !buffered_results.is_empty() {
                        info!("Processed {} buffered packet(s) after receiving seq={}", 
                             buffered_results.len(), sequence_number);
                    }
                    
                    // If we have buffered results, return the first one and keep the rest for next time
                    if !buffered_results.is_empty() {
                        // Return the first buffered result if we didn't get a result from the current packet
                        if result.is_none() {
                            return Ok(Some(buffered_results.remove(0)));
                        }
                        
                        // Otherwise return the current packet result
                        return Ok(result);
                    }
                    
                    // No buffered results, just return the current packet result
                    return Ok(result);
                } else if loss < MAX_OUT_OF_ORDER_DIFF {
                    // This is a future packet - add it to the reorder buffer
                    if self.reorder_buffer.add(sequence_number, data, *pkt_ctx, raw.timestamp()) {
                        info!(
                            "Buffered out-of-order packet seq={} (expecting seq={}), buffer size: {}",
                            sequence_number,
                            next_seq,
                            self.reorder_buffer.len()
                        );
                    } else {
                        info!(
                            "Buffer full, dropping out-of-order packet seq={} (expecting seq={})",
                            sequence_number,
                            next_seq
                        );
                    }
                    
                    // Clear old packets if our buffer is getting full
                    if self.reorder_buffer.len() > MAX_REORDER_BUFFER_SIZE / 2 {
                        self.reorder_buffer.clear_old_packets(next_seq);
                    }
                    
                    return Ok(None);
                } else {
                    // This is a past packet - we've already moved beyond it
                    info!(
                        "Skipping late out-of-order packet seq={} (expecting seq={})",
                        sequence_number,
                        next_seq
                    );
                    return Ok(None);
                }
            }
        }
        
        // For in-order packets or if we don't have a sequence yet,
        // process the packet directly
        return self.process_packet(
            session_options,
            stream_ctx,
            tool,
            conn_ctx,
            pkt_ctx,
            timeline,
            stream_id,
            data,
        );
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
        let (pkt, _payload_range) = crate::rtp::RawPacketBuilder {
            sequence_number: 0x1234,
            timestamp: 141000,
            payload_type: 105,
            ssrc: 0xd25614e,
            mark: true,
        }
        .build(*b"foo")
        .unwrap();
        match parser.rtp(
            &SessionOptions::default(),
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            pkt.0,
        ) {
            Ok(Some(PacketItem::Rtp(_))) => {}
            o => panic!("unexpected packet 1 result: {o:#?}"),
        }

        // Mystery pt=50 packet with same sequence number.
        let (pkt, _payload_range) = crate::rtp::RawPacketBuilder {
            sequence_number: 0x1234,
            timestamp: 141000,
            payload_type: 50,
            ssrc: 0xd25614e,
            mark: true,
        }
        .build(*b"bar")
        .unwrap();
        match parser.rtp(
            &SessionOptions::default(),
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            pkt.0,
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
        
        // Send packets out of order: 2, 1, 3
        
        // First send packet 2
        let (pkt, _payload_range) = crate::rtp::RawPacketBuilder {
            sequence_number: 2,
            timestamp: 2,
            payload_type: 96,
            ssrc: 0xd25614e,
            mark: true,
        }
        .build(*b"pkt 2")
        .unwrap();
        match parser.rtp(
            &session_options,
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            pkt.0,
        ) {
            Ok(Some(PacketItem::Rtp(p))) => {
                assert_eq!(p.timestamp().elapsed(), 0);
                assert_eq!(p.raw.sequence_number(), 2);
            }
            o => panic!("unexpected packet 2 result: {o:#?}"),
        }

        // Now send packet 1 (out of order, but should be buffered now)
        let (pkt, _payload_range) = crate::rtp::RawPacketBuilder {
            sequence_number: 1,
            timestamp: 1,
            payload_type: 96,
            ssrc: 0xd25614e,
            mark: true,
        }
        .build(*b"pkt 1")
        .unwrap();
        match parser.rtp(
            &session_options,
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            pkt.0,
        ) {
            // With the reorder buffer, it should still return None because packet 1 is older than
            // what we're expecting next (which is 3)
            Ok(None) => {}
            o => panic!("unexpected packet 1 result: {o:#?}"),
        }

        // Send packet 4 (out of order, gets buffered)
        let (pkt, _payload_range) = crate::rtp::RawPacketBuilder {
            sequence_number: 4,
            timestamp: 4,
            payload_type: 96,
            ssrc: 0xd25614e,
            mark: true,
        }
        .build(*b"pkt 4")
        .unwrap();
        match parser.rtp(
            &session_options,
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            pkt.0,
        ) {
            // Buffer packet 4 for later
            Ok(None) => {}
            o => panic!("unexpected packet 4 result: {o:#?}"),
        }
        
        // Now send packet 3 (in order) - should process 3 and then immediately process 4 from buffer
        let (pkt, _payload_range) = crate::rtp::RawPacketBuilder {
            sequence_number: 3,
            timestamp: 3,
            payload_type: 96,
            ssrc: 0xd25614e,
            mark: true,
        }
        .build(*b"pkt 3")
        .unwrap();
        match parser.rtp(
            &session_options,
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            pkt.0,
        ) {
            Ok(Some(PacketItem::Rtp(p))) => {
                // Verify we get packet 3
                assert_eq!(p.raw.sequence_number(), 3);
                assert_eq!(p.timestamp().elapsed(), 1);
            }
            o => panic!("unexpected packet 3 result: {o:#?}"),
        }
        
        // The next call should return packet 4 from the buffer
        let (pkt, _payload_range) = crate::rtp::RawPacketBuilder {
            sequence_number: 5,
            timestamp: 5,
            payload_type: 96,
            ssrc: 0xd25614e,
            mark: true,
        }
        .build(*b"pkt 5")
        .unwrap();
        match parser.rtp(
            &session_options,
            &stream_ctx,
            None,
            &ConnectionContext::dummy(),
            &PacketContext::dummy(),
            &mut timeline,
            0,
            pkt.0,
        ) {
            Ok(Some(PacketItem::Rtp(p))) => {
                // Verify we get packet 5
                assert_eq!(p.raw.sequence_number(), 5);
                assert_eq!(p.timestamp().elapsed(), 3);
            }
            o => panic!("unexpected packet 5 result: {o:#?}"),
        }
    }
}
