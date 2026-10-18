// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Handles RTP data as described in
//! [RFC 3550 section 5.1](https://datatracker.ietf.org/doc/html/rfc3550#section-5.1).

use std::ops::Range;

use crate::inputs::Input;

mod receiver;
mod reorder;
mod seq;
mod timeline;

pub use receiver::{ReceiveError, Receiver, ReceiverOptions, SenderReportInfo, SsrcMatch};
pub use reorder::{Pushed, ReorderCounters, ReorderOptions, Reordered, Reorderer};

/// Fixed RTP packet header (no CSRCs, payload, or extensions).
///
/// This is a thin wrapper around the raw 12-byte header, with accessor
/// methods for the individual fields. It can be obtained via
/// [`PacketHeader::validate`] or [`crate::client::RtpPacket::header`].
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct PacketHeader(
    /// ```text
    ///  0                   1                   2                   3
    ///  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    /// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    /// |V=2|P|X|  CC   |M|     PT      |       sequence number         |
    /// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    /// |                           timestamp                           |
    /// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    /// |           synchronization source (SSRC) identifier            |
    /// +=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+
    /// ```
    pub(crate) [u8; Self::LEN as usize],
);

impl PacketHeader {
    pub(crate) const LEN: u16 = 12;

    /// Validates an RTP packet, returning the fixed header and payload range.
    ///
    /// Accepts any [`Input`] implementation: a `&[u8]` or a
    /// [`Split`](crate::inputs::Split) pair of ring-buffer slices.
    pub fn validate<'i>(input: impl Input<'i>) -> Result<(Self, Range<u16>), &'static str> {
        let len = u16::try_from(input.len()).map_err(|_| "too long")?;
        if len < Self::LEN {
            return Err("too short");
        }
        let header = Self(input.peek_array::<{ Self::LEN as usize }>());
        if (header.0[0] & 0b1100_0000) != 2 << 6 {
            return Err("must be version 2");
        }
        let has_padding = (header.0[0] & 0b0010_0000) != 0;
        let has_extension = (header.0[0] & 0b0001_0000) != 0;
        let csrc_count = header.0[0] & 0b0000_1111;
        let csrc_end = Self::LEN + (4 * u16::from(csrc_count));
        let payload_start = if has_extension {
            if input.len() < usize::from(csrc_end + 4) {
                return Err("extension is after end of packet");
            }
            let extension_len = u16::from_be_bytes([
                input.byte_at(usize::from(csrc_end) + 2),
                input.byte_at(usize::from(csrc_end) + 3),
            ]);
            extension_len
                .checked_mul(4)
                .and_then(|e| e.checked_add(csrc_end + 4))
                .ok_or("extension extends beyond maximum packet size")?
        } else {
            csrc_end
        };
        if len < payload_start {
            return Err("payload start is after end of packet");
        }
        let payload_end = if has_padding {
            if len == payload_start {
                return Err("missing padding");
            }
            let padding_len = u16::from(input.byte_at(input.len() - 1));
            if padding_len == 0 {
                return Err("invalid padding length 0");
            }
            let payload_end = len
                .checked_sub(padding_len)
                .ok_or("padding larger than packet")?;
            if payload_end < payload_start {
                return Err("bad padding");
            }
            payload_end
        } else {
            len
        };
        Ok((header, payload_start..payload_end))
    }

    /// Returns the raw 12-byte header.
    #[inline]
    pub fn as_bytes(&self) -> &[u8; Self::LEN as usize] {
        &self.0
    }

    #[inline]
    pub fn mark(&self) -> bool {
        (self.0[1] & 0b1000_0000) != 0
    }

    #[inline]
    pub fn payload_type(&self) -> u8 {
        self.0[1] & 0b0111_1111
    }

    #[inline]
    pub fn sequence_number(&self) -> u16 {
        u16::from_be_bytes([self.0[2], self.0[3]])
    }

    #[inline]
    pub fn timestamp(&self) -> u32 {
        u32::from_be_bytes([self.0[4], self.0[5], self.0[6], self.0[7]])
    }

    #[inline]
    pub fn ssrc(&self) -> u32 {
        u32::from_be_bytes([self.0[8], self.0[9], self.0[10], self.0[11]])
    }
}

impl std::fmt::Debug for PacketHeader {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PacketHeader")
            .field("mark", &self.mark())
            .field("payload_type", &self.payload_type())
            .field("sequence_number", &self.sequence_number())
            .field("timestamp", &self.timestamp())
            .field("ssrc", &self.ssrc())
            .finish()
    }
}

/// Metadata about an RTP packet, as supplied to a depacketizer such as
/// [`crate::codec::VideoDepacketizer`]
/// within a [`crate::buf::PacketRef`].
///
/// `Ctx` is a caller-chosen packet context type, returned with the events the
/// packet contributes to. See [`crate::codec::VideoHandler`].
#[derive(Clone, Copy, Debug)]
pub struct PacketMeta<Ctx> {
    /// The caller's context for this packet.
    pub ctx: Ctx,

    /// The packet's timestamp, extended from the RTP header's 32-bit
    /// timestamp to avoid wraparound.
    pub timestamp: crate::Timestamp,

    /// The RTP sequence number.
    pub sequence_number: u16,

    /// The RTP synchronization source.
    pub ssrc: u32,

    /// The RTP marker bit.
    pub mark: bool,

    /// How this packet relates to the previous one in sequence.
    pub continuity: Continuity,
}

/// How an RTP packet relates to the previous one in its stream, as reported
/// in [`PacketMeta::continuity`].
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub enum Continuity {
    /// The packet directly follows the previous one, or is the first.
    #[default]
    Contiguous,

    /// This many packets were lost immediately before this one, as indicated
    /// by a gap in sequence numbers.
    Lost(std::num::NonZeroU16),

    /// The packet is unrelated to the previous one: the sender restarted its
    /// sequence numbers, as recognized by a [`Reorderer`]. Any number of
    /// packets may have been lost, and timestamps may not be comparable
    /// across it.
    Discontinuity,
}

impl Continuity {
    /// Returns [`Continuity::Lost`] with `packets`, or
    /// [`Continuity::Contiguous`] if `packets` is 0.
    #[inline]
    pub fn from_loss(packets: u16) -> Self {
        std::num::NonZeroU16::new(packets).map_or(Continuity::Contiguous, Continuity::Lost)
    }

    /// Returns true if this packet directly follows the previous one.
    #[inline]
    pub fn is_contiguous(self) -> bool {
        matches!(self, Continuity::Contiguous)
    }

    /// Returns a count for depacketizers' internal bookkeeping, which only
    /// distinguishes zero from nonzero: the packets lost, or 1 at a
    /// discontinuity.
    #[inline]
    pub(crate) fn loss_count(self) -> u16 {
        match self {
            Continuity::Contiguous => 0,
            Continuity::Lost(n) => n.get(),
            Continuity::Discontinuity => 1,
        }
    }
}

/// Builds a raw RTP packet with the given header fields and payload.
#[cfg(test)]
pub(crate) fn build_raw_rtp<P: IntoIterator<Item = u8>>(
    sequence_number: u16,
    timestamp: u32,
    payload_type: u8,
    ssrc: u32,
    mark: bool,
    payload: P,
) -> Result<bytes::Bytes, &'static str> {
    if payload_type >= 0x80 {
        return Err("payload type too large");
    }
    let data: bytes::Bytes = [
        2 << 6, // version=2, no padding, no extensions, no CSRCs.
        if mark { 0b1000_0000 } else { 0 } | payload_type,
    ]
    .into_iter()
    .chain(sequence_number.to_be_bytes())
    .chain(timestamp.to_be_bytes())
    .chain(ssrc.to_be_bytes())
    .chain(payload)
    .collect();
    let _ = u16::try_from(data.len()).map_err(|_| "payload too long")?;
    Ok(data)
}

/// The RTP session state of an outgoing stream.
///
/// Assigns sequence numbers to payloads (such as [`crate::codec::Payload`]s)
/// and maps their timestamps, yielding [`OutgoingPacket`]s. Like the receive
/// side, it owns no packet storage: the caller copies each packet wherever
/// it's going, e.g. into a connection's send buffer. The counterpart on the
/// receive side is the validation a [`crate::client`] session does before
/// handing packets to a depacketizer.
///
/// Use one `Sender` per receiver, so that each receiver sees an ordinary RTP
/// session with its own SSRC and sequence numbers, and so that data dropped
/// for one receiver (see [`crate::codec::PayloadSink::congested`]) doesn't
/// affect the others.
#[derive(Debug)]
pub struct Sender {
    ssrc: u32,
    payload_type: u8,
    next_sequence_number: u16,
    timestamp_offset: u32,
    packet_count: u32,
    octet_count: u32,
}

/// An outgoing RTP packet, as returned by [`Sender::packet`].
///
/// This borrows its payload, so the caller must copy it (e.g. via
/// [`OutgoingPacket::write_to`]) to keep it.
#[derive(Copy, Clone, Debug)]
pub struct OutgoingPacket<'a> {
    /// The packet's RTP header.
    pub header: PacketHeader,

    /// The packet's payload, as a sequence of slices to be concatenated.
    pub data: &'a [&'a [u8]],
}

impl OutgoingPacket<'_> {
    /// Returns the packet's total length in bytes, including its RTP header.
    #[inline]
    pub fn len(&self) -> usize {
        usize::from(PacketHeader::LEN) + self.data.iter().map(|d| d.len()).sum::<usize>()
    }

    /// Returns false; an RTP packet always has a header.
    #[inline]
    pub fn is_empty(&self) -> bool {
        false
    }

    /// Writes the complete packet to `out`.
    pub fn write_to(&self, out: &mut impl bytes::BufMut) {
        out.put_slice(&self.header.0);
        for d in self.data {
            out.put_slice(d);
        }
    }

    /// Returns the complete packet as a new `Vec`.
    pub fn to_vec(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(self.len());
        self.write_to(&mut v);
        v
    }
}

impl Sender {
    /// Creates a new sender.
    ///
    /// RFC 3550 recommends choosing `ssrc`, `initial_sequence_number`, and
    /// `timestamp_offset` randomly.
    ///
    /// # Panics
    ///
    /// If `payload_type` doesn't fit in 7 bits.
    pub fn new(
        payload_type: u8,
        ssrc: u32,
        initial_sequence_number: u16,
        timestamp_offset: u32,
    ) -> Self {
        assert!(payload_type < 0x80, "payload type {payload_type} too large");
        Self {
            ssrc,
            payload_type,
            next_sequence_number: initial_sequence_number,
            timestamp_offset,
            packet_count: 0,
            octet_count: 0,
        }
    }

    /// Returns the SSRC.
    #[inline]
    pub fn ssrc(&self) -> u32 {
        self.ssrc
    }

    /// Returns the sequence number the next packet will have, e.g. for a
    /// `PLAY` response's `RTP-Info` header.
    #[inline]
    pub fn next_sequence_number(&self) -> u16 {
        self.next_sequence_number
    }

    /// Returns the RTP timestamp that will represent `timestamp`.
    #[inline]
    pub fn rtp_timestamp(&self, timestamp: crate::Timestamp) -> u32 {
        (timestamp.timestamp as u32).wrapping_add(self.timestamp_offset)
    }

    /// Returns the number of packets sent so far, for RTCP sender reports.
    #[inline]
    pub fn packet_count(&self) -> u32 {
        self.packet_count
    }

    /// Returns the number of payload octets sent so far, for RTCP sender
    /// reports.
    #[inline]
    pub fn octet_count(&self) -> u32 {
        self.octet_count
    }

    /// Assigns the next sequence number to a payload with the given
    /// timestamp, marker bit, and data (as a sequence of slices to be
    /// concatenated), returning the packet.
    ///
    /// For a [`crate::codec::Payload`] `p`, pass `p.timestamp()`, `p.mark()`,
    /// and `p.data()`; or use [`Sender::sink`].
    ///
    /// # Panics
    ///
    /// If the packet exceeds 65,535 bytes.
    pub fn packet<'a>(
        &mut self,
        timestamp: crate::Timestamp,
        mark: bool,
        data: &'a [&'a [u8]],
    ) -> OutgoingPacket<'a> {
        let payload_len: usize = data.iter().map(|d| d.len()).sum();
        let len = usize::from(PacketHeader::LEN) + payload_len;
        assert!(
            len <= usize::from(u16::MAX),
            "RTP packet of {len} bytes is too long"
        );
        let sequence_number = self.next_sequence_number;
        self.next_sequence_number = sequence_number.wrapping_add(1);
        self.packet_count = self.packet_count.wrapping_add(1);
        self.octet_count = self.octet_count.wrapping_add(payload_len as u32);
        let mut header = [0; PacketHeader::LEN as usize];
        header[0] = 2 << 6; // version=2, no padding, no extensions, no CSRCs.
        header[1] = if mark { 0b1000_0000 } else { 0 } | self.payload_type;
        header[2..4].copy_from_slice(&sequence_number.to_be_bytes());
        header[4..8].copy_from_slice(&self.rtp_timestamp(timestamp).to_be_bytes());
        header[8..12].copy_from_slice(&self.ssrc.to_be_bytes());
        OutgoingPacket {
            header: PacketHeader(header),
            data,
        }
    }

    /// Skips a sequence number, so receivers see lost data as packet loss.
    pub fn skip(&mut self) {
        self.next_sequence_number = self.next_sequence_number.wrapping_add(1);
    }

    /// Returns an RTCP sender report stating that `timestamp` corresponds to
    /// wall time `ntp`.
    ///
    /// This is a compound packet's first (and only mandatory) part; see
    /// [RFC 3550 section 6.4.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.1).
    /// It has no reception report blocks.
    pub fn sender_report(&self, ntp: crate::NtpTimestamp, timestamp: crate::Timestamp) -> [u8; 28] {
        let mut sr = [0; 28];
        sr[0] = 2 << 6; // version=2, no padding, no reception reports.
        sr[1] = 200; // SR
        sr[2..4].copy_from_slice(&6u16.to_be_bytes()); // length in 32-bit words, minus one.
        sr[4..8].copy_from_slice(&self.ssrc.to_be_bytes());
        sr[8..16].copy_from_slice(&ntp.0.to_be_bytes());
        sr[16..20].copy_from_slice(&self.rtp_timestamp(timestamp).to_be_bytes());
        sr[20..24].copy_from_slice(&self.packet_count.to_be_bytes());
        sr[24..28].copy_from_slice(&self.octet_count.to_be_bytes());
        sr
    }

    /// Returns a [`crate::codec::PayloadSink`] which passes each packet to
    /// `f`, and skips a sequence number on each discontinuity.
    ///
    /// The sink is never congested; to throttle, wrap `Sender` in a sink of
    /// your own.
    pub fn sink<F: FnMut(&OutgoingPacket<'_>)>(&mut self, f: F) -> SenderSink<'_, F> {
        SenderSink { sender: self, f }
    }
}

/// Returned by [`Sender::sink`].
pub struct SenderSink<'a, F> {
    sender: &'a mut Sender,
    f: F,
}

impl<F: FnMut(&OutgoingPacket<'_>)> crate::codec::PayloadSink for SenderSink<'_, F> {
    fn payload(&mut self, payload: &crate::codec::Payload<'_>) {
        (self.f)(
            &self
                .sender
                .packet(payload.timestamp(), payload.mark(), payload.data()),
        );
    }

    fn discontinuity(&mut self) {
        self.sender.skip();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::init_logging;

    #[test]
    pub fn pkt_with_extension() {
        init_logging();
        let data = b"\x90\x60\x4c\x62\x01\xbb\x3c\xb5\x1c\x04\x15\xb1\xab\xac\x00\x03\
                     \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x67\x64\x00\x32\
                     \xac\x3c\x6b\x81\x7c\x05\x46\x9b\x82\x80\x82\xa0\x00\x00\x03\x00\
                     \x20\x00\x00\x07\x90\x80\x00";
        let (header, payload_range) = PacketHeader::validate(&data[..]).unwrap();
        assert_eq!(payload_range, 28..55);
        assert_eq!(data[payload_range.start as usize], 0x67);
        assert!(!header.mark());
    }

    #[test]
    fn sender() {
        let mut s = Sender::new(96, 0x1234_5678, 0xffff, 10);
        let ts = crate::Timestamp::new(100, std::num::NonZeroU32::new(90_000).unwrap(), 0).unwrap();
        let pkt = s.packet(ts, true, &[b"ab", b"cde"]);
        let raw = pkt.to_vec();
        assert_eq!(raw.len(), pkt.len());
        let (header, range) = PacketHeader::validate(&raw[..]).unwrap();
        assert_eq!(header, pkt.header);
        assert_eq!(&raw[usize::from(range.start)..], b"abcde");
        assert!(header.mark());
        assert_eq!(header.payload_type(), 96);
        assert_eq!(header.sequence_number(), 0xffff);
        assert_eq!(header.timestamp(), 110);
        assert_eq!(header.ssrc(), 0x1234_5678);
        assert_eq!(s.next_sequence_number(), 0);
        s.skip();
        assert_eq!(s.next_sequence_number(), 1);

        let sr = s.sender_report(crate::NtpTimestamp(0x0102_0304_0506_0708), ts);
        let (pkt, rest) = crate::rtcp::PacketRef::parse(&sr[..]).unwrap();
        assert!(rest.is_empty());
        let sr = pkt.as_sender_report().unwrap().unwrap();
        assert_eq!(sr.ssrc(), 0x1234_5678);
        assert_eq!(sr.ntp_timestamp().0, 0x0102_0304_0506_0708);
        assert_eq!(sr.rtp_timestamp(), 110);
    }
}
