// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Handles RTP data as described in
//! [RFC 3550 section 5.1](https://datatracker.ietf.org/doc/html/rfc3550#section-5.1).

use std::ops::Range;

use crate::inputs::Input;

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

    /// The number of packets lost immediately before this one, as determined
    /// by a gap in sequence numbers.
    pub loss: u16,
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
/// Turns payloads (such as [`crate::codec::Payload`]s) into complete RTP packets, assigning
/// sequence numbers and mapping timestamps. The counterpart on the receive
/// side is the validation a [`crate::client`] session does before handing
/// packets to a depacketizer.
///
/// Every packet built by one `Sender` has the same SSRC and one sequence of
/// sequence numbers, so identical packets can be sent to any number of
/// receivers.
#[derive(Debug)]
pub struct Sender {
    ssrc: u32,
    payload_type: u8,
    next_sequence_number: u16,
    timestamp_offset: u32,

    /// Space for packets, split off as they're built, to amortize allocation.
    arena: bytes::BytesMut,
}

/// A complete outgoing RTP packet, as built by [`Sender`].
#[derive(Clone, Debug)]
pub struct OutgoingPacket {
    /// The packet, including its RTP header.
    pub raw: bytes::Bytes,

    /// The packet's sequence number.
    pub sequence_number: u16,
}

impl Sender {
    const ARENA_SIZE: usize = 64 * 1024;

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
            arena: bytes::BytesMut::new(),
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

    /// Builds a packet with the given timestamp, marker bit, and payload
    /// (as a sequence of slices to be concatenated).
    ///
    /// For a [`crate::codec::Payload`] `p`, pass `p.timestamp()`, `p.mark()`,
    /// and `p.data()`; or use [`Sender::sink`].
    ///
    /// # Panics
    ///
    /// If the packet exceeds 65,535 bytes.
    pub fn packet(
        &mut self,
        timestamp: crate::Timestamp,
        mark: bool,
        payload: &[&[u8]],
    ) -> OutgoingPacket {
        let payload_len: usize = payload.iter().map(|d| d.len()).sum();
        let len = usize::from(PacketHeader::LEN) + payload_len;
        assert!(
            len <= usize::from(u16::MAX),
            "RTP packet of {len} bytes is too long"
        );
        if self.arena.capacity() < len {
            self.arena.reserve(len.max(Self::ARENA_SIZE));
        }
        let sequence_number = self.next_sequence_number;
        self.next_sequence_number = sequence_number.wrapping_add(1);
        self.arena.extend_from_slice(&[
            2 << 6, // version=2, no padding, no extensions, no CSRCs.
            if mark { 0b1000_0000 } else { 0 } | self.payload_type,
        ]);
        self.arena.extend_from_slice(&sequence_number.to_be_bytes());
        self.arena
            .extend_from_slice(&self.rtp_timestamp(timestamp).to_be_bytes());
        self.arena.extend_from_slice(&self.ssrc.to_be_bytes());
        for d in payload {
            self.arena.extend_from_slice(d);
        }
        OutgoingPacket {
            raw: self.arena.split().freeze(),
            sequence_number,
        }
    }

    /// Skips a sequence number, so receivers see lost data as packet loss.
    pub fn skip(&mut self) {
        self.next_sequence_number = self.next_sequence_number.wrapping_add(1);
    }

    /// Returns a [`crate::codec::PayloadSink`] which builds packets and passes
    /// them to `f`, skipping a sequence number on each discontinuity.
    pub fn sink<F: FnMut(OutgoingPacket)>(&mut self, f: F) -> SenderSink<'_, F> {
        SenderSink { sender: self, f }
    }
}

/// Returned by [`Sender::sink`].
pub struct SenderSink<'a, F> {
    sender: &'a mut Sender,
    f: F,
}

impl<F: FnMut(OutgoingPacket)> crate::codec::PayloadSink for SenderSink<'_, F> {
    fn payload(&mut self, payload: &crate::codec::Payload<'_>) {
        (self.f)(
            self.sender
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
}
