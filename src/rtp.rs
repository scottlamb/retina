// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Handles RTP data as described in
//! [RFC 3550 section 5.1](https://datatracker.ietf.org/doc/html/rfc3550#section-5.1).

use std::ops::Range;

use bytes::{Buf, Bytes};

use crate::inputs::Input;
use crate::{PacketContext, Timestamp};

/// Fixed RTP packet header (no CSRCs, payload, or extensions).
///
/// This is a thin wrapper around the raw 12-byte header, with accessor
/// methods for the individual fields. It can be constructed on-the-fly
/// from a [`ReceivedPacket`] or via [`PacketHeader::validate`].
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
    const LEN: u16 = 12;

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

/// A received RTP packet.
///
/// This holds more information than the packet itself: also a
/// [`PacketContext`], the stream, and extended timestamp.
#[derive(Eq, PartialEq)]
pub struct ReceivedPacket {
    pub(crate) ctx: PacketContext,
    pub(crate) stream_id: usize,
    pub(crate) timestamp: crate::Timestamp,

    /// Full packet data, including headers.
    pub(crate) data: Bytes,
    pub(crate) payload_range: Range<u16>,

    // TODO: consider dropping this field in favor of a PacketItem::Loss.
    // https://github.com/scottlamb/retina/issues/47
    pub(crate) loss: u16,
}

impl std::fmt::Debug for ReceivedPacket {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReceivedPacket")
            .field("ctx", &self.ctx)
            .field("stream_id", &self.stream_id)
            .field("timestamp", &self.timestamp)
            .field("ssrc", &self.ssrc())
            .field("sequence_number", &self.sequence_number())
            .field("mark", &self.mark())
            .field("payload", &crate::hex::LimitedHex::new(self.payload(), 64))
            .finish()
    }
}

impl ReceivedPacket {
    /// Returns the fixed 12-byte RTP header.
    ///
    /// This constructs a [`PacketHeader`] on-the-fly from the packet data;
    /// inlining should avoid an actual copy in most cases.
    #[inline]
    pub fn header(&self) -> PacketHeader {
        PacketHeader(self.data[..PacketHeader::LEN as usize].try_into().unwrap())
    }

    #[inline]
    pub fn timestamp(&self) -> crate::Timestamp {
        self.timestamp
    }

    #[inline]
    pub fn mark(&self) -> bool {
        self.header().mark()
    }

    #[inline]
    pub fn ctx(&self) -> &PacketContext {
        &self.ctx
    }

    #[inline]
    pub fn stream_id(&self) -> usize {
        self.stream_id
    }

    #[inline]
    pub fn ssrc(&self) -> u32 {
        self.header().ssrc()
    }

    #[inline]
    pub fn sequence_number(&self) -> u16 {
        self.header().sequence_number()
    }

    /// Returns the raw bytes, including the RTP headers.
    #[inline]
    pub fn raw(&self) -> &[u8] {
        &self.data[..]
    }

    /// Returns only the payload bytes.
    #[inline]
    pub fn payload(&self) -> &[u8] {
        &self.data[usize::from(self.payload_range.start)..usize::from(self.payload_range.end)]
    }

    #[inline]
    pub fn loss(&self) -> u16 {
        self.loss
    }

    /// Consumes the `ReceivedPacket` and returns the `Payload` as a [`Bytes`].
    ///
    /// This is currently very efficient (no copying or reference-counting),
    /// although that is not an API guarantee.
    #[inline]
    pub fn into_payload_bytes(self) -> Bytes {
        let mut data = self.data;
        data.truncate(usize::from(self.payload_range.end));
        data.advance(usize::from(self.payload_range.start));
        data
    }
}

/// Metadata extracted from a received RTP packet, for use by depacketizers.
///
/// This allows depacketizers to work without depending on [`ReceivedPacket`],
/// enabling the `Demuxed` path to pass data directly from the ring buffer.
#[derive(Clone, Copy, Debug)]
#[doc(hidden)]
pub struct PacketMeta {
    pub ctx: crate::PacketContext,
    pub stream_id: usize,
    pub timestamp: crate::Timestamp,
    pub sequence_number: u16,
    pub ssrc: u32,
    pub mark: bool,
    pub loss: u16,
}

impl PacketMeta {
    pub fn from_received(pkt: &ReceivedPacket) -> Self {
        let header = pkt.header();
        PacketMeta {
            ctx: *pkt.ctx(),
            stream_id: pkt.stream_id(),
            timestamp: pkt.timestamp(),
            sequence_number: header.sequence_number(),
            ssrc: header.ssrc(),
            mark: header.mark(),
            loss: pkt.loss(),
        }
    }
}

/// Builds raw RTP packet bytes for testing.
pub(crate) fn build_raw_rtp<P: IntoIterator<Item = u8>>(
    sequence_number: u16,
    timestamp: u32,
    payload_type: u8,
    ssrc: u32,
    mark: bool,
    payload: P,
) -> Result<Bytes, &'static str> {
    if payload_type >= 0x80 {
        return Err("payload type too large");
    }
    let data: Bytes = [
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

/// Testing API; exposed for fuzz tests.
#[doc(hidden)]
pub struct ReceivedPacketBuilder {
    pub ctx: PacketContext,
    pub stream_id: usize,
    pub sequence_number: u16,
    pub timestamp: Timestamp,
    pub payload_type: u8,
    pub ssrc: u32,
    pub mark: bool,
    pub loss: u16,
}

impl ReceivedPacketBuilder {
    pub fn build<P: IntoIterator<Item = u8>>(
        self,
        payload: P,
    ) -> Result<ReceivedPacket, &'static str> {
        let data = build_raw_rtp(
            self.sequence_number,
            self.timestamp.timestamp as u32,
            self.payload_type,
            self.ssrc,
            self.mark,
            payload,
        )?;
        let len = data.len() as u16;
        Ok(ReceivedPacket {
            ctx: self.ctx,
            stream_id: self.stream_id,
            timestamp: self.timestamp,
            data,
            payload_range: PacketHeader::LEN..len,
            loss: self.loss,
        })
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
