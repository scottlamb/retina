// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Handles RTP data as described in
//! [RFC 3550 section 5.1](https://datatracker.ietf.org/doc/html/rfc3550#section-5.1).

use std::ops::Range;

use crate::buf::{MarkBuf, Split};
use crate::inputs::Input;

#[cfg(feature = "unstable-send")]
mod sender;

#[cfg(feature = "unstable-send")]
pub use sender::{OutgoingPacketRef, Sender, SenderOptions, SenderSink};

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
    /// [`Split`] pair of ring-buffer slices.
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
/// within a [`ReceivedPacketRef`].
///
/// `Ctx` is a caller-chosen packet context type, returned with the events the
/// packet contributes to. See [`crate::codec::VideoHandler`].
///
/// This is `#[non_exhaustive]` so that fields can be added later; construct
/// it via [`ReceivedPacketMeta::new`].
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub struct ReceivedPacketMeta<Ctx> {
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

impl<Ctx> ReceivedPacketMeta<Ctx> {
    /// Creates metadata with the given field values.
    #[inline]
    pub fn new(
        ctx: Ctx,
        timestamp: crate::Timestamp,
        sequence_number: u16,
        ssrc: u32,
        mark: bool,
        loss: u16,
    ) -> Self {
        Self {
            ctx,
            timestamp,
            sequence_number,
            ssrc,
            mark,
            loss,
        }
    }
}

/// An RTP packet whose payload is in a [`MarkBuf`].
///
/// Passed to depacketizers such as [`crate::codec::VideoDepacketizer::push`],
/// bundling packet metadata with buffer access.
pub struct ReceivedPacketRef<'a, Ctx> {
    /// The packet's metadata.
    pub meta: ReceivedPacketMeta<Ctx>,
    buf: &'a MarkBuf,
    payload_pos: u64,
    payload_len: u16,
}

#[cfg_attr(not(any(feature = "h264", feature = "h265")), allow(dead_code))]
impl<'a, Ctx> ReceivedPacketRef<'a, Ctx> {
    /// Creates a `ReceivedPacketRef` for a payload at stream positions
    /// `[payload_pos, payload_pos + payload_len)` in `buf`.
    ///
    /// # Panics
    ///
    /// Panics if the payload isn't within `buf`'s parsed bytes, `[start(),
    /// unparsed())`. See the [`MarkBuf`] contract.
    pub fn new(
        meta: ReceivedPacketMeta<Ctx>,
        buf: &'a MarkBuf,
        payload_pos: u64,
        payload_len: u16,
    ) -> Self {
        assert!(
            payload_pos >= buf.start()
                && payload_pos
                    .checked_add(u64::from(payload_len))
                    .is_some_and(|end| end <= buf.unparsed()),
            "payload [{payload_pos}, +{payload_len}) must be within parsed bytes [{}, {})",
            buf.start(),
            buf.unparsed(),
        );
        Self {
            meta,
            buf,
            payload_pos,
            payload_len,
        }
    }

    /// Ring-buffer position of the first payload byte.
    #[inline]
    pub(crate) fn payload_pos(&self) -> u64 {
        self.payload_pos
    }

    /// Payload length in bytes.
    #[inline]
    pub(crate) fn payload_len(&self) -> u16 {
        self.payload_len
    }

    /// Returns the payload.
    #[inline]
    pub fn payload(&self) -> Split<'a> {
        self.buf
            .split(self.payload_pos, usize::from(self.payload_len))
    }

    /// Returns the buffer holding the payload.
    #[inline]
    pub(crate) fn buf(&self) -> &'a MarkBuf {
        self.buf
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

    fn meta() -> ReceivedPacketMeta<()> {
        crate::rtp::ReceivedPacketMeta {
            ctx: (),
            timestamp: crate::Timestamp::new(0, std::num::NonZeroU32::new(90_000).unwrap(), 0)
                .unwrap(),
            sequence_number: 0,
            ssrc: 0,
            mark: false,
            loss: 0,
        }
    }

    #[test]
    #[should_panic(expected = "must be within parsed bytes")]
    fn packet_ref_unparsed() {
        let mut buf = MarkBuf::new(64);
        buf.extend(b"hello");
        let _ = ReceivedPacketRef::new(meta(), &buf, 0, 5);
    }

    #[test]
    #[should_panic(expected = "must be within parsed bytes")]
    fn packet_ref_beyond_end() {
        let mut buf = MarkBuf::new(64);
        buf.extend(b"hello");
        buf.advance_unparsed(5);
        let _ = ReceivedPacketRef::new(meta(), &buf, 1, 5);
    }

    #[test]
    fn packet_ref_ok() {
        let mut buf = MarkBuf::new(64);
        buf.extend(b"hello");
        buf.advance_unparsed(5);
        let pkt = ReceivedPacketRef::new(meta(), &buf, 1, 4);
        assert_eq!(pkt.payload().to_vec(), b"ello");
    }
}
