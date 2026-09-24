// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [`ReceivedPacket`], as returned by [`super::Session`]'s packet-level stream.

use std::ops::Range;

use bytes::{Buf, Bytes};

use crate::rtp::{PacketHeader, PacketMeta};
use crate::{PacketContext, Timestamp};

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

impl PacketMeta<PacketContext> {
    /// Extracts metadata from a [`ReceivedPacket`].
    pub fn from_received(pkt: &ReceivedPacket) -> Self {
        let header = pkt.header();
        PacketMeta {
            ctx: *pkt.ctx(),
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
