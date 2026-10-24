// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Handles RTCP data as described in
//! [RFC 3550 section 6](https://datatracker.ietf.org/doc/html/rfc3550#section-6).

use std::convert::TryInto;
use std::time::Duration;

use bytes::Bytes;

use crate::PacketContext;

/// The minimum interval between reports, from [RFC 3550 section
/// 6.2](https://datatracker.ietf.org/doc/html/rfc3550#section-6.2).
pub(crate) const MIN_REPORT_INTERVAL: Duration = Duration::from_secs(5);

/// The compensation factor `e - 3/2` from [RFC 3550 section
/// 6.3.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.3.1), by
/// which the randomized interval is divided.
pub(crate) const REPORT_COMPENSATION: f64 = std::f64::consts::E - 1.5;

/// Randomizes the deterministic report interval `td` as in [RFC 3550 section
/// 6.3.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.3.1).
///
/// This simplifies the computation for a unicast session with one sender and
/// one receiver; see the client's receiver report schedule. Sender reports
/// ([`crate::rtp::Sender::report_sent`]) follow the same schedule.
pub(crate) fn report_interval(td: Duration, rng: &mut impl rand::Rng) -> Duration {
    td.mul_f64(rng.gen_range(0.5..1.5) / REPORT_COMPENSATION)
}

/// RTCP packet type for a source description (RFC 3550 section 6.5).
pub(crate) const PT_SDES: u8 = 202;

/// The `CNAME` SDES item type (RFC 3550 section 6.5.1).
pub(crate) const SDES_CNAME: u8 = 1;

/// Returns a random `CNAME`.
///
/// The `CNAME` is 96 random bits, Base64-encoded, as [RFC 7022 section
/// 4.2](https://datatracker.ietf.org/doc/html/rfc7022#section-4.2) and
/// [section 5](https://datatracker.ietf.org/doc/html/rfc7022#section-5)
/// suggest for a short-term persistent `CNAME`.
///
/// Every RTCP compound packet carries its sender's `CNAME`; see
/// [`crate::rtp::Sender::sender_report`]. Streams meant to be synchronized
/// with each other (e.g. a presentation's audio and video) should share one.
pub fn random_cname() -> String {
    use rand::Rng as _;
    cname_from_bits(rand::thread_rng().r#gen())
}

/// Encodes 96 random bits as a `CNAME`, as in [`random_cname`].
pub(crate) fn cname_from_bits(bits: [u8; 12]) -> String {
    use base64::Engine as _;
    base64::engine::general_purpose::STANDARD.encode(bits)
}

/// Appends a source description with one chunk to `out`: `ssrc`, the `CNAME`
/// item, a null octet to end the item list, and null octets to pad to a
/// 32-bit boundary (RFC 3550 section 6.5).
///
/// # Panics
///
/// If `cname` is longer than 255 bytes.
pub(crate) fn write_sdes_cname(ssrc: u32, cname: &str, out: &mut Vec<u8>) {
    let cname_len = u8::try_from(cname.len()).expect("CNAME is at most 255 bytes");
    let start = out.len();
    out.extend_from_slice(&[(2 << 6) | 1, PT_SDES, 0, 0]); // length filled in below.
    out.extend_from_slice(&ssrc.to_be_bytes());
    out.extend_from_slice(&[SDES_CNAME, cname_len]);
    out.extend_from_slice(cname.as_bytes());
    out.push(0);
    while !(out.len() - start).is_multiple_of(4) {
        out.push(0);
    }
    let len = ((out.len() - start) / 4 - 1) as u16;
    out[start + 2..start + 4].copy_from_slice(&len.to_be_bytes());
}

/// A received RTCP compound packet.
///
/// The contents have been validated at least as specified in [RFC 3550 appendix
/// A.2](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.2), updated
/// by [RFC 5506](https://datatracker.ietf.org/doc/html/rfc5506):
///
/// *   There is at least one RTCP packet within the compound packet.
/// *   All packets are RTCP version 2.
/// *   Non-final packets have no padding.
/// *   The packets' lengths add up to the compound packet's length.
#[derive(Eq, PartialEq)]
pub struct ReceivedCompoundPacket {
    pub(crate) ctx: PacketContext,
    pub(crate) stream_id: usize,
    pub(crate) rtp_timestamp: Option<crate::Timestamp>,
    pub(crate) raw: Bytes,
}

impl ReceivedCompoundPacket {
    /// For tests.
    #[doc(hidden)]
    pub fn dummy(rtp_timestamp: Option<crate::Timestamp>, data: &[u8]) -> Self {
        Self {
            ctx: PacketContext::dummy(),
            stream_id: 0,
            rtp_timestamp,
            raw: Bytes::copy_from_slice(data),
        }
    }

    /// Validates the supplied compound packet.
    ///
    /// Returns the first packet on success so the caller doesn't need to
    /// recaculate its lengths.
    pub(crate) fn validate(raw: &[u8]) -> Result<PacketRef<'_>, String> {
        let (first_pkt, mut rest) = PacketRef::parse(raw)?;
        let mut pkt = first_pkt;
        loop {
            if rest.is_empty() {
                break;
            } else if pkt.has_padding() {
                return Err("padding on non-final packet within RTCP compound packet".to_owned());
            }
            (pkt, rest) = PacketRef::parse(rest)?;
        }
        Ok(first_pkt)
    }

    #[inline]
    pub fn ctx(&self) -> &PacketContext {
        &self.ctx
    }

    #[inline]
    pub fn stream_id(&self) -> usize {
        self.stream_id
    }

    /// Returns an RTP timestamp iff this compound packet begins with a valid Sender Report.
    ///
    /// Iff this returns `Some`, other fields of the sender report can be accessed as follows:
    ///
    /// ```
    /// # let compound = retina::rtcp::ReceivedCompoundPacket::dummy(
    /// #     retina::Timestamp::new(0, std::num::NonZeroU32::new(90_000).unwrap(), 0),
    /// #     b"\x80\xc8\x00\x06\x66\x42\x6a\xe1\
    /// #       \xe4\x36\x2f\x99\xcc\xcc\xcc\xcc\
    /// #       \x85\x2e\xf8\x07\x00\x2a\x43\x33\
    /// #       \x2f\x4c\x34\x1d\
    /// #       \x81\xca\x00\x04\x66\x42\x6a\xe1\
    /// #       \x01\x06\x28\x6e\x6f\x6e\x65\x29\
    /// #       \x00\x00\x00\x00",
    /// # );
    /// let sender_report = compound.pkts().next().unwrap().as_sender_report().unwrap();
    /// ```
    #[inline]
    pub fn rtp_timestamp(&self) -> Option<crate::Timestamp> {
        self.rtp_timestamp
    }

    /// Returns the full raw compound packet, including headers of all packets.
    #[inline]
    pub fn raw(&self) -> &[u8] {
        &self.raw[..]
    }

    /// Returns an iterator through all contained packets.
    #[inline]
    pub fn pkts(&self) -> impl Iterator<Item = PacketRef<'_>> {
        CompoundPacketIterator(&self.raw[..])
    }
}

impl std::fmt::Debug for ReceivedCompoundPacket {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReceivedCompoundPacket")
            .field("ctx", &self.ctx)
            .field("stream_id", &self.stream_id)
            .field("rtp_timestamp", &self.rtp_timestamp)
            .field("raw", &crate::hex::LimitedHex::new(&self.raw[..], 64))
            .finish()
    }
}

/// Internal type returned from [`ReceivedCompoundPacket::pkts`].
struct CompoundPacketIterator<'a>(&'a [u8]);

impl<'a> Iterator for CompoundPacketIterator<'a> {
    type Item = PacketRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0.is_empty() {
            return None;
        }

        let (pkt, rest) =
            PacketRef::parse(self.0).expect("failed to parse previously validated packet");
        self.0 = rest;
        Some(pkt)
    }
}

/// A payload type-specific accessor for a packet.
#[non_exhaustive]
pub enum TypedPacketRef<'a> {
    SenderReport(SenderReportRef<'a>),
    ReceiverReport(ReceiverReportRef<'a>),
}

/// A sender report, as defined in
/// [RFC 3550 section 6.4.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.1).
///
/// ```text
///         0                   1                   2                   3
///         0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// header |V=2|P|    RC   |   PT=SR=200   |             length            |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |                         SSRC of sender                        |
///        +=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+
/// sender |              NTP timestamp, most significant word             |
/// info   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |             NTP timestamp, least significant word             |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |                         RTP timestamp                         |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |                     sender's packet count                     |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |                      sender's octet count                     |
///        +=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+
/// report |                 SSRC_1 (SSRC of first source)                 |
/// block  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///   1    | fraction lost |       cumulative number of packets lost       |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |           extended highest sequence number received           |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |                      interarrival jitter                      |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |                         last SR (LSR)                         |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |                   delay since last SR (DLSR)                  |
///        +=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+
/// report |                 SSRC_2 (SSRC of second source)                |
/// block  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///   2    :                               ...                             :
///        +=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+
///        |                  profile-specific extensions                  |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// ```
pub struct SenderReportRef<'a>(PacketRef<'a>);

impl<'a> SenderReportRef<'a> {
    fn validate(pkt: PacketRef<'a>) -> Result<Self, String> {
        let count = usize::from(pkt.count());
        const HEADER_LEN: usize = 8;
        const SENDER_INFO_LEN: usize = 20;
        const REPORT_BLOCK_LEN: usize = 24;
        let expected_len = HEADER_LEN + SENDER_INFO_LEN + (count * REPORT_BLOCK_LEN);
        if pkt.payload_end < expected_len {
            return Err(format!(
                "RTCP SR has invalid count={} with unpadded_byte_len={}",
                count, pkt.payload_end
            ));
        }
        Ok(Self(pkt))
    }

    pub fn ssrc(&self) -> u32 {
        u32::from_be_bytes(self.0.buf[4..8].try_into().unwrap())
    }

    pub fn ntp_timestamp(&self) -> crate::NtpTimestamp {
        crate::NtpTimestamp(u64::from_be_bytes(self.0.buf[8..16].try_into().unwrap()))
    }

    pub fn rtp_timestamp(&self) -> u32 {
        u32::from_be_bytes(self.0.buf[16..20].try_into().unwrap())
    }
}

impl<'a> std::ops::Deref for SenderReportRef<'a> {
    type Target = PacketRef<'a>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A receiver report, as defined in
/// [RFC 3550 section 6.4.2](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.2).
///
/// ```text
///         0                   1                   2                   3
///         0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// header |V=2|P|    RC   |   PT=RR=201   |             length            |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |                     SSRC of packet sender                     |
///        +=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+
/// report |                 SSRC_1 (SSRC of first source)                 |
/// block  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///   1    | fraction lost |       cumulative number of packets lost       |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |           extended highest sequence number received           |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |                      interarrival jitter                      |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |                         last SR (LSR)                         |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///        |                   delay since last SR (DLSR)                  |
///        +=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+
/// report |                 SSRC_2 (SSRC of second source)                |
/// block  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
///   2    :                               ...                             :
///        +=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+=+
///        |                  profile-specific extensions                  |
///        +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// ```
///
pub struct ReceiverReportRef<'a>(PacketRef<'a>);

impl<'a> ReceiverReportRef<'a> {
    fn validate(pkt: PacketRef<'a>) -> Result<Self, String> {
        let count = usize::from(pkt.count());
        const HEADER_LEN: usize = 8;
        const REPORT_BLOCK_LEN: usize = 24;
        let expected_len = HEADER_LEN + (count * REPORT_BLOCK_LEN);
        if pkt.payload_end < expected_len {
            return Err(format!(
                "RTCP RR has invalid count={} with unpadded_byte_len={}",
                count, pkt.payload_end
            ));
        }
        Ok(Self(pkt))
    }

    pub fn ssrc(&self) -> u32 {
        u32::from_be_bytes(self.0.buf[4..8].try_into().unwrap())
    }
}

impl<'a> std::ops::Deref for ReceiverReportRef<'a> {
    type Target = PacketRef<'a>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A generic packet, not parsed as any particular payload type.
///
/// This only interprets the leading four bytes:
///
/// ```text
///  0                   1                   2                   3
///  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// |V=2|P|         |   PT          |             length            |
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// ```
#[derive(Copy, Clone)]
pub struct PacketRef<'a> {
    buf: &'a [u8],
    payload_end: usize,
}

const COMMON_HEADER_LEN: usize = 4;

impl<'a> PacketRef<'a> {
    /// Parses a buffer into this packet and rest, doing only basic validation
    /// of the version, padding, and length.
    pub fn parse(buf: &'a [u8]) -> Result<(Self, &'a [u8]), String> {
        if buf.len() < COMMON_HEADER_LEN {
            return Err(format!(
                "RTCP packets must be at least {} bytes; have only {}",
                COMMON_HEADER_LEN,
                buf.len()
            ));
        }
        let ver = buf[0] >> 6;
        if ver != 2 {
            return Err(format!("RTCP packets must be version 2; got {ver}"));
        }

        // raw_len is "The length of this RTCP packet in 32-bit words minus one,
        // including the header and any padding."
        let raw_len = (u16::from(buf[2]) << 8) | u16::from(buf[3]);
        let len = (usize::from(raw_len) + 1) * 4;
        if buf.len() < len {
            return Err(format!(
                "RTCP packet header has length {} bytes; have only {}",
                len,
                buf.len()
            ));
        }
        let (this, rest) = buf.split_at(len);
        let padding_bit = this[0] & 0b0010_0000;
        if padding_bit != 0 {
            if raw_len == 0 {
                return Err("RTCP packet has invalid combination of padding and len=0".to_owned());
            }
            let padding_bytes = usize::from(this[len - 1]);
            if padding_bytes == 0 || padding_bytes > len - COMMON_HEADER_LEN {
                return Err(format!(
                    "RTCP packet of len {len} states invalid {padding_bytes} padding bytes"
                ));
            }
            Ok((
                PacketRef {
                    buf: this,
                    payload_end: len - padding_bytes,
                },
                rest,
            ))
        } else {
            Ok((
                PacketRef {
                    buf: this,
                    payload_end: len,
                },
                rest,
            ))
        }
    }

    /// Returns the uninterpreted payload type of this RTCP packet.
    #[inline]
    pub fn payload_type(&self) -> u8 {
        self.buf[1]
    }

    /// Parses to a `TypedPacketRef` if the payload type is supported.
    pub fn as_typed(self) -> Result<Option<TypedPacketRef<'a>>, String> {
        match self.payload_type() {
            200 => Ok(Some(TypedPacketRef::SenderReport(
                SenderReportRef::validate(self)?,
            ))),
            201 => Ok(Some(TypedPacketRef::ReceiverReport(
                ReceiverReportRef::validate(self)?,
            ))),
            _ => Ok(None),
        }
    }

    /// Parses as a sender report, if the type matches.
    pub fn as_sender_report(self) -> Result<Option<SenderReportRef<'a>>, String> {
        if self.payload_type() == 200 {
            return Ok(Some(SenderReportRef::validate(self)?));
        }
        Ok(None)
    }

    /// Returns true iff this packet has padding.
    #[inline]
    pub fn has_padding(&self) -> bool {
        (self.buf[0] & 0b0010_0000) != 0
    }

    /// Returns the low 5 bits of the first octet, which is typically a count
    /// or subtype.
    #[inline]
    pub fn count(&self) -> u8 {
        self.buf[0] & 0b0001_1111
    }

    /// Returns the full raw data, including headers.
    #[inline]
    pub fn raw(&self) -> &[u8] {
        self.buf
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dahua() {
        // Sender report and source description from a Dahua camera.
        let buf = b"\x80\xc8\x00\x06\x66\x42\x6a\xe1\
                    \xe4\x36\x2f\x99\xcc\xcc\xcc\xcc\
                    \x85\x2e\xf8\x07\x00\x2a\x43\x33\
                    \x2f\x4c\x34\x1d\
                    \x81\xca\x00\x04\x66\x42\x6a\xe1\
                    \x01\x06\x28\x6e\x6f\x6e\x65\x29\
                    \x00\x00\x00\x00";
        let (pkt, buf) = PacketRef::parse(buf).unwrap();
        let sr = pkt.as_sender_report().unwrap().unwrap();
        assert_eq!(sr.ntp_timestamp(), crate::NtpTimestamp(0xe4362f99cccccccc));
        assert_eq!(sr.rtp_timestamp(), 0x852ef807);
        let (pkt, buf) = PacketRef::parse(buf).unwrap();
        assert_eq!(pkt.payload_type(), 202);
        assert_eq!(buf.len(), 0);
    }

    #[test]
    fn padding() {
        let buf = b"\xa7\x00\x00\x02asdf\x00\x00\x00\x04rest";
        let (pkt, rest) = PacketRef::parse(buf).unwrap();
        assert_eq!(pkt.count(), 7);
        assert_eq!(&pkt.buf[4..pkt.payload_end], b"asdf");
        assert_eq!(b"rest", rest);
    }
}
