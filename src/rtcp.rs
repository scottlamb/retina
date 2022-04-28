// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

/// Handles RTCP data as described in
/// [RFC 3550 section 6](https://datatracker.ietf.org/doc/html/rfc3550#section-6).
use std::convert::TryInto;

pub enum Packet<'a> {
    SenderReport(SenderReport<'a>),
    Unknown(GenericPacket<'a>),
}

impl<'a> Packet<'a> {
    pub fn parse(buf: &'a [u8]) -> Result<(Self, &'a [u8]), String> {
        let (pkt, rest) = GenericPacket::parse(buf)?;
        let pkt = match pkt.payload_type() {
            200 => Packet::SenderReport(SenderReport::validate(pkt)?),
            _ => Packet::Unknown(pkt),
        };
        Ok((pkt, rest))
    }
}

/// A RTCP sender report, as defined in
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
pub struct SenderReport<'a>(GenericPacket<'a>);

impl<'a> SenderReport<'a> {
    fn validate(pkt: GenericPacket<'a>) -> Result<Self, String> {
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
        Ok(SenderReport(pkt))
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

/// A generic packet, not parsed as any particular payload type.
///
/// This only inteprets the leading four bytes:
///
/// ```text
///  0                   1                   2                   3
///  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// |V=2|P|         |   PT          |             length            |
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// ```
pub struct GenericPacket<'a> {
    buf: &'a [u8],
    payload_end: usize,
}

const COMMON_HEADER_LEN: usize = 4;

impl<'a> GenericPacket<'a> {
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
            return Err(format!("RTCP packets must be version 2; got {}", ver));
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
                    "RTCP packet of len {} states invalid {} padding bytes",
                    len, padding_bytes
                ));
            }
            Ok((
                GenericPacket {
                    buf: this,
                    payload_end: len - padding_bytes,
                },
                rest,
            ))
        } else {
            Ok((
                GenericPacket {
                    buf: this,
                    payload_end: len,
                },
                rest,
            ))
        }
    }

    /// Returns the uninterpreted payload type of this RTCP packet.
    pub fn payload_type(&self) -> u8 {
        self.buf[1]
    }

    /// Returns the low 5 bits of the first octet, which is typically a count
    /// or subtype.
    pub fn count(&self) -> u8 {
        self.buf[0] & 0b0001_1111
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
        let (sr, buf) = Packet::parse(buf).unwrap();
        match sr {
            Packet::SenderReport(p) => {
                assert_eq!(p.ntp_timestamp(), crate::NtpTimestamp(0xe4362f99cccccccc));
                assert_eq!(p.rtp_timestamp(), 0x852ef807);
            }
            _ => panic!(),
        }
        let (sdes, buf) = Packet::parse(buf).unwrap();
        match sdes {
            Packet::Unknown(p) => assert_eq!(p.payload_type(), 202),
            _ => panic!(),
        }
        assert_eq!(buf.len(), 0);
    }

    #[test]
    fn padding() {
        let buf = b"\xa7\x00\x00\x02asdf\x00\x00\x00\x04rest";
        let (pkt, rest) = GenericPacket::parse(buf).unwrap();
        assert_eq!(pkt.count(), 7);
        assert_eq!(&pkt.buf[4..pkt.payload_end], b"asdf");
        assert_eq!(b"rest", rest);
    }
}
