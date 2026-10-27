// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The send side of an RTP session: [`Sender`].

use super::{ExtensionIds, Extensions, PacketHeader};

/// The RTP session state of an outgoing stream.
///
/// Assigns sequence numbers to payloads (such as [`crate::codec::Payload`]s)
/// and maps their timestamps, yielding [`OutgoingPacketRef`]s. Like the receive
/// side, it owns no packet storage: the caller copies each packet wherever
/// it's going, e.g. into a connection's send buffer. The counterparts on the
/// receive side are [`super::Reorderer`] and [`super::Receiver`].
///
/// When sending one source to several destinations (e.g. a server answering
/// `PLAY` from several clients, as in the `proxy` example), give each
/// destination its own `Sender`, so each sees an ordinary RTP session with
/// its own SSRC and sequence numbers. Likewise give each its own packetizer:
/// throttling (see [`crate::codec::PayloadSink::congested`]) changes the
/// packetizer's state, so a shared one would let one slow destination drop
/// data for all.
#[derive(Debug)]
pub struct Sender {
    ssrc: u32,
    payload_type: u8,
    next_sequence_number: u16,
    timestamp_offset: u32,
    extension_ids: ExtensionIds,
    max_payload_size: u16,
    packet_count: u32,
    octet_count: u32,

    /// When the next sender report is due, or `None` if one is due after
    /// the next packet; see [`Sender::report_due`].
    next_report: Option<std::time::Instant>,
}

/// Options for a [`Sender`].
///
/// By default, the SSRC, initial sequence number, and timestamp offset are
/// chosen randomly when the sender is created, as RFC 3550 recommends.
#[derive(Clone, Debug)]
pub struct SenderOptions {
    ssrc: Option<u32>,
    initial_sequence_number: Option<u16>,
    timestamp_offset: Option<u32>,
    extension_ids: ExtensionIds,
    max_payload_size: u16,
}

impl Default for SenderOptions {
    fn default() -> Self {
        Self {
            ssrc: None,
            initial_sequence_number: None,
            timestamp_offset: None,
            extension_ids: ExtensionIds::default(),
            max_payload_size: 1400,
        }
    }
}

impl SenderOptions {
    /// Sets the SSRC. By default, it's chosen randomly.
    #[inline]
    pub fn ssrc(self, ssrc: u32) -> Self {
        Self {
            ssrc: Some(ssrc),
            ..self
        }
    }

    /// Sets the first packet's sequence number. By default, it's chosen
    /// randomly.
    #[inline]
    pub fn initial_sequence_number(self, seq: u16) -> Self {
        Self {
            initial_sequence_number: Some(seq),
            ..self
        }
    }

    /// Sets the offset added to each [`crate::Timestamp`] to form the RTP
    /// timestamp; see [`Sender::rtp_timestamp`]. By default, it's chosen
    /// randomly.
    #[inline]
    pub fn timestamp_offset(self, offset: u32) -> Self {
        Self {
            timestamp_offset: Some(offset),
            ..self
        }
    }

    /// Sets the maximum payload size in bytes, as packetizers see it via
    /// [`crate::codec::PayloadSink::max_payload_size`] on [`Sender::sink`].
    /// Defaults to 1400. See also [`Sender::set_max_payload_size`].
    #[inline]
    pub fn max_payload_size(self, max_payload_size: u16) -> Self {
        Self {
            max_payload_size,
            ..self
        }
    }

    pub_if_unstable_extensions! {
        /// Sets the IDs of header extensions to write. By default, none are
        /// written.
        ///
        /// Describe them to receivers via [`ExtensionIds::sdp_extmap`].
        #[inline]
        pub fn extension_ids(self, extension_ids: ExtensionIds) -> Self {
            Self {
                extension_ids,
                ..self
            }
        }
    }
}

/// An outgoing RTP packet, as returned by [`Sender::packet`].
///
/// This borrows its payload, so the caller must copy it (e.g. via
/// [`OutgoingPacketRef::write_to`]) to keep it.
#[derive(Copy, Clone, Debug)]
pub struct OutgoingPacketRef<'a> {
    header: PacketHeader,
    extension: &'a [u8],
    data: &'a [&'a [u8]],
}

impl<'a> OutgoingPacketRef<'a> {
    /// Returns the packet's fixed RTP header.
    #[inline]
    pub fn header(&self) -> PacketHeader {
        self.header
    }

    pub_if_unstable_extensions! {
        /// Returns the packet's header extension block, including its 4-byte
        /// profile and length header, or empty.
        #[inline]
        pub fn extension(&self) -> &'a [u8] {
            self.extension
        }
    }

    /// Returns the packet's payload, as a sequence of slices to be
    /// concatenated.
    #[inline]
    pub fn data(&self) -> &'a [&'a [u8]] {
        self.data
    }

    /// Returns the packet's total length in bytes, including its RTP header.
    #[inline]
    pub fn len(&self) -> usize {
        usize::from(PacketHeader::LEN)
            + self.extension.len()
            + self.data.iter().map(|d| d.len()).sum::<usize>()
    }

    /// Returns false; an RTP packet always has a header.
    #[inline]
    pub fn is_empty(&self) -> bool {
        false
    }

    /// Writes the complete packet to `out`.
    pub fn write_to(&self, out: &mut impl bytes::BufMut) {
        out.put_slice(&self.header.0);
        out.put_slice(self.extension);
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
    /// Creates a new sender with the given payload type.
    ///
    /// # Panics
    ///
    /// If `payload_type` doesn't fit in 7 bits.
    pub fn new(payload_type: u8, options: SenderOptions) -> Self {
        assert!(payload_type < 0x80, "payload type {payload_type} too large");
        Self {
            ssrc: options.ssrc.unwrap_or_else(rand::random),
            payload_type,
            next_sequence_number: options.initial_sequence_number.unwrap_or_else(rand::random),
            timestamp_offset: options.timestamp_offset.unwrap_or_else(rand::random),
            extension_ids: options.extension_ids,
            max_payload_size: options.max_payload_size,
            packet_count: 0,
            octet_count: 0,
            next_report: None,
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

    /// Returns the maximum payload size; see [`SenderOptions::max_payload_size`].
    #[inline]
    pub fn max_payload_size(&self) -> u16 {
        self.max_payload_size
    }

    /// Changes the maximum payload size, e.g. as path MTU discovery finds
    /// the path's MTU. Packetizers see the change at their next frame.
    #[inline]
    pub fn set_max_payload_size(&mut self, max_payload_size: u16) {
        self.max_payload_size = max_payload_size;
    }

    pub_if_unstable_extensions! {
        /// Encodes those of `extensions` which have IDs (see
        /// [`SenderOptions::extension_ids`]) as a header extension block,
        /// replacing the contents of `out`, for
        /// [`Sender::packet_with_extensions`]. Leaves `out` empty if there's
        /// nothing to send.
        ///
        /// [`Sender::sink`] supplies this to packetizers via
        /// [`crate::codec::PayloadSink::serialize_extensions`].
        #[inline]
        pub fn serialize_extensions(&self, extensions: &Extensions, out: &mut Vec<u8>) {
            self.extension_ids.encode(extensions, out);
        }
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
    /// and `p.data()`; or use [`Sender::sink`], which also writes
    /// [`crate::codec::Payload::encoded_extensions`].
    ///
    /// # Panics
    ///
    /// If the packet exceeds 65,535 bytes.
    #[inline]
    pub fn packet<'a>(
        &mut self,
        timestamp: crate::Timestamp,
        mark: bool,
        data: &'a [&'a [u8]],
    ) -> OutgoingPacketRef<'a> {
        self.packet_with_extensions(timestamp, mark, &[], data)
    }

    pub_if_unstable_extensions! {
        /// As [`Sender::packet`], also writing the header extension block
        /// `extension`, as encoded by [`Sender::serialize_extensions`], if
        /// it's non-empty.
        ///
        /// # Panics
        ///
        /// If the packet exceeds 65,535 bytes, or `extension` is non-empty
        /// but not a well-formed block: a multiple of 4 bytes, whose length
        /// field matches.
        pub fn packet_with_extensions<'a>(
            &mut self,
            timestamp: crate::Timestamp,
            mark: bool,
            extension: &'a [u8],
            data: &'a [&'a [u8]],
        ) -> OutgoingPacketRef<'a> {
            assert!(
                extension.is_empty()
                    || (extension.len() >= 4
                        && extension.len().is_multiple_of(4)
                        && usize::from(u16::from_be_bytes([extension[2], extension[3]])) * 4 + 4
                            == extension.len()),
                "malformed header extension block of {} bytes",
                extension.len()
            );
            let payload_len: usize = data.iter().map(|d| d.len()).sum();
            let len = usize::from(PacketHeader::LEN) + extension.len() + payload_len;
            assert!(
                len <= usize::from(u16::MAX),
                "RTP packet of {len} bytes is too long"
            );
            let sequence_number = self.next_sequence_number;
            self.next_sequence_number = sequence_number.wrapping_add(1);
            self.packet_count = self.packet_count.wrapping_add(1);
            self.octet_count = self.octet_count.wrapping_add(payload_len as u32);
            let mut header = [0; PacketHeader::LEN as usize];
            // version=2, no padding, no CSRCs.
            header[0] = 2 << 6 | if extension.is_empty() { 0 } else { 0b0001_0000 };
            header[1] = if mark { 0b1000_0000 } else { 0 } | self.payload_type;
            header[2..4].copy_from_slice(&sequence_number.to_be_bytes());
            header[4..8].copy_from_slice(&self.rtp_timestamp(timestamp).to_be_bytes());
            header[8..12].copy_from_slice(&self.ssrc.to_be_bytes());
            OutgoingPacketRef {
                header: PacketHeader(header),
                extension,
                data,
            }
        }
    }

    /// Skips a sequence number, so receivers see lost data as packet loss.
    pub fn skip(&mut self) {
        self.next_sequence_number = self.next_sequence_number.wrapping_add(1);
    }

    /// Returns an RTCP compound packet whose sender report states that
    /// `timestamp` corresponds to wall time `ntp`.
    ///
    /// The packet is a sender report with no reception report blocks
    /// ([RFC 3550 section 6.4.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.1)),
    /// then a source description with `cname`, as [section
    /// 6.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.1) requires
    /// of every compound packet. See [`crate::rtcp::random_cname`].
    ///
    /// Section 6.4.1 says `ntp` and `timestamp` should describe the instant
    /// the report is sent, which needn't be when any packet was sampled.
    ///
    /// # Panics
    ///
    /// If `cname` is longer than 255 bytes.
    pub fn sender_report(
        &self,
        ntp: crate::NtpTimestamp,
        timestamp: crate::Timestamp,
        cname: &str,
    ) -> Vec<u8> {
        let mut out = Vec::with_capacity(28 + 12 + cname.len());
        out.extend_from_slice(&[
            2 << 6, // version=2, no padding, no reception reports.
            200,    // SR
            0,
            6, // length in 32-bit words, minus one.
        ]);
        out.extend_from_slice(&self.ssrc.to_be_bytes());
        out.extend_from_slice(&ntp.0.to_be_bytes());
        out.extend_from_slice(&self.rtp_timestamp(timestamp).to_be_bytes());
        out.extend_from_slice(&self.packet_count.to_be_bytes());
        out.extend_from_slice(&self.octet_count.to_be_bytes());
        crate::rtcp::write_sdes_cname(self.ssrc, cname, &mut out);
        out
    }

    /// Returns true if a sender report is due at `now`.
    ///
    /// Check this after sending each packet, so reports go out while packets
    /// flow. The first report is due right after the first packet: [RFC 3550
    /// section 6.2](https://datatracker.ietf.org/doc/html/rfc3550#section-6.2)
    /// says that for unicast sessions "the delay before sending the initial
    /// compound RTCP packet MAY be zero". After that, see
    /// [`Sender::report_sent`].
    #[inline]
    pub fn report_due(&self, now: std::time::Instant) -> bool {
        self.next_report.is_none_or(|t| now >= t)
    }

    /// Notes that a sender report was sent at `now`, scheduling the next.
    ///
    /// The next is due 5 s × [0.5, 1.5) / (e − 3/2) later, as [RFC 3550
    /// section 6.3.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.3.1)
    /// describes for a unicast session (and as the client schedules its
    /// receiver reports).
    pub fn report_sent(&mut self, now: std::time::Instant) {
        self.next_report = Some(
            now + crate::rtcp::report_interval(
                crate::rtcp::MIN_REPORT_INTERVAL,
                &mut rand::thread_rng(),
            ),
        );
    }

    /// Returns a [`crate::codec::PayloadSink`] which passes each packet to
    /// `f`, and skips a sequence number on each discontinuity.
    ///
    /// The sink is never congested; to throttle, wrap `Sender` in a sink of
    /// your own.
    pub fn sink<F: FnMut(&OutgoingPacketRef<'_>)>(&mut self, f: F) -> SenderSink<'_, F> {
        SenderSink { sender: self, f }
    }
}

/// Returned by [`Sender::sink`].
pub struct SenderSink<'a, F> {
    sender: &'a mut Sender,
    f: F,
}

impl<F: FnMut(&OutgoingPacketRef<'_>)> crate::codec::PayloadSink for SenderSink<'_, F> {
    fn payload(&mut self, payload: &crate::codec::Payload<'_>) {
        (self.f)(&self.sender.packet_with_extensions(
            payload.timestamp(),
            payload.mark(),
            payload.encoded_extensions(),
            payload.data(),
        ));
    }

    fn discontinuity(&mut self) {
        self.sender.skip();
    }

    #[inline]
    fn max_payload_size(&self) -> u16 {
        self.sender.max_payload_size()
    }

    #[cfg(feature = "unstable-extensions")]
    #[inline]
    fn serialize_extensions(&self, extensions: &Extensions, out: &mut Vec<u8>) {
        self.sender.serialize_extensions(extensions, out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rtp::ValidatedPacket;

    #[test]
    fn sender() {
        let mut s = Sender::new(
            96,
            SenderOptions::default()
                .ssrc(0x1234_5678)
                .initial_sequence_number(0xffff)
                .timestamp_offset(10),
        );
        let ts = crate::Timestamp::new(100, std::num::NonZeroU32::new(90_000).unwrap(), 0).unwrap();
        let pkt = s.packet(ts, true, &[b"ab", b"cde"]);
        let raw = pkt.to_vec();
        assert_eq!(raw.len(), pkt.len());
        let ValidatedPacket {
            header, payload, ..
        } = PacketHeader::validate(&raw[..]).unwrap();
        assert_eq!(header, pkt.header());
        assert_eq!(&raw[usize::from(payload.start)..], b"abcde");
        assert!(header.mark());
        assert_eq!(header.payload_type(), 96);
        assert_eq!(header.sequence_number(), 0xffff);
        assert_eq!(header.timestamp(), 110);
        assert_eq!(header.ssrc(), 0x1234_5678);
        assert_eq!(s.next_sequence_number(), 0);
        s.skip();
        assert_eq!(s.next_sequence_number(), 1);

        assert!(pkt.extension().is_empty());

        let sr = s.sender_report(crate::NtpTimestamp(0x0102_0304_0506_0708), ts, "abc");
        let (pkt, rest) = crate::rtcp::PacketRef::parse(&sr[..]).unwrap();
        let (sdes, rest) = crate::rtcp::PacketRef::parse(rest).unwrap();
        assert!(rest.is_empty());
        assert_eq!(
            sdes.raw(),
            b"\x81\xca\x00\x03\x12\x34\x56\x78\x01\x03abc\x00\x00\x00"
        );
        assert_eq!(&pkt.raw()[20..28], b"\x00\x00\x00\x01\x00\x00\x00\x05"); // packet and octet counts.
        let sr = pkt.as_sender_report().unwrap().unwrap();
        assert_eq!(sr.ssrc(), 0x1234_5678);
        assert_eq!(sr.ntp_timestamp().0, 0x0102_0304_0506_0708);
        assert_eq!(sr.rtp_timestamp(), 110);
    }

    #[test]
    fn sender_extensions() {
        use crate::rtp::AbsCaptureTime;
        let id = std::num::NonZeroU8::new(5).unwrap();
        let ids = ExtensionIds::default().with::<AbsCaptureTime>(id);
        let mut s = Sender::new(96, SenderOptions::default().extension_ids(ids));
        let ts = crate::Timestamp::new(100, std::num::NonZeroU32::new(90_000).unwrap(), 0).unwrap();
        let values = Extensions::default().with(AbsCaptureTime::new(crate::NtpTimestamp(42)));

        let mut ext = Vec::new();
        s.serialize_extensions(&values, &mut ext);
        let raw = s
            .packet_with_extensions(ts, false, &ext, &[b"xyz"])
            .to_vec();
        let v = PacketHeader::validate(&raw[..]).unwrap();
        assert_eq!(&raw[usize::from(v.payload.start)..], b"xyz");
        assert_eq!(ids.read(&v.extension(&raw).unwrap()), values);

        // Without values, no extension is written.
        let raw = s.packet(ts, false, &[b"xyz"]).to_vec();
        let v = PacketHeader::validate(&raw[..]).unwrap();
        assert_eq!(v.extension, None);
        assert_eq!(raw.len(), 15);
    }
}
