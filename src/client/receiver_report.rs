// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Sans-I/O RTCP receiver reports, as described in
//! [RFC 3550 section 6.4.2](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.2).
//!
//! Each stream's [`crate::rtp::Receiver`] keeps reception statistics for its
//! selected source. The pieces here decide when the next report is due
//! ([`ReportSchedule`]) and write reports ([`ReportWriter`]). They do no I/O
//! and read no clock: callers pass in times and send the bytes they get back.
//! `Session<Playing>`'s poll loop does that.
//!
//! Each stream is its own RTP session
//! ([RFC 3550 section 5.2](https://datatracker.ietf.org/doc/html/rfc3550#section-5.2)):
//! it has its own interleaved channel pair or UDP port pair, so it gets its own
//! statistics and its own report, sent on its own RTCP channel or socket.

use std::time::Instant;

use rand::Rng;

use crate::rtp::ReceptionReport;

use crate::rtcp::{MIN_REPORT_INTERVAL, report_interval};

/// RTCP packet type for a receiver report (RFC 3550 section 6.4.2).
const PT_RR: u8 = 201;

/// Writes a report block, as described in [RFC 3550 section
/// 6.4.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.1).
fn write_block(block: &ReceptionReport, out: &mut Vec<u8>) {
    out.extend_from_slice(&block.ssrc.to_be_bytes());
    out.push(block.fraction_lost);
    out.extend_from_slice(&block.cumulative_lost.to_be_bytes()[1..]);
    out.extend_from_slice(&block.extended_highest_seq.to_be_bytes());
    out.extend_from_slice(&block.jitter.to_be_bytes());
    out.extend_from_slice(&block.lsr.to_be_bytes());
    out.extend_from_slice(&block.dlsr.to_be_bytes());
}

/// Writes RTCP compound packets with receiver reports.
///
/// One writer serves all streams of a session. They share a `CNAME`, as RFC
/// 3550 section 6.5.1 says a participant's should be across related RTP
/// sessions, and an SSRC, which need only be unique within each RTP session.
#[derive(Debug)]
pub(crate) struct ReportWriter {
    /// Our SSRC, chosen randomly as described in [RFC 3550 section
    /// 8.1](https://datatracker.ietf.org/doc/html/rfc3550#section-8.1).
    pub(crate) ssrc: u32,

    /// Our `CNAME`; at most 255 bytes.
    pub(crate) cname: String,
}

impl ReportWriter {
    /// Returns a writer with a random SSRC and `CNAME`, as in
    /// [`crate::rtcp::random_cname`].
    pub(crate) fn random(rng: &mut impl Rng) -> Self {
        let ssrc = rng.r#gen();
        let cname = crate::rtcp::cname_from_bits(rng.r#gen());
        ReportWriter { ssrc, cname }
    }

    /// Writes a compound packet, as described in [RFC 3550 section
    /// 6.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.1): a
    /// receiver report with the given block, if any, then a source description
    /// with our `CNAME`.
    ///
    /// When nothing has arrived since the last report, there's no block, but
    /// the (empty) receiver report still heads the packet, as RFC 3550 section
    /// 6.4 requires.
    pub(crate) fn write(&self, block: Option<&ReceptionReport>) -> Vec<u8> {
        let rc = u8::from(block.is_some());
        let mut out = Vec::with_capacity(64);

        // Receiver report: header, our SSRC, the report block.
        out.extend_from_slice(&[(2 << 6) | rc, PT_RR]);
        out.extend_from_slice(&(1 + 6 * u16::from(rc)).to_be_bytes());
        out.extend_from_slice(&self.ssrc.to_be_bytes());
        if let Some(block) = block {
            write_block(block, &mut out);
        }

        crate::rtcp::write_sdes_cname(self.ssrc, &self.cname, &mut out);
        out
    }
}

/// Decides when reports are due, as described in [RFC 3550 section
/// 6.2](https://datatracker.ietf.org/doc/html/rfc3550#section-6.2) and
/// [section 6.3.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.3.1).
///
/// This simplifies the computation for a unicast session with one sender (the
/// server) and one receiver (us). The deterministic interval is the 5-second
/// minimum, halved for the first report as section 6.2 allows. The
/// bandwidth-based interval would exceed that only with a session bandwidth
/// below about 6.4 kbit/s (two members, ~100-byte reports, 5% of the session
/// bandwidth for RTCP), and servers seldom say what the session bandwidth is
/// anyway. As section 6.3.1 describes, the interval is then multiplied by a
/// random factor in `[0.5, 1.5)` and divided by `e - 3/2` to compensate for
/// timer reconsideration (appendix A.7). Reconsideration itself is moot with a
/// fixed membership of two, so it's not done.
#[derive(Debug)]
pub(crate) struct ReportSchedule {
    next: Instant,
}

impl ReportSchedule {
    /// Schedules the first report after joining the session at `start`.
    pub(crate) fn new(start: Instant, rng: &mut impl Rng) -> Self {
        ReportSchedule {
            next: start + report_interval(MIN_REPORT_INTERVAL / 2, rng),
        }
    }

    /// Returns when the next report is due.
    pub(crate) fn next_due(&self) -> Instant {
        self.next
    }

    /// Notes that reports were sent at `now`, scheduling the next.
    pub(crate) fn sent(&mut self, now: Instant, rng: &mut impl Rng) {
        self.next = now + report_interval(MIN_REPORT_INTERVAL, rng);
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::time::Duration;

    use rand::SeedableRng as _;
    use rand::rngs::StdRng;

    use super::*;
    use crate::rtcp::{PacketRef, ReceivedCompoundPacket, TypedPacketRef};

    /// Parses `pkt` with Retina's own RTCP parser, checking it's an RR from
    /// `ssrc` with `rc` blocks followed by an SDES with `cname`, and returns
    /// the RR's raw bytes.
    pub(crate) fn parse_report<'a>(pkt: &'a [u8], ssrc: u32, rc: u8, cname: &str) -> &'a [u8] {
        let first = ReceivedCompoundPacket::validate(pkt).unwrap();
        let rr = match first.as_typed().unwrap() {
            Some(TypedPacketRef::ReceiverReport(rr)) => rr,
            _ => panic!("expected an RR"),
        };
        assert_eq!(rr.ssrc(), ssrc);
        assert_eq!(rr.count(), rc);
        let rr_len = rr.raw().len();
        assert_eq!(rr_len, 8 + 24 * usize::from(rc));
        let (sdes, rest) = PacketRef::parse(&pkt[rr_len..]).unwrap();
        assert!(rest.is_empty());
        assert_eq!(sdes.payload_type(), crate::rtcp::PT_SDES);
        assert_eq!(sdes.count(), 1);
        let sdes = sdes.raw();
        assert_eq!(&sdes[4..8], &ssrc.to_be_bytes());
        assert_eq!(sdes[8], crate::rtcp::SDES_CNAME);
        let len = usize::from(sdes[9]);
        assert_eq!(&sdes[10..10 + len], cname.as_bytes());
        // At least one null octet ends the item list; the rest is padding.
        assert!(sdes[10 + len..].iter().all(|&b| b == 0));
        assert!(sdes.len() > 10 + len);
        &pkt[..rr_len]
    }

    /// Returns the report block in a parsed RR.
    pub(crate) fn parse_block(rr: &[u8]) -> ReceptionReport {
        let word = |i: usize| u32::from_be_bytes(rr[i..i + 4].try_into().unwrap());
        ReceptionReport {
            ssrc: word(8),
            fraction_lost: rr[12],
            cumulative_lost: i32::from_be_bytes([0, rr[13], rr[14], rr[15]]) << 8 >> 8,
            extended_highest_seq: word(16),
            jitter: word(20),
            lsr: word(24),
            dlsr: word(28),
        }
    }

    #[test]
    fn write_round_trip() {
        let mut rng = StdRng::seed_from_u64(0);
        let writer = ReportWriter::random(&mut rng);
        assert_eq!(writer.cname.len(), 16);
        let other = ReportWriter::random(&mut rng);
        assert_ne!(writer.ssrc, other.ssrc);
        assert_ne!(writer.cname, other.cname);

        let block = ReceptionReport {
            ssrc: 0xdcc4_a0d8,
            fraction_lost: 34,
            cumulative_lost: -2,
            extended_highest_seq: 0x0001_000e,
            jitter: 56,
            lsr: 0x2f99_cccc,
            dlsr: 98_304,
        };
        let pkt = writer.write(Some(&block));
        assert_eq!(pkt.len(), 32 + 28);
        let rr = parse_report(&pkt, writer.ssrc, 1, &writer.cname);
        assert_eq!(parse_block(rr), block);
        assert_eq!(&rr[13..16], &[0xff, 0xff, 0xfe]);
    }

    #[test]
    fn write_empty_rr() {
        // Nothing arrived: an RR with no blocks still heads the packet.
        let writer = ReportWriter {
            ssrc: 0xfeed_beef,
            cname: "abc".to_owned(),
        };
        let pkt = writer.write(None);
        assert_eq!(
            &pkt[..],
            b"\x80\xc9\x00\x01\xfe\xed\xbe\xef\
              \x81\xca\x00\x03\xfe\xed\xbe\xef\
              \x01\x03abc\x00\x00\x00"
        );
        parse_report(&pkt, 0xfeed_beef, 0, "abc");
    }

    #[test]
    fn write_pads_sdes() {
        // A CNAME whose item ends on a 32-bit boundary still gets a null
        // octet, then padding to the next boundary.
        let writer = ReportWriter {
            ssrc: 1,
            cname: "ab".to_owned(),
        };
        let pkt = writer.write(None);
        assert_eq!(
            &pkt[8..],
            b"\x81\xca\x00\x03\x00\x00\x00\x01\x01\x02ab\x00\x00\x00\x00"
        );
        parse_report(&pkt, 1, 0, "ab");
    }

    #[test]
    fn interval_bounds() {
        let mut rng = StdRng::seed_from_u64(0);
        let start = Instant::now();
        let compensated = |d: f64| Duration::from_secs_f64(d / crate::rtcp::REPORT_COMPENSATION);
        let (mut min, mut max) = (Duration::MAX, Duration::ZERO);
        for _ in 0..10_000 {
            let first = ReportSchedule::new(start, &mut rng).next_due() - start;
            assert!(first >= compensated(1.25) && first < compensated(3.75));
            let mut schedule = ReportSchedule::new(start, &mut rng);
            let now = start + Duration::from_secs(100);
            schedule.sent(now, &mut rng);
            let next = schedule.next_due() - now;
            min = min.min(next);
            max = max.max(next);
        }
        // 5 s × [0.5, 1.5) / (e - 3/2) is [2.052, 6.156) s; check the draws
        // actually spread over that.
        assert!(min >= compensated(2.5) && min < compensated(2.6), "{min:?}");
        assert!(max < compensated(7.5) && max > compensated(7.4), "{max:?}");
    }
}
