// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Sans-I/O RTCP receiver reports, as described in
//! [RFC 3550 section 6.4.2](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.2).
//!
//! The pieces here keep reception statistics ([`ReceptionStats`]), decide when
//! the next report is due ([`ReportSchedule`]), and write reports
//! ([`ReportWriter`]). They do no I/O and read no clock: callers pass in
//! packets and times and send the bytes they get back. `Session<Playing>`'s
//! poll loop does that.
//!
//! Each stream is its own RTP session
//! ([RFC 3550 section 5.2](https://datatracker.ietf.org/doc/html/rfc3550#section-5.2)):
//! it has its own interleaved channel pair or UDP port pair, so it gets its own
//! statistics and its own report, sent on its own RTCP channel or socket.

use std::time::{Duration, Instant};

use base64::Engine as _;
use rand::Rng;

/// `MAX_DROPOUT` from [RFC 3550 appendix
/// A.1](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.1): a jump
/// ahead by less than this is taken as loss.
const MAX_DROPOUT: u16 = 3000;

/// `MAX_MISORDER` from RFC 3550 appendix A.1: a packet at most this far behind
/// the highest sequence number is taken as reordered or duplicated.
const MAX_MISORDER: u16 = 100;

/// `MIN_SEQUENTIAL` from RFC 3550 appendix A.1: the number of sequential
/// packets required before a new source is considered valid.
const MIN_SEQUENTIAL: u8 = 2;

/// `RTP_SEQ_MOD` from RFC 3550 appendix A.1.
const RTP_SEQ_MOD: u32 = 1 << 16;

/// The minimum interval between reports, from [RFC 3550 section
/// 6.2](https://datatracker.ietf.org/doc/html/rfc3550#section-6.2).
const MIN_INTERVAL: Duration = Duration::from_secs(5);

/// The compensation factor `e - 3/2` from [RFC 3550 section
/// 6.3.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.3.1), by
/// which the randomized interval is divided.
const COMPENSATION: f64 = std::f64::consts::E - 1.5;

/// RTCP packet type for a receiver report (RFC 3550 section 6.4.2).
const PT_RR: u8 = 201;

/// RTCP packet type for a source description (RFC 3550 section 6.5).
const PT_SDES: u8 = 202;

/// The `CNAME` SDES item type (RFC 3550 section 6.5.1).
const SDES_CNAME: u8 = 1;

/// Per-source sequence number state, the `source` struct of RFC 3550 appendix
/// A.1.
#[derive(Clone, Debug)]
struct SeqState {
    /// The highest sequence number seen.
    max_seq: u16,

    /// The count of sequence number wraps, shifted left by 16 bits.
    cycles: u32,

    /// The first sequence number counted.
    base_seq: u32,

    /// The last "bad" sequence number plus one.
    bad_seq: u32,

    /// Sequential packets still required before the source is valid.
    probation: u8,

    /// Packets received.
    received: u32,

    /// `expected` as of the last report.
    expected_prior: u32,

    /// `received` as of the last report.
    received_prior: u32,
}

impl SeqState {
    /// Starts tracking a source on its first packet, on probation.
    ///
    /// The caller should then pass the same packet to [`SeqState::update`],
    /// as in appendix A.1.
    fn new(seq: u16) -> Self {
        let mut s = SeqState {
            max_seq: 0,
            cycles: 0,
            base_seq: 0,
            bad_seq: 0,
            probation: MIN_SEQUENTIAL,
            received: 0,
            expected_prior: 0,
            received_prior: 0,
        };
        s.init(seq);
        s.max_seq = seq.wrapping_sub(1);
        s
    }

    /// `init_seq` from appendix A.1.
    fn init(&mut self, seq: u16) {
        self.base_seq = u32::from(seq);
        self.max_seq = seq;
        self.bad_seq = RTP_SEQ_MOD + 1; // so seq == bad_seq is false
        self.cycles = 0;
        self.received = 0;
        self.received_prior = 0;
        self.expected_prior = 0;
    }

    /// `update_seq` from appendix A.1. Returns true iff the packet is valid.
    fn update(&mut self, seq: u16) -> bool {
        let udelta = seq.wrapping_sub(self.max_seq);

        // Source is not valid until MIN_SEQUENTIAL packets with sequential
        // sequence numbers have been received.
        if self.probation > 0 {
            if seq == self.max_seq.wrapping_add(1) {
                self.probation -= 1;
                self.max_seq = seq;
                if self.probation == 0 {
                    self.init(seq);
                    self.received += 1;
                    return true;
                }
            } else {
                self.probation = MIN_SEQUENTIAL - 1;
                self.max_seq = seq;
            }
            return false;
        }

        if udelta < MAX_DROPOUT {
            // In order, with permissible gap.
            if seq < self.max_seq {
                // Sequence number wrapped: count another 64K cycle.
                self.cycles = self.cycles.wrapping_add(RTP_SEQ_MOD);
            }
            self.max_seq = seq;
        } else if u32::from(udelta) <= RTP_SEQ_MOD - u32::from(MAX_MISORDER) {
            // The sequence number made a very large jump.
            if u32::from(seq) == self.bad_seq {
                // Two sequential packets: assume that the other side restarted
                // without telling us, so just re-sync (i.e., pretend this was
                // the first packet).
                self.init(seq);
            } else {
                self.bad_seq = u32::from(seq.wrapping_add(1));
                return false;
            }
        } else {
            // Duplicate or reordered packet.
        }
        self.received = self.received.wrapping_add(1);
        true
    }

    /// Returns `(fraction_lost, cumulative_lost, extended_highest_seq)` as
    /// computed in [RFC 3550 appendix
    /// A.3](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.3), and
    /// starts a new reporting interval.
    fn report(&mut self) -> (u8, i32, u32) {
        let extended_max = self.cycles.wrapping_add(u32::from(self.max_seq));
        let expected = extended_max.wrapping_sub(self.base_seq).wrapping_add(1);

        // The cumulative number of packets lost is a 24-bit signed value,
        // clamped rather than wrapped.
        let lost = (i64::from(expected) - i64::from(self.received)).clamp(-0x80_0000, 0x7f_ffff);

        let expected_interval = expected.wrapping_sub(self.expected_prior);
        self.expected_prior = expected;
        let received_interval = self.received.wrapping_sub(self.received_prior);
        self.received_prior = self.received;
        let lost_interval = i64::from(expected_interval) - i64::from(received_interval);
        let fraction = if expected_interval == 0 || lost_interval <= 0 {
            0
        } else {
            // At most 255 as long as a packet was received in the interval;
            // clamp in case one wasn't.
            ((lost_interval << 8) / i64::from(expected_interval)).min(255) as u8
        };
        (fraction, lost as i32, extended_max)
    }
}

/// Interarrival jitter state, as in [RFC 3550 appendix
/// A.8](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.8).
#[derive(Clone, Debug)]
struct Jitter {
    /// The arrival time that arrival timestamps are relative to.
    epoch: Instant,

    /// The relative transit time of the previous packet, if any.
    transit: Option<u32>,

    /// The jitter estimate, scaled by 16 as in appendix A.8's integer version.
    scaled: u32,
}

impl Jitter {
    fn new(epoch: Instant) -> Self {
        Jitter {
            epoch,
            transit: None,
            scaled: 0,
        }
    }

    /// Updates the estimate with a packet with RTP timestamp `timestamp` which
    /// arrived at `arrival`, with a clock rate of `clock_rate` Hz.
    fn update(&mut self, clock_rate: u32, timestamp: u32, arrival: Instant) {
        // The arrival time in RTP timestamp units, modulo 2^32 as RTP
        // timestamps are. Only differences matter, so the epoch is arbitrary.
        let arrival = (arrival.saturating_duration_since(self.epoch).as_nanos()
            * u128::from(clock_rate)
            / 1_000_000_000) as u32;
        let transit = arrival.wrapping_sub(timestamp);
        if let Some(prev) = self.transit.replace(transit) {
            let d = (transit.wrapping_sub(prev) as i32).unsigned_abs();
            self.scaled = self
                .scaled
                .saturating_add(d)
                .saturating_sub(self.scaled.saturating_add(8) >> 4);
        }
    }

    /// Returns the jitter in RTP timestamp units, as it goes in a report block.
    fn get(&self) -> u32 {
        self.scaled >> 4
    }
}

/// A synchronization source a stream has heard from.
#[derive(Clone, Debug)]
struct Source {
    ssrc: u32,
    seq: SeqState,
    jitter: Jitter,
}

/// The last sender report received on a stream.
#[derive(Copy, Clone, Debug)]
struct LastSenderReport {
    ssrc: u32,

    /// The middle 32 bits of its NTP timestamp.
    lsr: u32,

    /// When it arrived.
    arrival: Instant,
}

/// Reception statistics for one stream (RTP session), from which its report
/// blocks are made.
#[derive(Debug)]
pub(crate) struct ReceptionStats {
    /// The stream's RTP clock rate in Hz, used for jitter.
    clock_rate: u32,

    /// The source heard from, if any. A packet from another SSRC starts over
    /// with that SSRC; the old one is no longer reported on.
    source: Option<Source>,

    /// True iff a valid RTP packet has been received since the last report
    /// block. RFC 3550 section 6.4 only reports on sources heard from since the
    /// last report.
    received_since_report: bool,

    last_sr: Option<LastSenderReport>,
}

/// A report block, as described in [RFC 3550 section
/// 6.4.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.1).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReportBlock {
    pub(crate) ssrc: u32,
    pub(crate) fraction_lost: u8,

    /// The cumulative number of packets lost, within the 24-bit signed range.
    pub(crate) cumulative_lost: i32,
    pub(crate) extended_highest_seq: u32,

    /// The interarrival jitter, in RTP timestamp units.
    pub(crate) jitter: u32,

    /// The middle 32 bits of the last sender report's NTP timestamp, or 0.
    pub(crate) lsr: u32,

    /// The delay since the last sender report, in units of 1/65536 seconds, or 0.
    pub(crate) dlsr: u32,
}

impl ReportBlock {
    fn write(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.ssrc.to_be_bytes());
        out.push(self.fraction_lost);
        out.extend_from_slice(&self.cumulative_lost.to_be_bytes()[1..]);
        out.extend_from_slice(&self.extended_highest_seq.to_be_bytes());
        out.extend_from_slice(&self.jitter.to_be_bytes());
        out.extend_from_slice(&self.lsr.to_be_bytes());
        out.extend_from_slice(&self.dlsr.to_be_bytes());
    }
}

impl ReceptionStats {
    pub(crate) fn new(clock_rate: u32) -> Self {
        ReceptionStats {
            clock_rate,
            source: None,
            received_since_report: false,
            last_sr: None,
        }
    }

    /// Notes an RTP packet as it arrives, before any reordering or loss
    /// handling.
    pub(crate) fn rtp(&mut self, ssrc: u32, seq: u16, timestamp: u32, arrival: Instant) {
        let source = match &mut self.source {
            Some(s) if s.ssrc == ssrc => s,
            s => {
                if let Some(old) = s {
                    log::debug!(
                        "RTP source changed from ssrc={:08x} to ssrc={:08x}; \
                         restarting reception statistics",
                        old.ssrc,
                        ssrc
                    );
                }
                self.received_since_report = false;
                s.insert(Source {
                    ssrc,
                    seq: SeqState::new(seq),
                    jitter: Jitter::new(arrival),
                })
            }
        };
        if source.seq.update(seq) {
            source.jitter.update(self.clock_rate, timestamp, arrival);
            self.received_since_report = true;
        }
    }

    /// Notes a sender report, as described in [RFC 3550 section
    /// 6.4.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.1), as
    /// it arrives.
    pub(crate) fn sender_report(&mut self, ssrc: u32, ntp: crate::NtpTimestamp, arrival: Instant) {
        self.last_sr = Some(LastSenderReport {
            ssrc,
            lsr: (ntp.0 >> 16) as u32,
            arrival,
        });
    }

    /// Returns a report block as of `now` and starts a new reporting interval,
    /// or `None` if no valid RTP packet has arrived since the last report.
    pub(crate) fn report_block(&mut self, now: Instant) -> Option<ReportBlock> {
        if !self.received_since_report {
            return None;
        }
        let source = self.source.as_mut()?;
        self.received_since_report = false;
        let (fraction_lost, cumulative_lost, extended_highest_seq) = source.seq.report();

        // LSR and DLSR are 0 until a sender report from this source has
        // arrived (RFC 3550 section 6.4.1).
        let (lsr, dlsr) = match self.last_sr {
            Some(sr) if sr.ssrc == source.ssrc => {
                let delay = now.saturating_duration_since(sr.arrival);
                let dlsr = (delay.as_nanos() * 65_536 / 1_000_000_000).min(u128::from(u32::MAX));
                (sr.lsr, dlsr as u32)
            }
            _ => (0, 0),
        };
        Some(ReportBlock {
            ssrc: source.ssrc,
            fraction_lost,
            cumulative_lost,
            extended_highest_seq,
            jitter: source.jitter.get(),
            lsr,
            dlsr,
        })
    }
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
    /// Returns a writer with a random SSRC and `CNAME`.
    ///
    /// The `CNAME` is 96 random bits, Base64-encoded, as [RFC 7022 section
    /// 4.2](https://datatracker.ietf.org/doc/html/rfc7022#section-4.2) and
    /// [section 5](https://datatracker.ietf.org/doc/html/rfc7022#section-5)
    /// suggest for a short-term persistent `CNAME`.
    pub(crate) fn random(rng: &mut impl Rng) -> Self {
        let ssrc = rng.r#gen();
        let cname = base64::engine::general_purpose::STANDARD.encode(rng.r#gen::<[u8; 12]>());
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
    pub(crate) fn write(&self, block: Option<&ReportBlock>) -> Vec<u8> {
        let rc = u8::from(block.is_some());
        let mut out = Vec::with_capacity(64);

        // Receiver report: header, our SSRC, the report block.
        out.extend_from_slice(&[(2 << 6) | rc, PT_RR]);
        out.extend_from_slice(&(1 + 6 * u16::from(rc)).to_be_bytes());
        out.extend_from_slice(&self.ssrc.to_be_bytes());
        if let Some(block) = block {
            block.write(&mut out);
        }

        // Source description with one chunk: our SSRC, the CNAME item, a null
        // octet to end the item list, and null octets to pad to a 32-bit
        // boundary (RFC 3550 section 6.5).
        let sdes_start = out.len();
        out.extend_from_slice(&[(2 << 6) | 1, PT_SDES, 0, 0]); // length filled in below.
        out.extend_from_slice(&self.ssrc.to_be_bytes());
        out.extend_from_slice(&[SDES_CNAME, self.cname.len() as u8]);
        out.extend_from_slice(self.cname.as_bytes());
        out.push(0);
        while out.len() % 4 != 0 {
            out.push(0);
        }
        let sdes_len = ((out.len() - sdes_start) / 4 - 1) as u16;
        out[sdes_start + 2..sdes_start + 4].copy_from_slice(&sdes_len.to_be_bytes());
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
            next: start + interval(MIN_INTERVAL / 2, rng),
        }
    }

    /// Returns when the next report is due.
    pub(crate) fn next_due(&self) -> Instant {
        self.next
    }

    /// Notes that reports were sent at `now`, scheduling the next.
    pub(crate) fn sent(&mut self, now: Instant, rng: &mut impl Rng) {
        self.next = now + interval(MIN_INTERVAL, rng);
    }
}

/// Randomizes the deterministic interval `td` as in RFC 3550 section 6.3.1.
fn interval(td: Duration, rng: &mut impl Rng) -> Duration {
    td.mul_f64(rng.gen_range(0.5..1.5) / COMPENSATION)
}

#[cfg(test)]
pub(crate) mod tests {
    use rand::SeedableRng as _;
    use rand::rngs::StdRng;

    use super::*;
    use crate::rtcp::{PacketRef, ReceivedCompoundPacket, TypedPacketRef};

    /// Returns a source that has passed probation with `seq`.
    fn valid_seq(seq: u16) -> SeqState {
        let mut s = SeqState::new(seq.wrapping_sub(1));
        assert!(!s.update(seq.wrapping_sub(1)));
        assert!(s.update(seq));
        s
    }

    #[test]
    fn probation() {
        // RFC 3550 appendix A.1: a new source is valid after MIN_SEQUENTIAL (2)
        // sequential packets; the first isn't counted.
        let mut s = SeqState::new(10);
        assert!(!s.update(10));
        assert!(s.update(11));
        assert_eq!((s.base_seq, s.received), (11, 1));

        // A non-sequential packet on probation restarts probation from there.
        let mut s = SeqState::new(10);
        assert!(!s.update(10));
        assert!(!s.update(20));
        assert_eq!((s.probation, s.max_seq), (1, 20));
        assert!(s.update(21));
        assert_eq!((s.base_seq, s.received), (21, 1));
    }

    #[test]
    fn wrap() {
        let mut s = valid_seq(0xfffe);
        assert!(s.update(0xffff));
        assert!(s.update(0));
        assert_eq!(s.cycles, RTP_SEQ_MOD);
        assert!(s.update(1));
        let (fraction, lost, extended) = s.report();
        assert_eq!((fraction, lost, extended), (0, 0, RTP_SEQ_MOD + 1));
    }

    #[test]
    fn misorder_and_duplicates() {
        let mut s = valid_seq(100);
        assert!(s.update(102));
        // Reordered and duplicate packets are valid and counted as received,
        // without moving the highest sequence number.
        assert!(s.update(101));
        assert!(s.update(102));
        assert_eq!(s.max_seq, 102);
        assert_eq!(s.received, 4);
        // The duplicate makes the loss negative.
        assert_eq!(s.report(), (0, -1, 102));

        // A packet MAX_MISORDER behind is still reordered; one more is a jump.
        let mut s = valid_seq(1000);
        assert!(s.update(1000 - MAX_MISORDER + 1));
        assert_eq!(s.max_seq, 1000);
        assert!(!s.update(1000 - MAX_MISORDER));
        assert_eq!(s.bad_seq, u32::from(1000 - MAX_MISORDER + 1));
    }

    #[test]
    fn large_jump_resyncs() {
        let mut s = valid_seq(10);
        // A gap of less than MAX_DROPOUT is loss.
        assert!(s.update(10 + MAX_DROPOUT - 1));
        let max = s.max_seq;
        // A jump of MAX_DROPOUT or more is dropped...
        assert!(!s.update(max.wrapping_add(MAX_DROPOUT)));
        assert_eq!(s.max_seq, max);
        // ...unless the next packet follows it: then the sender is assumed to
        // have restarted, and the statistics start over from there.
        assert!(!s.update(20_000));
        assert_eq!(s.bad_seq, 20_001);
        assert!(s.update(20_001));
        assert_eq!((s.base_seq, s.max_seq, s.received), (20_001, 20_001, 1));
        assert_eq!(s.report(), (0, 0, 20_001));
    }

    #[test]
    fn loss() {
        // RFC 3550 appendix A.3, across a wrap: 0xfff1 through 0x000e is 30
        // expected packets; 26 arrive.
        let mut s = valid_seq(0xfff1);
        for seq in 0xfff2..=0xffff {
            assert!(s.update(seq));
        }
        for seq in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 14] {
            assert!(s.update(seq));
        }
        assert_eq!(s.received, 26);
        // fraction = (4 << 8) / 30 = 34.
        assert_eq!(s.report(), (34, 4, RTP_SEQ_MOD + 14));

        // Nothing new: nothing lost in this interval; the cumulative count stays.
        assert_eq!(s.report(), (0, 4, RTP_SEQ_MOD + 14));

        // 15..=24 expected (10), 5 arrive: half lost in the interval.
        for seq in [16, 18, 20, 22, 24] {
            assert!(s.update(seq));
        }
        assert_eq!(s.report(), (128, 9, RTP_SEQ_MOD + 24));

        // The cumulative count is clamped to 24 signed bits.
        s.received = 0;
        s.base_seq = 0;
        s.cycles = 0x0100_0000;
        assert_eq!(s.report().1, 0x7f_ffff);
        s.received = 0x0200_0000;
        assert_eq!(s.report().1, -0x80_0000);
    }

    #[test]
    fn jitter() {
        // RFC 3550 appendix A.8. A 90 kHz stream, packets every 10 ms stamped
        // 900 apart: no jitter.
        let t0 = Instant::now();
        let mut j = Jitter::new(t0);
        for i in 0..10u32 {
            j.update(
                90_000,
                i * 900,
                t0 + Duration::from_millis(u64::from(i) * 10),
            );
        }
        assert_eq!(j.get(), 0);

        // One packet 10 ms (900 ticks) late: |D| = 900, so J = 0 + (900 - 0) / 16.
        j.update(90_000, 9_000, t0 + Duration::from_millis(110));
        assert_eq!(j.scaled, 900);
        assert_eq!(j.get(), 56);

        // The next on time: |D| = 900 again; J += (900 - J) / 16, in the
        // integer form J' = J + |D| - ((J + 8) >> 4) with J scaled by 16.
        j.update(90_000, 9_900, t0 + Duration::from_millis(110));
        assert_eq!(j.scaled, 900 + 900 - ((900 + 8) >> 4));
        assert_eq!(j.get(), 109);

        // Early counts like late.
        let mut early = Jitter::new(t0);
        early.update(8_000, 0, t0);
        early.update(8_000, 160, t0); // 20 ms early on an 8 kHz clock.
        assert_eq!(early.scaled, 160);
    }

    #[test]
    fn stats_report_block() {
        let t0 = Instant::now();
        let mut stats = ReceptionStats::new(90_000);
        assert_eq!(stats.report_block(t0), None);

        // A sender report before any RTP; it's from the source that follows.
        stats.sender_report(0x1234, crate::NtpTimestamp(0xe436_2f99_cccc_cccc), t0);

        stats.rtp(0x1234, 1, 0, t0);
        // Still on probation: no block.
        assert_eq!(stats.report_block(t0), None);
        stats.rtp(0x1234, 2, 900, t0 + Duration::from_millis(10));
        stats.rtp(0x1234, 4, 2_700, t0 + Duration::from_millis(40)); // 3 lost; 4 is 10 ms late.
        let now = t0 + Duration::from_millis(1500);
        assert_eq!(
            stats.report_block(now),
            Some(ReportBlock {
                ssrc: 0x1234,
                fraction_lost: 85, // (1 << 8) / 3
                cumulative_lost: 1,
                extended_highest_seq: 4,
                jitter: 56, // 900 / 16
                lsr: 0x2f99_cccc,
                dlsr: 98_304, // 1.5 * 65536
            })
        );

        // Nothing since: no block.
        assert_eq!(stats.report_block(now), None);
    }

    #[test]
    fn stats_lsr_dlsr() {
        let t0 = Instant::now();
        let mut stats = ReceptionStats::new(8_000);
        stats.rtp(0x1234, 1, 0, t0);
        stats.rtp(0x1234, 2, 160, t0 + Duration::from_millis(20));

        // No sender report yet: LSR and DLSR are 0.
        let b = stats.report_block(t0).unwrap();
        assert_eq!((b.lsr, b.dlsr), (0, 0));

        // A sender report from another SSRC doesn't count.
        stats.sender_report(0x5678, crate::NtpTimestamp(0x0000_1111_2222_0000), t0);
        stats.rtp(0x1234, 3, 320, t0 + Duration::from_millis(40));
        let b = stats.report_block(t0).unwrap();
        assert_eq!((b.lsr, b.dlsr), (0, 0));

        // One from the source does, with the delay since it arrived.
        stats.sender_report(0x1234, crate::NtpTimestamp(0x0000_1111_2222_0000), t0);
        stats.rtp(0x1234, 4, 480, t0 + Duration::from_millis(60));
        let b = stats.report_block(t0 + Duration::from_millis(250)).unwrap();
        assert_eq!((b.lsr, b.dlsr), (0x1111_2222, 16_384));
    }

    #[test]
    fn stats_new_ssrc_restarts() {
        let t0 = Instant::now();
        let mut stats = ReceptionStats::new(8_000);
        stats.rtp(0x1234, 1, 0, t0);
        stats.rtp(0x1234, 2, 160, t0);
        stats.rtp(0x5678, 500, 0, t0);
        // The old source is forgotten, and the new one is on probation.
        assert_eq!(stats.report_block(t0), None);
        stats.rtp(0x5678, 501, 160, t0);
        let b = stats.report_block(t0).unwrap();
        assert_eq!((b.ssrc, b.extended_highest_seq), (0x5678, 501));
    }

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
        assert_eq!(sdes.payload_type(), PT_SDES);
        assert_eq!(sdes.count(), 1);
        let sdes = sdes.raw();
        assert_eq!(&sdes[4..8], &ssrc.to_be_bytes());
        assert_eq!(sdes[8], SDES_CNAME);
        let len = usize::from(sdes[9]);
        assert_eq!(&sdes[10..10 + len], cname.as_bytes());
        // At least one null octet ends the item list; the rest is padding.
        assert!(sdes[10 + len..].iter().all(|&b| b == 0));
        assert!(sdes.len() > 10 + len);
        &pkt[..rr_len]
    }

    /// Returns the report block in a parsed RR.
    pub(crate) fn parse_block(rr: &[u8]) -> ReportBlock {
        let word = |i: usize| u32::from_be_bytes(rr[i..i + 4].try_into().unwrap());
        ReportBlock {
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

        let block = ReportBlock {
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
        let compensated = |d: f64| Duration::from_secs_f64(d / COMPENSATION);
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
