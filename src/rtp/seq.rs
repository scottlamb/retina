// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Sequence number tracking as in [RFC 3550 appendix
//! A.1](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.1), used by
//! [`super::Reorderer`] to classify arrivals and to compute receiver report
//! statistics.

/// `MAX_DROPOUT` from RFC 3550 appendix A.1: a jump ahead by less than this is
/// taken as loss.
pub(crate) const MAX_DROPOUT: u16 = 3000;

/// `MAX_MISORDER` from RFC 3550 appendix A.1: a packet at most this far behind
/// the highest sequence number is taken as reordered or duplicated.
pub(crate) const MAX_MISORDER: u16 = 100;

/// `MIN_SEQUENTIAL` from RFC 3550 appendix A.1: the number of sequential
/// packets required before a new source is considered valid.
const MIN_SEQUENTIAL: u8 = 2;

/// `RTP_SEQ_MOD` from RFC 3550 appendix A.1.
const RTP_SEQ_MOD: u32 = 1 << 16;

/// How [`SeqState::update`] classified an arriving packet.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum Arrival {
    /// The source is still on probation; the packet isn't counted.
    Probation,

    /// The packet is in order (possibly after a gap), reordered, or a
    /// duplicate. It's counted as received.
    Valid,

    /// The packet made a very large jump from the highest sequence number. It
    /// isn't counted and should be discarded, unless the next packet follows
    /// it.
    Stray,

    /// The packet follows a stray one: the sender is assumed to have
    /// restarted its sequence numbers, and statistics start over from here.
    Restart,
}

/// Per-source sequence number state, the `source` struct of RFC 3550 appendix
/// A.1.
#[derive(Clone, Debug)]
pub(crate) struct SeqState {
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

    /// True iff a valid packet has arrived since the last report.
    /// RFC 3550 section 6.4 only reports on sources heard from since then.
    valid_since_report: bool,
}

impl SeqState {
    /// Starts tracking a source on its first packet, on probation.
    ///
    /// The caller should then pass the same packet to [`SeqState::update`],
    /// as in appendix A.1.
    pub(crate) fn new(seq: u16) -> Self {
        let mut s = SeqState {
            max_seq: 0,
            cycles: 0,
            base_seq: 0,
            bad_seq: 0,
            probation: MIN_SEQUENTIAL,
            received: 0,
            expected_prior: 0,
            received_prior: 0,
            valid_since_report: false,
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

    /// `update_seq` from appendix A.1.
    pub(crate) fn update(&mut self, seq: u16) -> Arrival {
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
                    self.valid_since_report = true;
                    return Arrival::Valid;
                }
            } else {
                self.probation = MIN_SEQUENTIAL - 1;
                self.max_seq = seq;
            }
            return Arrival::Probation;
        }

        let arrival = if udelta < MAX_DROPOUT {
            // In order, with permissible gap.
            if seq < self.max_seq {
                // Sequence number wrapped: count another 64K cycle.
                self.cycles = self.cycles.wrapping_add(RTP_SEQ_MOD);
            }
            self.max_seq = seq;
            Arrival::Valid
        } else if u32::from(udelta) <= RTP_SEQ_MOD - u32::from(MAX_MISORDER) {
            // The sequence number made a very large jump.
            if u32::from(seq) == self.bad_seq {
                // Two sequential packets: assume that the other side restarted
                // without telling us, so just re-sync (i.e., pretend this was
                // the first packet).
                self.init(seq);
                Arrival::Restart
            } else {
                self.bad_seq = u32::from(seq.wrapping_add(1));
                return Arrival::Stray;
            }
        } else {
            // Duplicate or reordered packet.
            Arrival::Valid
        };
        self.received = self.received.wrapping_add(1);
        self.valid_since_report = true;
        arrival
    }

    /// Returns `(fraction_lost, cumulative_lost, extended_highest_seq)` as
    /// computed in [RFC 3550 appendix
    /// A.3](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.3), and
    /// starts a new reporting interval, or `None` if no valid packet has
    /// arrived since the last report.
    pub(crate) fn report(&mut self) -> Option<(u8, i32, u32)> {
        if !std::mem::take(&mut self.valid_since_report) {
            return None;
        }
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
        Some((fraction, lost as i32, extended_max))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Returns a source that has passed probation with `seq`.
    fn valid_seq(seq: u16) -> SeqState {
        let mut s = SeqState::new(seq.wrapping_sub(1));
        assert_eq!(s.update(seq.wrapping_sub(1)), Arrival::Probation);
        assert_eq!(s.update(seq), Arrival::Valid);
        s
    }

    #[test]
    fn probation() {
        // RFC 3550 appendix A.1: a new source is valid after MIN_SEQUENTIAL (2)
        // sequential packets; the first isn't counted.
        let mut s = SeqState::new(10);
        assert_eq!(s.update(10), Arrival::Probation);
        assert_eq!(s.report(), None);
        assert_eq!(s.update(11), Arrival::Valid);
        assert_eq!((s.base_seq, s.received), (11, 1));

        // A non-sequential packet on probation restarts probation from there.
        let mut s = SeqState::new(10);
        assert_eq!(s.update(10), Arrival::Probation);
        assert_eq!(s.update(20), Arrival::Probation);
        assert_eq!((s.probation, s.max_seq), (1, 20));
        assert_eq!(s.update(21), Arrival::Valid);
        assert_eq!((s.base_seq, s.received), (21, 1));
    }

    #[test]
    fn wrap() {
        let mut s = valid_seq(0xfffe);
        assert_eq!(s.update(0xffff), Arrival::Valid);
        assert_eq!(s.update(0), Arrival::Valid);
        assert_eq!(s.cycles, RTP_SEQ_MOD);
        assert_eq!(s.update(1), Arrival::Valid);
        assert_eq!(s.report(), Some((0, 0, RTP_SEQ_MOD + 1)));
    }

    #[test]
    fn misorder_and_duplicates() {
        let mut s = valid_seq(100);
        assert_eq!(s.update(102), Arrival::Valid);
        // Reordered and duplicate packets are valid and counted as received,
        // without moving the highest sequence number.
        assert_eq!(s.update(101), Arrival::Valid);
        assert_eq!(s.update(102), Arrival::Valid);
        assert_eq!(s.max_seq, 102);
        assert_eq!(s.received, 4);
        // The duplicate makes the loss negative.
        assert_eq!(s.report(), Some((0, -1, 102)));

        // A packet MAX_MISORDER behind is still reordered; one more is a jump.
        let mut s = valid_seq(1000);
        assert_eq!(s.update(1000 - MAX_MISORDER + 1), Arrival::Valid);
        assert_eq!(s.max_seq, 1000);
        assert_eq!(s.update(1000 - MAX_MISORDER), Arrival::Stray);
        assert_eq!(s.bad_seq, u32::from(1000 - MAX_MISORDER + 1));
    }

    #[test]
    fn large_jump_resyncs() {
        let mut s = valid_seq(10);
        // A gap of less than MAX_DROPOUT is loss.
        assert_eq!(s.update(10 + MAX_DROPOUT - 1), Arrival::Valid);
        let max = s.max_seq;
        // A jump of MAX_DROPOUT or more is dropped...
        assert_eq!(s.update(max.wrapping_add(MAX_DROPOUT)), Arrival::Stray);
        assert_eq!(s.max_seq, max);
        // ...unless the next packet follows it: then the sender is assumed to
        // have restarted, and the statistics start over from there.
        assert_eq!(s.update(20_000), Arrival::Stray);
        assert_eq!(s.bad_seq, 20_001);
        assert_eq!(s.update(20_001), Arrival::Restart);
        assert_eq!((s.base_seq, s.max_seq, s.received), (20_001, 20_001, 1));
        assert_eq!(s.report(), Some((0, 0, 20_001)));
    }

    #[test]
    fn loss() {
        // RFC 3550 appendix A.3, across a wrap: 0xfff1 through 0x000e is 30
        // expected packets; 26 arrive.
        let mut s = valid_seq(0xfff1);
        for seq in 0xfff2..=0xffff {
            assert_eq!(s.update(seq), Arrival::Valid);
        }
        for seq in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 14] {
            assert_eq!(s.update(seq), Arrival::Valid);
        }
        assert_eq!(s.received, 26);
        // fraction = (4 << 8) / 30 = 34.
        assert_eq!(s.report(), Some((34, 4, RTP_SEQ_MOD + 14)));

        // Nothing new: no report.
        assert_eq!(s.report(), None);

        // 15..=24 expected (10), 5 arrive: half lost in the interval.
        for seq in [16, 18, 20, 22, 24] {
            assert_eq!(s.update(seq), Arrival::Valid);
        }
        assert_eq!(s.report(), Some((128, 9, RTP_SEQ_MOD + 24)));

        // The cumulative count is clamped to 24 signed bits.
        s.received = 0;
        s.base_seq = 0;
        s.cycles = 0x0100_0000;
        s.valid_since_report = true;
        assert_eq!(s.report().unwrap().1, 0x7f_ffff);
        s.received = 0x0200_0000;
        s.valid_since_report = true;
        assert_eq!(s.report().unwrap().1, -0x80_0000);
    }
}
