// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [`Source`]: the state of one RTP source (SSRC) within an RTP session.

use std::num::NonZeroU32;
use std::time::Instant;

use super::reorder::{self, ReorderOptions, Reordered, Reorderer};
use super::timeline::Extender;
use super::{Continuity, PacketHeader};
use crate::NtpTimestamp;
use crate::buf::MarkBuf;

/// Interarrival jitter state, as in [RFC 3550 appendix
/// A.8](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.8).
#[derive(Clone, Debug)]
pub(crate) struct Jitter {
    /// The arrival time that arrival timestamps are relative to.
    epoch: Instant,

    /// The relative transit time of the previous packet, if any.
    transit: Option<u32>,

    /// The jitter estimate, scaled by 16 as in appendix A.8's integer version.
    pub(crate) scaled: u32,
}

impl Jitter {
    pub(crate) fn new(epoch: Instant) -> Self {
        Jitter {
            epoch,
            transit: None,
            scaled: 0,
        }
    }

    /// Updates the estimate with a packet with RTP timestamp `timestamp` which
    /// arrived at `arrival`, with a clock rate of `clock_rate` Hz.
    pub(crate) fn update(&mut self, clock_rate: u32, timestamp: u32, arrival: Instant) {
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
    pub(crate) fn get(&self) -> u32 {
        self.scaled >> 4
    }
}

/// The last sender report received from a source.
#[derive(Copy, Clone, Debug)]
struct LastSenderReport {
    /// The middle 32 bits of its NTP timestamp.
    lsr: u32,

    /// When it arrived.
    arrival: Instant,
}

/// A packet popped from a [`Source`], in sequence order.
pub(crate) struct Popped<T> {
    pub(crate) reordered: Reordered<T>,

    /// The packet's extended timestamp, from the source's own base.
    pub(crate) timestamp: i64,

    pub(crate) continuity: Continuity,
}

/// The state of one source (SSRC) within an RTP session, as in the source
/// table of [RFC 3550 section 6.2.1 and appendix
/// A.1](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.1): its
/// reorder buffer and sequence number state, jitter, timestamp extension, and
/// sender report.
pub(crate) struct Source<T> {
    pub(crate) ssrc: u32,
    reorderer: Reorderer<T>,
    jitter: Option<Jitter>,
    extender: Extender,
    last_sr: Option<LastSenderReport>,

    /// When the latest RTP or RTCP packet from this source arrived.
    pub(crate) last_heard: Instant,

    /// True once a packet from this source has been reported as
    /// [`super::Pushed::Unselected`].
    pub(crate) reported_unselected: bool,

    /// True once this source has sent an RTCP BYE.
    pub(crate) bye: bool,

    /// Packets popped and dropped since the last packet returned, which the
    /// next packet's [`Continuity`] includes.
    dropped_since_returned: u16,

    /// True if a restart was popped and dropped since the last packet
    /// returned.
    restart_since_returned: bool,
}

impl<T> std::fmt::Debug for Source<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Source")
            .field("ssrc", &format_args!("{:08x}", self.ssrc))
            .field("reorderer", &self.reorderer)
            .field("bye", &self.bye)
            .finish()
    }
}

impl<T> Source<T> {
    pub(crate) fn new(
        ssrc: u32,
        options: ReorderOptions,
        initial_sequence_number: Option<u16>,
        now: Instant,
    ) -> Self {
        Self {
            ssrc,
            reorderer: Reorderer::new(options, initial_sequence_number),
            jitter: None,
            extender: Extender::default(),
            last_sr: None,
            last_heard: now,
            reported_unselected: false,
            bye: false,
            dropped_since_returned: 0,
            restart_since_returned: false,
        }
    }

    /// Returns true once the source is out of probation, as in RFC 3550
    /// appendix A.1.
    #[inline]
    pub(crate) fn is_valid(&self) -> bool {
        self.reorderer.is_valid()
    }

    /// Returns the number of packets held.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.reorderer.len()
    }

    /// Returns when the earliest packet still held arrived.
    #[inline]
    pub(crate) fn earliest_arrival(&self) -> Option<Instant> {
        self.reorderer.earliest_arrival()
    }

    #[inline]
    pub(crate) fn reorder_counters(&self) -> reorder::ReorderCounters {
        self.reorderer.counters()
    }

    /// Adds an RTP packet; see [`Reorderer::push`].
    pub(crate) fn push(
        &mut self,
        buf: &MarkBuf,
        header: PacketHeader,
        pos: u64,
        now: Instant,
        clock_rate: NonZeroU32,
        item: T,
    ) -> reorder::Pushed {
        self.last_heard = self.last_heard.max(now);
        let rtp_timestamp = header.timestamp();
        let pushed = self.reorderer.push(buf, header, pos, now, item);

        // Jitter uses the packets the sequence number statistics count.
        if self.reorderer.last_arrival_counted() {
            self.jitter.get_or_insert_with(|| Jitter::new(now)).update(
                clock_rate.get(),
                rtp_timestamp,
                now,
            );
        }
        pushed
    }

    /// Pops the next due packet, or with `now` of `None`, the next packet
    /// only if the source holds too many. Extends its timestamp.
    ///
    /// Returns `None` if no packet is due. A packet whose timestamp can't be
    /// extended (only possible with a hostile sender) is dropped and
    /// `dropped` is incremented; its loss is included in the next packet's
    /// [`Continuity`].
    pub(crate) fn pop(
        &mut self,
        buf: &MarkBuf,
        now: Option<Instant>,
        dropped: &mut u64,
    ) -> Option<Popped<T>> {
        loop {
            let reordered = match now {
                Some(now) => self.reorderer.pop(buf, now)?,
                None => self.reorderer.pop_overflow(buf)?,
            };
            let Some(timestamp) = self.extender.advance_to(reordered.header.timestamp()) else {
                *dropped += 1;
                self.note_dropped(&reordered);
                continue;
            };
            let continuity = self.continuity(&reordered);
            return Some(Popped {
                reordered,
                timestamp,
                continuity,
            });
        }
    }

    /// Notes that `reordered` was popped and dropped, so the next packet
    /// returned reflects its loss.
    pub(crate) fn note_dropped(&mut self, reordered: &Reordered<T>) {
        self.restart_since_returned |= reordered.restarted;
        self.dropped_since_returned = self
            .dropped_since_returned
            .saturating_add(reordered.skipped)
            .saturating_add(1);
    }

    /// Returns the continuity of `reordered`, to be returned, including any
    /// packets dropped since the last packet returned.
    fn continuity(&mut self, reordered: &Reordered<T>) -> Continuity {
        let restarted = reordered.restarted || std::mem::take(&mut self.restart_since_returned);
        let lost = reordered
            .skipped
            .saturating_add(std::mem::take(&mut self.dropped_since_returned));
        if restarted {
            Continuity::Discontinuity
        } else {
            Continuity::from_loss(lost)
        }
    }

    /// Pops and drops every due packet, returning how many.
    pub(crate) fn drain(&mut self, buf: &MarkBuf, now: Instant) -> u64 {
        let mut n = 0;
        while let Some(r) = self.reorderer.pop(buf, now) {
            self.note_dropped(&r);
            n += 1;
        }
        n
    }

    /// Returns when [`Source::pop`] should next be called; see
    /// [`Reorderer::poll_timeout`].
    #[inline]
    pub(crate) fn poll_timeout(&self) -> Option<Instant> {
        self.reorderer.poll_timeout()
    }

    /// Notes a sender report from this source which arrived at `now`, and
    /// returns its RTP timestamp extended from this source's base, or `None`
    /// on overflow.
    pub(crate) fn sender_report(
        &mut self,
        ntp: NtpTimestamp,
        rtp_timestamp: u32,
        now: Instant,
    ) -> Option<i64> {
        self.last_heard = self.last_heard.max(now);
        self.last_sr = Some(LastSenderReport {
            lsr: (ntp.0 >> 16) as u32,
            arrival: now,
        });
        self.extender.place(rtp_timestamp)
    }

    /// Returns reception statistics for a report block as of `now` and starts
    /// a new reporting interval, or `None` if no packet has been counted
    /// since the last report.
    pub(crate) fn reception_report(&mut self, now: Instant) -> Option<super::ReceptionReport> {
        let (fraction_lost, cumulative_lost, extended_highest_seq) =
            self.reorderer.reception_report()?;

        // LSR and DLSR are 0 until a sender report from this source has
        // arrived (RFC 3550 section 6.4.1).
        let (lsr, dlsr) = match self.last_sr {
            Some(sr) => {
                let delay = now.saturating_duration_since(sr.arrival);
                let dlsr = (delay.as_nanos() * 65_536 / 1_000_000_000).min(u128::from(u32::MAX));
                (sr.lsr, dlsr as u32)
            }
            None => (0, 0),
        };
        Some(super::ReceptionReport {
            ssrc: self.ssrc,
            fraction_lost,
            cumulative_lost,
            extended_highest_seq,
            jitter: self.jitter.as_ref().map_or(0, Jitter::get),
            lsr,
            dlsr,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;

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

    fn push(s: &mut Source<()>, buf: &mut MarkBuf, seq: u16, ts: u32, at: Instant) {
        let raw = crate::rtp::build_raw_rtp(seq, ts, 96, s.ssrc, true, *b"x").unwrap();
        let pos = buf.end();
        buf.extend(&raw);
        buf.advance_unparsed(buf.end());
        let header = PacketHeader::validate(&raw[..]).unwrap().header;
        s.push(buf, header, pos, at, NonZeroU32::new(90_000).unwrap(), ());
    }

    #[test]
    fn report() {
        let t0 = Instant::now();
        let mut buf = MarkBuf::new(1024);
        let mut s = Source::<()>::new(0x1234, ReorderOptions::default(), None, t0);

        // A sender report before any RTP.
        s.sender_report(NtpTimestamp(0xe436_2f99_cccc_cccc), 0, t0);

        push(&mut s, &mut buf, 1, 0, t0); // probation; not counted.
        assert!(!s.is_valid());
        push(&mut s, &mut buf, 2, 900, t0 + Duration::from_millis(10));
        assert!(s.is_valid());
        push(&mut s, &mut buf, 4, 2_700, t0 + Duration::from_millis(40)); // 10 ms late.
        let now = t0 + Duration::from_millis(1500);
        assert_eq!(
            s.reception_report(now),
            Some(crate::rtp::ReceptionReport {
                ssrc: 0x1234,
                fraction_lost: 85, // 1 of 3.
                cumulative_lost: 1,
                extended_highest_seq: 4,
                jitter: 56, // 900 / 16
                lsr: 0x2f99_cccc,
                dlsr: 98_304, // 1.5 * 65536
            })
        );
        assert_eq!(s.reception_report(now), None);
    }

    /// Popped packets carry their continuity, including those dropped since
    /// the last one returned.
    #[test]
    fn continuity() {
        let t0 = Instant::now();
        let mut buf = MarkBuf::new(1024);
        let opts = ReorderOptions::default().max_delay(Duration::ZERO);
        let mut s = Source::<()>::new(1, opts, None, t0);
        let mut dropped = 0;
        let mut pop = |s: &mut Source<()>, buf: &MarkBuf| {
            let p = s.pop(buf, Some(t0), &mut dropped).unwrap();
            (p.reordered.header.sequence_number(), p.continuity)
        };
        push(&mut s, &mut buf, 1, 0, t0);
        assert_eq!(pop(&mut s, &buf), (1, Continuity::Contiguous));
        push(&mut s, &mut buf, 3, 0, t0);
        assert_eq!(pop(&mut s, &buf), (3, Continuity::from_loss(1)));
        push(&mut s, &mut buf, 4, 0, t0);
        push(&mut s, &mut buf, 6, 0, t0);
        assert_eq!(s.drain(&buf, t0), 2);
        push(&mut s, &mut buf, 7, 0, t0);
        assert_eq!(pop(&mut s, &buf), (7, Continuity::from_loss(3)));
    }
}
