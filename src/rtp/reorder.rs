// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [`Reorderer`]: puts received RTP packets back in sequence order.

use std::collections::VecDeque;
use std::time::{Duration, Instant};

use super::PacketHeader;
use super::seq::{Arrival, SeqState};
use crate::buf::{Mark, MarkBuf};

/// Options for a [`Reorderer`].
#[derive(Copy, Clone, Debug)]
pub struct ReorderOptions {
    pub(crate) max_delay: Duration,
    pub(crate) max_packets: u16,
    pub(crate) initial_sequence_number: Option<u16>,
}

impl Default for ReorderOptions {
    fn default() -> Self {
        Self {
            max_delay: Duration::from_millis(50),
            max_packets: 128,
            initial_sequence_number: None,
        }
    }
}

impl ReorderOptions {
    /// Sets how long to wait for a missing packet before giving up on it.
    /// Defaults to 50 milliseconds.
    ///
    /// This is the most latency reordering adds, once a stream has started.
    /// Zero returns each packet as soon as it arrives, dropping any which
    /// arrive after a later one.
    #[inline]
    pub fn max_delay(self, max_delay: Duration) -> Self {
        Self { max_delay, ..self }
    }

    /// Sets how many packets to hold while waiting for a missing packet
    /// before giving up on it. Defaults to 128.
    ///
    /// This bounds the buffer space held, in addition to
    /// [`ReorderOptions::max_delay`].
    #[inline]
    pub fn max_packets(self, max_packets: u16) -> Self {
        Self {
            max_packets,
            ..self
        }
    }

    /// Sets the first sequence number to return, e.g. from the `PLAY`
    /// response's `RTP-Info` header.
    ///
    /// By default, the reorderer waits up to [`ReorderOptions::max_delay`]
    /// before returning the first packet, in case packets with earlier
    /// sequence numbers arrive. With a known first sequence number, it returns
    /// that packet as soon as it arrives.
    #[inline]
    pub fn initial_sequence_number(self, seq: u16) -> Self {
        Self {
            initial_sequence_number: Some(seq),
            ..self
        }
    }
}

/// The outcome of [`Reorderer::push`].
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Pushed {
    /// The packet is held until [`Reorderer::pop`] returns it.
    Held,

    /// The packet was discarded as a duplicate of one held.
    Duplicate,

    /// The packet was discarded because it arrived after the reorderer
    /// returned a later packet: it was too late or a duplicate of one
    /// returned.
    Late,

    /// The packet was discarded because its sequence number jumped too far
    /// from the others', as described in [RFC 3550 appendix
    /// A.1](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.1). If
    /// the next packet follows it, the sender is assumed to have restarted;
    /// see [`Reordered::restarted`].
    Stray,
}

/// A packet returned by [`Reorderer::pop`].
#[derive(Debug)]
#[non_exhaustive]
pub struct Reordered<T> {
    /// The caller's item supplied to [`Reorderer::push`].
    pub item: T,

    /// The packet's header.
    pub header: PacketHeader,

    /// The position to pass to [`crate::rtp::ReceivedPacketRef::with_pin_pos`].
    ///
    /// This is at or before the packet's own position and that of every
    /// packet still held, all of which [`Reorderer::pop`] will return later.
    pub pin_pos: u64,

    /// True if the sender restarted its sequence numbers before this packet,
    /// so it's unrelated to the packet returned before it. The caller should
    /// call [`super::Receiver::restart_sequence`] before passing it on.
    pub restarted: bool,
}

/// Counts of packets a [`Reorderer`] discarded or gave up on.
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
pub struct ReorderCounters {
    /// Packets discarded as [`Pushed::Late`].
    pub late: u64,

    /// Packets discarded as [`Pushed::Duplicate`].
    pub duplicates: u64,

    /// Packets discarded as [`Pushed::Stray`].
    pub strays: u64,

    /// Times the sender restarted its sequence numbers.
    pub restarts: u64,

    /// Missing packets given up on.
    pub skipped: u64,

    /// Held packets discarded because the buffer revoked their data; see
    /// [`crate::buf::MarkBuf::set_max_retained`]. Like missing packets, these
    /// are also counted in `skipped` when given up on.
    pub evicted: u64,
}

struct Held<T> {
    header: PacketHeader,
    pos: u64,
    arrival: Instant,
    item: T,
}

/// A held packet's place in sequence order: its sequence number and its index
/// in push order, as described at [`Reorderer::packets`].
#[derive(Copy, Clone)]
struct Slot {
    seq: u16,
    id: u64,
}

/// Puts RTP packets from a single stream (one SSRC) back in sequence order,
/// and keeps the arrival statistics of [RFC 3550 appendix
/// A.1](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.1).
///
/// This is sans-I/O and works with packets in place within a [`MarkBuf`]. The
/// caller parses each packet's header via [`PacketHeader::validate`], then:
///
/// 1.  advances the buffer's `unparsed()` position past the packet and calls
///     [`Reorderer::push`], which pins the packet's data in the buffer.
/// 2.  calls [`Reorderer::pop`] until it returns `None`, and for each packet,
///     calls [`super::Receiver::rtp`] and builds a
///     [`crate::rtp::ReceivedPacketRef`] using [`Reordered::pin_pos`].
/// 3.  calls `pop` again by [`Reorderer::poll_timeout`], to give up on
///     missing packets.
///
/// Unless [`ReorderOptions::initial_sequence_number`] is set, the reorderer
/// waits up to [`ReorderOptions::max_delay`] before returning the first
/// packet, in case packets with earlier sequence numbers arrive. Afterward,
/// it returns each packet as soon as those before it have been returned or
/// given up on. A packet whose predecessor was given up on, or which arrives
/// after a later packet was returned, is [`Pushed::Late`] and dropped.
///
/// It also recognizes a sender restarting its sequence numbers, as RFC 3550
/// appendix A.1 does: after a packet whose sequence number jumps far from the
/// others ([`Pushed::Stray`]), a packet following it starts a new sequence.
/// The reorderer returns the packets it holds from the old sequence, then
/// continues with the new one, marking its first packet
/// [`Reordered::restarted`].
///
/// With a [`ReorderOptions::max_delay`] of zero, it returns each packet
/// immediately, so it only drops late packets and recognizes restarts.
///
/// It doesn't check SSRCs; that's left to the [`super::Receiver`].
pub struct Reorderer<T> {
    options: ReorderOptions,

    /// Held packets in the order pushed, or `None` for those since returned
    /// or discarded. The first and last are always `Some`.
    ///
    /// Positions and arrival times never decrease in this order, so the first
    /// has the earliest of each. Each packet's id is `first_id` plus its
    /// index here.
    packets: VecDeque<Option<Held<T>>>,

    /// The id of `packets[0]`.
    first_id: u64,

    /// Packets from before a restart, in order, to return before `held`.
    ready: VecDeque<Slot>,

    /// Held packets, sorted by sequence number relative to `next`.
    held: VecDeque<Slot>,

    /// The next sequence number to return, once one is known.
    next: Option<u16>,

    /// True once a packet has been returned or the first sequence number is
    /// known. Before then, an earlier packet can move `next` backward.
    started: bool,

    /// True if the next packet returned from `held` starts a new sequence.
    restart_pending: bool,

    /// Pins the earliest position of any packet held and of the packet last
    /// returned by `pop`, until the next call, or `None` if there are none.
    mark: Option<Mark>,

    /// After `pop` returns a packet, where to move `mark` on the next call:
    /// the earliest position of any packet still held, if any.
    release_to: Option<Option<u64>>,

    /// Arrival statistics, once a packet has arrived.
    seq: Option<SeqState>,

    /// How the statistics classified the last packet pushed.
    last_arrival: Option<Arrival>,

    counters: ReorderCounters,
}

impl<T> std::fmt::Debug for Reorderer<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let seqs = |q: &VecDeque<Slot>| q.iter().map(|s| s.seq).collect::<Vec<_>>();
        f.debug_struct("Reorderer")
            .field("options", &self.options)
            .field("next", &self.next)
            .field("started", &self.started)
            .field("ready", &seqs(&self.ready))
            .field("held", &seqs(&self.held))
            .field("counters", &self.counters)
            .finish()
    }
}

impl<T> Reorderer<T> {
    pub fn new(options: ReorderOptions) -> Self {
        Self {
            options,
            packets: VecDeque::new(),
            first_id: 0,
            ready: VecDeque::new(),
            held: VecDeque::new(),
            next: options.initial_sequence_number,
            started: options.initial_sequence_number.is_some(),
            restart_pending: false,
            mark: None,
            release_to: None,
            seq: None,
            last_arrival: None,
            counters: ReorderCounters::default(),
        }
    }

    /// Returns the number of packets held.
    #[inline]
    pub fn len(&self) -> usize {
        self.ready.len() + self.held.len()
    }

    /// Returns true if no packets are held.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns counts of packets discarded or given up on so far.
    #[inline]
    pub fn counters(&self) -> ReorderCounters {
        self.counters
    }

    /// Returns `(fraction_lost, cumulative_lost, extended_highest_seq)` for an
    /// RTCP report block and starts a new reporting interval, or `None` if no
    /// valid packet has arrived since the last report.
    pub(crate) fn reception_report(&mut self) -> Option<(u8, i32, u32)> {
        self.seq.as_mut()?.report()
    }

    /// Returns true if the last packet pushed was counted as received in the
    /// arrival statistics. Per RFC 3550 appendix A.1, packets are counted
    /// once the source is out of probation, including duplicates and late
    /// packets but not strays. Receiver reports' jitter uses the same packets.
    pub(crate) fn last_arrival_counted(&self) -> bool {
        matches!(self.last_arrival, Some(Arrival::Valid | Arrival::Restart))
    }

    /// Offset of `seq` from `next`.
    #[inline]
    fn offset(next: u16, seq: u16) -> u16 {
        seq.wrapping_sub(next)
    }

    /// Adds a packet received at `now`, whose data starts at `pos` in `buf`.
    ///
    /// `item` is returned with the packet by [`Reorderer::pop`]; it might
    /// hold the packet's context and payload range, for example.
    ///
    /// Packets should be pushed in the order they were received. If `now` is
    /// before a packet still held was pushed, the reorderer treats this packet
    /// as arriving at the same time as that one.
    ///
    /// # Panics
    ///
    /// Panics unless `pos` is within `[buf.start(), buf.unparsed()]`, or if
    /// `pos` is before that of a packet still held.
    pub fn push(
        &mut self,
        buf: &MarkBuf,
        header: PacketHeader,
        pos: u64,
        now: Instant,
        item: T,
    ) -> Pushed {
        self.release(buf);
        assert!(
            pos >= buf.start() && pos <= buf.unparsed(),
            "push({pos}): must be within [{}, {}]",
            buf.start(),
            buf.unparsed(),
        );
        let last = self
            .packets
            .back()
            .map(|p| p.as_ref().expect("last is Some"));
        if let Some(last) = last {
            assert!(
                pos >= last.pos,
                "push({pos}): before held packet at {}",
                last.pos
            );
        }
        let arrival_at = last.map_or(now, |l| now.max(l.arrival));
        let seq = header.sequence_number();
        let arrival = self
            .seq
            .get_or_insert_with(|| SeqState::new(seq))
            .update(seq);
        self.last_arrival = Some(arrival);
        match arrival {
            Arrival::Stray => {
                self.counters.strays += 1;
                return Pushed::Stray;
            }
            Arrival::Restart => {
                // Return what's held from the old sequence first, in order.
                self.counters.restarts += 1;
                self.ready.append(&mut self.held);
                self.next = Some(seq);
                self.started = true;
                self.restart_pending = true;
            }
            Arrival::Probation | Arrival::Valid => {}
        }
        let mut next = *self.next.get_or_insert(seq);
        let offset = Self::offset(next, seq);
        if offset >= 0x8000 {
            // Before `next`. Before starting, move `next` back, provided all
            // held packets stay within half the sequence number space of it.
            let back = offset.wrapping_neg();
            let max_offset = self
                .held
                .back()
                .map(|s| Self::offset(next, s.seq))
                .unwrap_or(0);
            if self.started || u32::from(max_offset) + u32::from(back) >= 0x8000 {
                self.counters.late += 1;
                return Pushed::Late;
            }
            next = seq;
            self.next = Some(next);
        }
        let offset = Self::offset(next, seq);
        let i = self
            .held
            .partition_point(|s| Self::offset(next, s.seq) < offset);
        if self.held.get(i).is_some_and(|s| s.seq == seq) {
            self.counters.duplicates += 1;
            return Pushed::Duplicate;
        }
        let id = self.first_id + crate::to_u64(self.packets.len());
        self.held.insert(i, Slot { seq, id });
        self.packets.push_back(Some(Held {
            header,
            pos,
            arrival: arrival_at,
            item,
        }));
        if self.mark.is_none() {
            self.mark = Some(buf.add_mark_at(pos));
        }
        Pushed::Held
    }

    /// Returns the earliest-pushed packet held.
    #[inline]
    fn earliest(&self) -> Option<&Held<T>> {
        self.packets
            .front()
            .map(|p| p.as_ref().expect("first is Some"))
    }

    /// Removes and returns the packet with the given id.
    fn take(&mut self, id: u64) -> Held<T> {
        let i = usize::try_from(id - self.first_id).expect("id is within packets");
        let h = self.packets[i].take().expect("packet is held");
        while self.packets.front().is_some_and(Option::is_none) {
            self.packets.pop_front();
            self.first_id += 1;
        }
        while self.packets.back().is_some_and(Option::is_none) {
            self.packets.pop_back();
        }
        h
    }

    /// Returns true if the front of `held` is next in sequence.
    fn front_in_order(&self) -> bool {
        self.started && self.held.front().is_some_and(|f| Some(f.seq) == self.next)
    }

    /// Returns true if the front of `held` should be returned at `now`.
    fn front_due(&self, now: Instant) -> bool {
        !self.held.is_empty()
            && (self.front_in_order()
                || self.held.len() > usize::from(self.options.max_packets)
                || self.give_up_at().is_some_and(|t| t <= now))
    }

    /// Returns when the oldest held packet will have waited `max_delay`.
    ///
    /// Only valid when `ready` is empty, so all packets are in `held`.
    fn give_up_at(&self) -> Option<Instant> {
        debug_assert!(self.ready.is_empty());
        self.earliest().map(|h| h.arrival + self.options.max_delay)
    }

    /// Returns the next packet in sequence order, if it's due at `now`.
    ///
    /// A packet is due when it's next in sequence, or when giving up on any
    /// missing packets before it, because a held packet has waited
    /// [`ReorderOptions::max_delay`] or more than
    /// [`ReorderOptions::max_packets`] are held.
    ///
    /// `buf` must be the buffer passed to [`Reorderer::push`]. The returned
    /// packet's data stays pinned until the next call to `push` or `pop`, so
    /// the caller can build a [`crate::rtp::ReceivedPacketRef`] to it.
    pub fn pop(&mut self, buf: &MarkBuf, now: Instant) -> Option<Reordered<T>> {
        self.release(buf);
        let (slot, restarted) = match self.ready.pop_front() {
            Some(s) => (s, false),
            None => {
                if !self.front_due(now) {
                    return None;
                }
                let s = self.held.pop_front().expect("front_due implies non-empty");
                if self.started
                    && let Some(next) = self.next
                {
                    self.counters.skipped += u64::from(Self::offset(next, s.seq));
                }
                self.next = Some(s.seq.wrapping_add(1));
                self.started = true;
                (s, std::mem::take(&mut self.restart_pending))
            }
        };
        let h = self.take(slot.id);
        let rest = self.earliest().map(|e| e.pos);
        self.release_to = Some(rest);
        let pin_pos = rest.map_or(h.pos, |r| r.min(h.pos));
        Some(Reordered {
            item: h.item,
            header: h.header,
            pin_pos,
            restarted,
        })
    }

    /// Releases the packet last returned by `pop`, and discards held packets
    /// whose data the buffer has discarded after revoking `mark`.
    fn release(&mut self, buf: &MarkBuf) {
        let release_to = self.release_to.take();
        let Some(mark) = &mut self.mark else {
            return;
        };
        if mark.is_revoked() {
            // The buffer discards data only before its new start, so held
            // packets from there on can be pinned again. Positions never
            // decrease in push order, so the discarded packets come first.
            let start = buf.start();
            while let Some(p) = self.packets.front() {
                match p {
                    Some(h) if h.pos >= start => break,
                    Some(_) => self.counters.evicted += 1,
                    None => {}
                }
                self.packets.pop_front();
                self.first_id += 1;
            }
            let first_id = self.first_id;
            self.ready.retain(|s| s.id >= first_id);
            self.held.retain(|s| s.id >= first_id);
            self.mark = self.earliest().map(|h| buf.add_mark_at(h.pos));
            return;
        }
        match release_to {
            None => {}
            Some(None) => self.mark = None,
            Some(Some(pos)) => mark.move_forward(pos),
        }
    }

    /// Returns when [`Reorderer::pop`] should next be called, absent another
    /// [`Reorderer::push`], or `None` if no packets are held.
    ///
    /// This may be in the past, if a packet is due now.
    pub fn poll_timeout(&self) -> Option<Instant> {
        if !self.ready.is_empty()
            || self.front_in_order()
            || self.held.len() > usize::from(self.options.max_packets)
        {
            // Due now.
            return self.earliest().map(|h| h.arrival);
        }
        self.give_up_at()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rtp::build_raw_rtp;

    const DELAY: Duration = Duration::from_millis(50);

    struct Fixture {
        buf: MarkBuf,
        r: Reorderer<()>,
        t0: Instant,
    }

    impl Fixture {
        fn new(options: ReorderOptions) -> Self {
            Self {
                buf: MarkBuf::new(1024),
                r: Reorderer::new(options),
                t0: Instant::now(),
            }
        }

        /// Writes a packet with the given sequence number and pushes it,
        /// returning its position.
        fn push(&mut self, seq: u16, at_ms: u64) -> (Pushed, u64) {
            let raw = build_raw_rtp(seq, 0, 96, 1, true, *b"x").unwrap();
            let pos = self.buf.end();
            self.buf.extend(&raw);
            self.buf.advance_unparsed(self.buf.end());
            let header = PacketHeader::validate(&raw[..]).unwrap().header;
            let t = self.t0 + Duration::from_millis(at_ms);
            (self.r.push(&self.buf, header, pos, t, ()), pos)
        }

        /// Pops all due packets, returning their sequence numbers.
        fn pop(&mut self, at_ms: u64) -> Vec<u16> {
            let t = self.t0 + Duration::from_millis(at_ms);
            std::iter::from_fn(|| self.r.pop(&self.buf, t))
                .map(|p| p.header.sequence_number())
                .collect()
        }
    }

    #[test]
    fn waits_before_starting() {
        let mut f = Fixture::new(ReorderOptions::default());
        f.push(10, 0);
        f.push(11, 10);
        assert_eq!(f.pop(10), []);
        assert_eq!(f.r.poll_timeout(), Some(f.t0 + DELAY));

        // An earlier packet before starting moves the start back.
        assert_eq!(f.push(9, 20).0, Pushed::Held);
        assert_eq!(f.pop(49), []);
        assert_eq!(f.pop(50), [9, 10, 11]);
        assert_eq!(f.r.poll_timeout(), None);

        // Afterward, in-order packets are returned immediately.
        f.push(12, 60);
        assert_eq!(f.r.poll_timeout(), Some(f.t0 + Duration::from_millis(60)));
        assert_eq!(f.pop(60), [12]);
    }

    #[test]
    fn reorders() {
        let mut f = Fixture::new(ReorderOptions::default());
        f.push(5, 0);
        assert_eq!(f.pop(50), [5]);
        f.push(7, 60);
        f.push(8, 61);
        assert_eq!(f.pop(61), []);
        assert_eq!(f.push(6, 62).0, Pushed::Held);
        assert_eq!(f.pop(62), [6, 7, 8]);
    }

    #[test]
    fn gives_up_after_delay() {
        let mut f = Fixture::new(ReorderOptions::default());
        f.push(5, 0);
        assert_eq!(f.pop(50), [5]);
        f.push(7, 60);
        f.push(8, 70);
        assert_eq!(f.r.poll_timeout(), Some(f.t0 + Duration::from_millis(110)));
        assert_eq!(f.pop(109), []);
        assert_eq!(f.pop(110), [7, 8]);

        // The missing packet is now late.
        assert_eq!(f.push(6, 120).0, Pushed::Late);
    }

    #[test]
    fn gives_up_when_full() {
        let mut f = Fixture::new(ReorderOptions::default().max_packets(2));
        f.push(0, 0);
        assert_eq!(f.pop(50), [0]);
        f.push(2, 60);
        f.push(3, 60);
        assert_eq!(f.pop(60), []);
        f.push(5, 60);
        assert_eq!(f.pop(60), [2, 3]);
        assert_eq!(f.pop(110), [5]);
    }

    #[test]
    fn duplicates() {
        let mut f = Fixture::new(ReorderOptions::default());
        f.push(0, 0);
        assert_eq!(f.pop(50), [0]);
        f.push(2, 60);
        assert_eq!(f.push(2, 60).0, Pushed::Duplicate);
        assert_eq!(f.push(0, 60).0, Pushed::Late);
    }

    #[test]
    fn initial_sequence_number() {
        let mut f = Fixture::new(ReorderOptions::default().initial_sequence_number(10));
        f.push(10, 0);
        assert_eq!(f.pop(0), [10]);
        assert_eq!(f.push(9, 0).0, Pushed::Late);

        // A gap after the known start is a gap, not a startup wait.
        let mut f = Fixture::new(ReorderOptions::default().initial_sequence_number(10));
        f.push(11, 0);
        assert_eq!(f.pop(49), []);
        assert_eq!(f.pop(50), [11]);
        assert_eq!(f.r.counters().skipped, 1);
    }

    #[test]
    fn zero_delay() {
        let mut f = Fixture::new(ReorderOptions::default().max_delay(Duration::ZERO));
        f.push(5, 0);
        assert_eq!(f.pop(0), [5]);
        f.push(7, 0);
        assert_eq!(f.pop(0), [7]);
        assert_eq!(f.push(6, 0).0, Pushed::Late);
        assert_eq!(
            f.r.counters(),
            ReorderCounters {
                late: 1,
                skipped: 1,
                ..Default::default()
            }
        );
    }

    #[test]
    fn restart() {
        let mut f = Fixture::new(ReorderOptions::default());
        for seq in 1000..1003 {
            f.push(seq, 0);
        }
        assert_eq!(f.pop(50), [1000, 1001, 1002]);
        f.push(1004, 60); // held, waiting for 1003.

        // A single stray packet is dropped...
        assert_eq!(f.push(10, 60).0, Pushed::Stray);
        assert_eq!(f.pop(60), Vec::<u16>::new());

        // ...but a packet following it starts a new sequence. The old
        // sequence's held packets are returned first.
        assert_eq!(f.push(11, 61).0, Pushed::Held);
        let t = f.t0 + Duration::from_millis(61);
        let p = f.r.pop(&f.buf, t).unwrap();
        assert_eq!((p.header.sequence_number(), p.restarted), (1004, false));
        let p = f.r.pop(&f.buf, t).unwrap();
        assert_eq!((p.header.sequence_number(), p.restarted), (11, true));
        assert!(f.r.pop(&f.buf, t).is_none());

        // Then the new sequence continues normally.
        f.push(12, 62);
        assert_eq!(f.pop(62), [12]);
        assert_eq!(
            f.r.counters(),
            ReorderCounters {
                strays: 1,
                restarts: 1,
                ..Default::default()
            }
        );
    }

    #[test]
    fn reception_report() {
        let mut f = Fixture::new(ReorderOptions::default());
        f.push(1, 0); // on probation, not counted.
        assert_eq!(f.r.reception_report(), None);
        f.push(2, 0);
        f.push(4, 0);
        f.push(4, 0); // duplicate, counted as received.
        assert_eq!(f.r.reception_report(), Some((0, 0, 4)));
    }

    #[test]
    fn wraparound() {
        let mut f = Fixture::new(ReorderOptions::default());
        f.push(0, 0);
        f.push(u16::MAX, 0);
        assert_eq!(f.pop(50), [u16::MAX, 0]);
        f.push(2, 60);
        f.push(1, 60);
        assert_eq!(f.pop(60), [1, 2]);
    }

    /// A held packet whose data the buffer revokes is discarded, not returned.
    #[test]
    fn evicted() {
        let mut f = Fixture::new(ReorderOptions::default());
        f.buf.set_max_retained(30); // each packet is 13 bytes.
        f.push(1, 0);
        assert_eq!(f.pop(50), [1]);
        f.push(3, 60); // held at 13, waiting for 2.
        f.push(4, 60); // 26
        f.push(5, 60); // 39
        f.push(6, 60); // 52; reclaiming before this revokes 3's mark.
        assert_eq!(f.pop(60), []);
        assert_eq!(f.pop(110), [4, 5, 6]);
        assert_eq!(
            f.r.counters(),
            ReorderCounters {
                evicted: 1,
                skipped: 2,
                ..Default::default()
            }
        );
    }

    /// A packet pushed with an earlier time than one held is treated as
    /// arriving with it.
    #[test]
    fn earlier_arrival_time() {
        let mut f = Fixture::new(ReorderOptions::default());
        f.push(1, 0);
        assert_eq!(f.pop(50), [1]);
        f.push(3, 60);
        f.push(4, 40);
        assert_eq!(f.r.poll_timeout(), Some(f.t0 + Duration::from_millis(110)));
        assert_eq!(f.pop(110), [3, 4]);
    }

    #[test]
    #[should_panic(expected = "before held packet")]
    fn pos_before_held() {
        let mut f = Fixture::new(ReorderOptions::default());
        f.push(2, 0);
        let (_, pos) = f.push(3, 0);
        let raw = build_raw_rtp(1, 0, 96, 1, true, *b"x").unwrap();
        let header = PacketHeader::validate(&raw[..]).unwrap().header;
        f.r.push(&f.buf, header, pos - 1, f.t0, ());
    }

    #[test]
    fn pin_pos() {
        let mut f = Fixture::new(ReorderOptions::default());
        let (_, pos2) = f.push(2, 0);
        let (_, pos1) = f.push(1, 0);
        let (_, pos3) = f.push(3, 0);
        assert!(pos2 < pos1 && pos1 < pos3);
        let t = f.t0 + DELAY;
        let p = f.r.pop(&f.buf, t).unwrap();
        assert_eq!((p.header.sequence_number(), p.pin_pos), (1, pos2));
        let p = f.r.pop(&f.buf, t).unwrap();
        assert_eq!((p.header.sequence_number(), p.pin_pos), (2, pos2));
        let p = f.r.pop(&f.buf, t).unwrap();
        assert_eq!((p.header.sequence_number(), p.pin_pos), (3, pos3));
    }

    /// Checks that a depacketizer accumulating an access unit from reordered
    /// packets retains all of their data, via [`Reordered::pin_pos`].
    ///
    /// The H.264 depacketizer pins only the access unit's first packet's
    /// position. Here that's an SEI, which arrives after the first slice.
    /// Without `pin_pos`, reclaiming buffer space before the final slice is
    /// pushed would discard the first slice, and building the frame would
    /// panic. (Parameter sets wouldn't do here; the depacketizer copies them.)
    #[cfg(feature = "h264")]
    #[test]
    fn h264_access_unit() {
        use crate::codec::{
            Accumulate, FrameFormat, VideoData, VideoDepacketizer, VideoFrameEnd, VideoFrameStart,
            VideoHandler,
        };
        use crate::rtp::ReceivedPacketRef;
        use crate::rtp::ValidatedPacket;
        use crate::rtp::{Receiver, ReceiverOptions};

        #[derive(Default)]
        struct Frames(Vec<Vec<u8>>);
        impl VideoHandler<()> for Frames {
            fn frame_start(&mut self, _: &mut VideoFrameStart<'_, ()>) -> Accumulate {
                Accumulate::Yes
            }
            fn data(&mut self, _: &VideoData<'_>) {}
            fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, ()>) {
                self.0
                    .push(frame_end.complete_frame(FrameFormat::default()).unwrap());
            }
        }

        let mut d = VideoDepacketizer::<()>::new(
            "h264",
            90_000,
            Some(
                "packetization-mode=1;profile-level-id=4d002a;\
                 sprop-parameter-sets=Z00AKpWoHgCJ+WEAAAMAAQAAAwAyhA==,aO48gA==",
            ),
        )
        .unwrap();
        let mut receiver = Receiver::new(90_000, ReceiverOptions::default()).unwrap();
        let mut reorderer = Reorderer::<std::ops::Range<u64>>::new(ReorderOptions::default());
        let mut buf = MarkBuf::new(64);
        let mut frames = Frames::default();
        let t0 = Instant::now();

        let receive = |buf: &mut MarkBuf, r: &mut Reorderer<_>, seq, mark, payload: &[u8]| {
            let raw = build_raw_rtp(seq, 0, 96, 1, mark, payload.iter().copied()).unwrap();
            let pos = buf.end();
            buf.extend(&raw);
            buf.advance_unparsed(buf.end());
            let ValidatedPacket {
                header, payload, ..
            } = PacketHeader::validate(&raw[..]).unwrap();
            let payload = pos + u64::from(payload.start)..pos + u64::from(payload.end);
            assert_eq!(r.push(buf, header, pos, t0, payload), Pushed::Held);
        };
        let mut drain = |buf: &MarkBuf, r: &mut Reorderer<std::ops::Range<u64>>, now| {
            while let Some(p) = r.pop(buf, now) {
                let meta = receiver.rtp((), &p.header).unwrap();
                let len = u16::try_from(p.item.end - p.item.start).unwrap();
                let pkt =
                    ReceivedPacketRef::new(meta, buf, p.item.start, len).with_pin_pos(p.pin_pos);
                d.push(&pkt, &mut frames);
            }
        };

        const SEI: &[u8] = b"\x06\xe5\x01\xa7\x80";
        const SLICE_A: &[u8] = b"\x65slice a";
        const SLICE_B: &[u8] = b"\x65slice b";
        receive(&mut buf, &mut reorderer, 1, false, SLICE_A);
        receive(&mut buf, &mut reorderer, 0, false, SEI);
        drain(&buf, &mut reorderer, t0 + DELAY);
        receive(&mut buf, &mut reorderer, 2, true, SLICE_B);

        // Another datagram arrives, reclaiming space before it's popped.
        buf.extend(&[0; 64]);
        buf.advance_unparsed(buf.end());
        drain(&buf, &mut reorderer, t0 + DELAY);

        assert_eq!(frames.0.len(), 1);
        let frame = &frames.0[0];
        assert!(frame.windows(SEI.len()).any(|w| w == SEI), "{frame:02x?}");
        assert!(
            frame.windows(SLICE_A.len()).any(|w| w == SLICE_A),
            "{frame:02x?}"
        );
        assert!(frame.ends_with(SLICE_B), "{frame:02x?}");
    }

    /// Like `h264_access_unit`, for zeros the depacketizer's Annex B scanner
    /// holds back at the end of reordered FU-A fragments, whether or not the
    /// analyzer has released the data before them.
    #[cfg(feature = "h264")]
    #[test]
    fn h264_fu_a_annex_b_zeros() {
        use crate::codec::{
            Accumulate, VideoData, VideoDepacketizer, VideoFrameEnd, VideoFrameStart, VideoHandler,
        };
        use crate::rtp::ReceivedPacketRef;
        use crate::rtp::ValidatedPacket;
        use crate::rtp::{Receiver, ReceiverOptions};
        for accumulate in [Accumulate::No, Accumulate::Yes] {
            struct Frames {
                accumulate: Accumulate,
                data: Vec<u8>,
                ends: usize,
                losses: usize,
            }
            impl VideoHandler<()> for Frames {
                fn frame_start(&mut self, _: &mut VideoFrameStart<'_, ()>) -> Accumulate {
                    self.accumulate
                }
                fn data(&mut self, data: &VideoData<'_>) {
                    for d in data.data {
                        self.data.extend_from_slice(d);
                    }
                }
                fn frame_end(&mut self, _: &mut VideoFrameEnd<'_, ()>) {
                    self.ends += 1;
                }
                fn loss(&mut self, _: &crate::codec::Loss<'_, ()>) {
                    self.losses += 1;
                }
            }

            let mut d = VideoDepacketizer::<()>::new(
                "h264",
                90_000,
                Some(
                    "packetization-mode=1;profile-level-id=4d002a;\
                 sprop-parameter-sets=Z00AKpWoHgCJ+WEAAAMAAQAAAwAyhA==,aO48gA==",
                ),
            )
            .unwrap();
            let mut receiver = Receiver::new(90_000, ReceiverOptions::default()).unwrap();
            let mut reorderer = Reorderer::<std::ops::Range<u64>>::new(ReorderOptions::default());
            let mut buf = MarkBuf::new(64);
            let mut frames = Frames {
                accumulate,
                data: Vec::new(),
                ends: 0,
                losses: 0,
            };
            let t0 = Instant::now();

            let receive = |buf: &mut MarkBuf, r: &mut Reorderer<_>, seq, mark, payload: &[u8]| {
                let raw = build_raw_rtp(seq, 0, 96, 1, mark, payload.iter().copied()).unwrap();
                let pos = buf.end();
                buf.extend(&raw);
                buf.advance_unparsed(buf.end());
                let ValidatedPacket {
                    header, payload, ..
                } = PacketHeader::validate(&raw[..]).unwrap();
                let payload = pos + u64::from(payload.start)..pos + u64::from(payload.end);
                assert_eq!(r.push(buf, header, pos, t0, payload), Pushed::Held);
            };
            let mut drain = |buf: &MarkBuf, r: &mut Reorderer<std::ops::Range<u64>>, now| {
                while let Some(p) = r.pop(buf, now) {
                    let meta = receiver.rtp((), &p.header).unwrap();
                    let len = u16::try_from(p.item.end - p.item.start).unwrap();
                    let pkt = ReceivedPacketRef::new(meta, buf, p.item.start, len)
                        .with_pin_pos(p.pin_pos);
                    d.push(&pkt, &mut frames);
                }
            };

            // An IDR slice in three FU-A fragments, the first two ending in
            // zeros which may begin an Annex B separator. The second arrives
            // first, so it's earlier in the buffer.
            const START: &[u8] = b"\x7c\x85\x88ab\x00";
            const MIDDLE: &[u8] = b"\x7c\x05\x00";
            const END: &[u8] = b"\x7c\x45\x03cd";
            receive(&mut buf, &mut reorderer, 1, false, MIDDLE);
            receive(&mut buf, &mut reorderer, 0, false, START);
            drain(&buf, &mut reorderer, t0 + DELAY);

            // Other datagrams arrive, reclaiming space.
            for _ in 0..2 {
                buf.extend(&[0; 64]);
                buf.advance_unparsed(buf.end());
            }
            receive(&mut buf, &mut reorderer, 2, true, END);
            drain(&buf, &mut reorderer, t0 + DELAY);

            assert_eq!((frames.ends, frames.losses), (1, 0), "{accumulate:?}");
            assert_eq!(frames.data, b"\x65\x88ab\x00\x00\x03cd", "{accumulate:?}");
        }
    }
}
