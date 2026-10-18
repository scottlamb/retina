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
}

struct Held<T> {
    header: PacketHeader,
    pos: u64,
    arrival: Instant,
    mark: Mark,
    item: T,
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

    /// Packets from before a restart, in order, to return before `held`.
    ready: VecDeque<Held<T>>,

    /// Held packets, sorted by sequence number relative to `next`.
    held: VecDeque<Held<T>>,

    /// The next sequence number to return, once one is known.
    next: Option<u16>,

    /// True once a packet has been returned or the first sequence number is
    /// known. Before then, an earlier packet can move `next` backward.
    started: bool,

    /// True if the next packet returned from `held` starts a new sequence.
    restart_pending: bool,

    /// The mark of the last packet returned by `pop`, held until the next
    /// call so the caller can build a `ReceivedPacketRef` to it.
    last: Option<Mark>,

    /// Arrival statistics, once a packet has arrived.
    seq: Option<SeqState>,

    /// How the statistics classified the last packet pushed.
    last_arrival: Option<Arrival>,

    counters: ReorderCounters,
}

impl<T> std::fmt::Debug for Reorderer<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let seqs = |q: &VecDeque<Held<T>>| {
            q.iter()
                .map(|h| h.header.sequence_number())
                .collect::<Vec<_>>()
        };
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
            ready: VecDeque::new(),
            held: VecDeque::new(),
            next: options.initial_sequence_number,
            started: options.initial_sequence_number.is_some(),
            restart_pending: false,
            last: None,
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
    /// # Panics
    ///
    /// Panics unless `pos` is within `[buf.start(), buf.unparsed()]`.
    pub fn push(
        &mut self,
        buf: &MarkBuf,
        header: PacketHeader,
        pos: u64,
        now: Instant,
        item: T,
    ) -> Pushed {
        self.last = None;
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
                .map(|h| Self::offset(next, h.header.sequence_number()))
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
            .partition_point(|h| Self::offset(next, h.header.sequence_number()) < offset);
        if self
            .held
            .get(i)
            .is_some_and(|h| h.header.sequence_number() == seq)
        {
            self.counters.duplicates += 1;
            return Pushed::Duplicate;
        }
        self.held.insert(
            i,
            Held {
                header,
                pos,
                arrival: now,
                mark: buf.add_mark_at(pos),
                item,
            },
        );
        Pushed::Held
    }

    /// Returns true if the front of `held` is next in sequence.
    fn front_in_order(&self) -> bool {
        self.started
            && self
                .held
                .front()
                .is_some_and(|f| Some(f.header.sequence_number()) == self.next)
    }

    /// Returns true if the front of `held` should be returned at `now`.
    fn front_due(&self, now: Instant) -> bool {
        !self.held.is_empty()
            && (self.front_in_order()
                || self.held.len() > usize::from(self.options.max_packets)
                || self.give_up_at().is_some_and(|t| t <= now))
    }

    /// Returns when the oldest held packet will have waited `max_delay`.
    fn give_up_at(&self) -> Option<Instant> {
        self.held
            .iter()
            .map(|h| h.arrival)
            .min()
            .map(|a| a + self.options.max_delay)
    }

    /// Returns the next packet in sequence order, if it's due at `now`.
    ///
    /// A packet is due when it's next in sequence, or when giving up on any
    /// missing packets before it, because a held packet has waited
    /// [`ReorderOptions::max_delay`] or more than
    /// [`ReorderOptions::max_packets`] are held.
    ///
    /// The returned packet's data stays pinned until the next call to `push`
    /// or `pop`, so the caller can build a [`crate::rtp::ReceivedPacketRef`] to it.
    pub fn pop(&mut self, now: Instant) -> Option<Reordered<T>> {
        self.last = None;
        let (h, restarted) = match self.ready.pop_front() {
            Some(h) => (h, false),
            None => {
                if !self.front_due(now) {
                    return None;
                }
                let h = self.held.pop_front().expect("front_due implies non-empty");
                let seq = h.header.sequence_number();
                if self.started
                    && let Some(next) = self.next
                {
                    self.counters.skipped += u64::from(Self::offset(next, seq));
                }
                self.next = Some(seq.wrapping_add(1));
                self.started = true;
                (h, std::mem::take(&mut self.restart_pending))
            }
        };
        let pin_pos = self
            .ready
            .iter()
            .chain(self.held.iter())
            .map(|h| h.pos)
            .fold(h.pos, u64::min);
        self.last = Some(h.mark);
        Some(Reordered {
            item: h.item,
            header: h.header,
            pin_pos,
            restarted,
        })
    }

    /// Returns when [`Reorderer::pop`] should next be called, absent another
    /// [`Reorderer::push`], or `None` if no packets are held.
    ///
    /// This may be in the past, if a packet is due now.
    pub fn poll_timeout(&self) -> Option<Instant> {
        if let Some(r) = self.ready.front() {
            return Some(r.arrival);
        }
        let front = self.held.front()?;
        if self.front_in_order() || self.held.len() > usize::from(self.options.max_packets) {
            return Some(front.arrival);
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
            let (header, _) = PacketHeader::validate(&raw[..]).unwrap();
            let t = self.t0 + Duration::from_millis(at_ms);
            (self.r.push(&self.buf, header, pos, t, ()), pos)
        }

        /// Pops all due packets, returning their sequence numbers.
        fn pop(&mut self, at_ms: u64) -> Vec<u16> {
            let t = self.t0 + Duration::from_millis(at_ms);
            std::iter::from_fn(|| self.r.pop(t))
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
        let p = f.r.pop(t).unwrap();
        assert_eq!((p.header.sequence_number(), p.restarted), (1004, false));
        let p = f.r.pop(t).unwrap();
        assert_eq!((p.header.sequence_number(), p.restarted), (11, true));
        assert!(f.r.pop(t).is_none());

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

    #[test]
    fn pin_pos() {
        let mut f = Fixture::new(ReorderOptions::default());
        let (_, pos2) = f.push(2, 0);
        let (_, pos1) = f.push(1, 0);
        let (_, pos3) = f.push(3, 0);
        assert!(pos2 < pos1 && pos1 < pos3);
        let t = f.t0 + DELAY;
        let p = f.r.pop(t).unwrap();
        assert_eq!((p.header.sequence_number(), p.pin_pos), (1, pos2));
        let p = f.r.pop(t).unwrap();
        assert_eq!((p.header.sequence_number(), p.pin_pos), (2, pos2));
        let p = f.r.pop(t).unwrap();
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
            let (header, range) = PacketHeader::validate(&raw[..]).unwrap();
            let payload = pos + u64::from(range.start)..pos + u64::from(range.end);
            assert_eq!(r.push(buf, header, pos, t0, payload), Pushed::Held);
        };
        let mut drain = |buf: &MarkBuf, r: &mut Reorderer<std::ops::Range<u64>>, now| {
            while let Some(p) = r.pop(now) {
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
}
