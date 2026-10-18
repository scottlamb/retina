// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [`Reorderer`]: puts received RTP packets back in sequence order.

use std::collections::VecDeque;
use std::time::{Duration, Instant};

use super::PacketHeader;
use crate::buf::{Mark, MarkBuf};

/// Options for a [`Reorderer`].
#[derive(Copy, Clone, Debug)]
pub struct ReorderOptions {
    pub(crate) max_delay: Duration,
    pub(crate) max_packets: u16,
}

impl Default for ReorderOptions {
    fn default() -> Self {
        Self {
            max_delay: Duration::from_millis(50),
            max_packets: 128,
        }
    }
}

impl ReorderOptions {
    /// Sets how long to wait for a missing packet before giving up on it.
    /// Defaults to 50 milliseconds.
    ///
    /// This is the most latency reordering adds, once a stream has started.
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
}

/// A packet returned by [`Reorderer::pop`].
#[derive(Debug)]
#[non_exhaustive]
pub struct Reordered<T> {
    /// The caller's item supplied to [`Reorderer::push`].
    pub item: T,

    /// The packet's header.
    pub header: PacketHeader,

    /// The position to pass to [`crate::buf::PacketRef::with_pin_pos`].
    ///
    /// This is at or before the packet's own position and that of every
    /// packet still held, all of which [`Reorderer::pop`] will return later.
    pub pin_pos: u64,
}

struct Held<T> {
    header: PacketHeader,
    pos: u64,
    arrival: Instant,
    mark: Mark,
    item: T,
}

/// Puts RTP packets from a single stream (one SSRC), such as one received
/// over UDP, back in sequence order.
///
/// This is sans-I/O and works with packets in place within a [`MarkBuf`]. The
/// caller parses each packet's header via [`PacketHeader::validate`], then:
///
/// 1.  advances the buffer's `unparsed()` position past the packet and calls
///     [`Reorderer::push`], which pins the packet's data in the buffer.
/// 2.  calls [`Reorderer::pop`] until it returns `None`, and for each packet,
///     calls [`super::Receiver::rtp`] and builds a
///     [`crate::buf::PacketRef`] using [`Reordered::pin_pos`].
/// 3.  calls `pop` again by [`Reorderer::poll_timeout`], to give up on
///     missing packets.
///
/// Before the first packet is returned, the reorderer waits up to
/// [`ReorderOptions::max_delay`] in case packets with earlier sequence
/// numbers arrive. Afterward, it returns each packet as soon as those before
/// it have been returned or given up on. A packet whose predecessor was given
/// up on, or which arrives after a later packet was returned, is
/// [`Pushed::Late`] and dropped.
///
/// It doesn't check SSRCs; that's left to the [`super::Receiver`].
pub struct Reorderer<T> {
    options: ReorderOptions,

    /// Held packets, sorted by sequence number relative to `next`.
    held: VecDeque<Held<T>>,

    /// The next sequence number to return, once one is known.
    next: Option<u16>,

    /// True once a packet has been returned. Before then, an earlier packet
    /// can move `next` backward.
    started: bool,

    /// The mark of the last packet returned by `pop`, held until the next
    /// call so the caller can build a `PacketRef` to it.
    last: Option<Mark>,
}

impl<T> std::fmt::Debug for Reorderer<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Reorderer")
            .field("options", &self.options)
            .field("next", &self.next)
            .field("started", &self.started)
            .field(
                "held",
                &self
                    .held
                    .iter()
                    .map(|h| h.header.sequence_number())
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl<T> Reorderer<T> {
    pub fn new(options: ReorderOptions) -> Self {
        Self {
            options,
            held: VecDeque::new(),
            next: None,
            started: false,
            last: None,
        }
    }

    /// Returns the number of packets held.
    #[inline]
    pub fn len(&self) -> usize {
        self.held.len()
    }

    /// Returns true if no packets are held.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.held.is_empty()
    }

    /// Offset of `seq` from `next`, which must be known.
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

    /// Returns true if the front packet should be returned at `now`.
    fn front_due(&self, now: Instant) -> bool {
        let Some(front) = self.held.front() else {
            return false;
        };
        (self.started && Some(front.header.sequence_number()) == self.next)
            || self.held.len() > usize::from(self.options.max_packets)
            || self.give_up_at().is_some_and(|t| t <= now)
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
    /// or `pop`, so the caller can build a [`crate::buf::PacketRef`] to it.
    pub fn pop(&mut self, now: Instant) -> Option<Reordered<T>> {
        self.last = None;
        if !self.front_due(now) {
            return None;
        }
        let h = self.held.pop_front().expect("front_due implies non-empty");
        self.next = Some(h.header.sequence_number().wrapping_add(1));
        self.started = true;
        let pin_pos = self.held.iter().map(|h| h.pos).fold(h.pos, u64::min);
        self.last = Some(h.mark);
        Some(Reordered {
            item: h.item,
            header: h.header,
            pin_pos,
        })
    }

    /// Returns when [`Reorderer::pop`] should next be called, absent another
    /// [`Reorderer::push`], or `None` if no packets are held.
    ///
    /// This may be in the past, if a packet is due now.
    pub fn poll_timeout(&self) -> Option<Instant> {
        let front = self.held.front()?;
        if (self.started && Some(front.header.sequence_number()) == self.next)
            || self.held.len() > usize::from(self.options.max_packets)
        {
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
        use crate::buf::PacketRef;
        use crate::codec::{
            Accumulate, FrameFormat, VideoData, VideoDepacketizer, VideoFrameEnd, VideoFrameStart,
            VideoHandler,
        };
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
                let meta = receiver.rtp((), &p.header).unwrap().unwrap();
                let len = u16::try_from(p.item.end - p.item.start).unwrap();
                let pkt = PacketRef::new(meta, buf, p.item.start, len).with_pin_pos(p.pin_pos);
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
