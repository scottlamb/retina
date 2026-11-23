// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [`Receiver`]: receives one RTP session, sorting its packets by source
//! (SSRC), choosing a source to play, and putting its packets in sequence
//! order on one continuous timeline.

// Without the feature, only what the client uses is reachable.
#![cfg_attr(not(feature = "unstable-rtp-receive"), allow(dead_code))]

use std::num::NonZeroU32;
use std::time::{Duration, Instant};

use super::reorder::{self, ReorderOptions};
use super::seq::{MAX_DROPOUT, MAX_MISORDER};
use super::source::Source;
use super::timeline::Output;
use super::{Continuity, PacketHeader, ReceivedPacketMeta, ReceivedPacketRef};
use crate::Timestamp;
use crate::buf::MarkBuf;

/// RTCP packet types for a sender report and a goodbye (RFC 3550 section 12.1).
const PT_SR: u8 = 200;
const PT_BYE: u8 = 203;

/// Without an expected SSRC, how long a lone source's first packet waits for
/// the source to leave probation before the source is selected anyway.
///
/// Probation normally ends with the second packet, within milliseconds, but a
/// sparse stream (such as ONVIF metadata) may send one packet and then nothing
/// for a long time.
const LONE_SOURCE_DELAY: Duration = Duration::from_secs(1);

/// The default bound on how many sources a [`Receiver`] tracks at once, to
/// bound the state spoofed packets can create. A session normally has one
/// source; a few more allow for a stale session's data or another stream
/// sharing the channel.
const MAX_SOURCES: usize = 4;

/// Options for a [`Receiver`].
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct ReceiverOptions {
    pub(crate) reorder: ReorderOptions,
    pub(crate) ssrc: Option<u32>,
    pub(crate) initial_sequence_number: Option<u16>,
    pub(crate) initial_rtptime: Option<u32>,
    pub(crate) max_sources: usize,
}

impl Default for ReceiverOptions {
    fn default() -> Self {
        Self {
            reorder: ReorderOptions::default(),
            ssrc: None,
            initial_sequence_number: None,
            initial_rtptime: None,
            max_sources: MAX_SOURCES,
        }
    }
}

impl ReceiverOptions {
    /// Sets how to put each source's packets back in sequence order. Defaults
    /// to [`ReorderOptions::default`].
    ///
    /// A [`ReorderOptions::max_delay`] of zero suits TCP, which doesn't
    /// reorder: each packet is returned as soon as it arrives, and late ones
    /// are dropped.
    #[inline]
    pub fn reorder(self, reorder: ReorderOptions) -> Self {
        Self { reorder, ..self }
    }

    /// Sets the expected SSRC, e.g. (for a client receiving via `PLAY`) from
    /// the `SETUP` response's `Transport` header.
    ///
    /// The receiver plays this source, and no other. Without it, the
    /// receiver chooses one, as described under [`Receiver`].
    #[inline]
    pub fn ssrc(self, ssrc: u32) -> Self {
        Self {
            ssrc: Some(ssrc),
            ..self
        }
    }

    /// Sets the expected first sequence number, e.g. (for a client receiving
    /// via `PLAY`) from the `PLAY` response's `RTP-Info` header.
    ///
    /// By default, the receiver waits up to [`ReorderOptions::max_delay`]
    /// before returning the first packet, in case packets with earlier
    /// sequence numbers arrive. With a known first sequence number, it returns
    /// that packet as soon as it arrives, and reports a gap before the first
    /// packet as loss. It applies only to a source whose first packet is
    /// within the reorder window of it.
    #[inline]
    pub fn initial_sequence_number(self, seq: u16) -> Self {
        Self {
            initial_sequence_number: Some(seq),
            ..self
        }
    }

    /// Sets the RTP timestamp which is time 0 in normal play time, e.g. (for a
    /// client receiving via `PLAY`) from the `PLAY` response's `RTP-Info`
    /// header. By default, this is the selected source's first packet's (or
    /// sender report's) timestamp.
    #[inline]
    pub fn initial_rtptime(self, rtptime: u32) -> Self {
        Self {
            initial_rtptime: Some(rtptime),
            ..self
        }
    }

    /// Sets the most sources to track at once, for tests. Defaults to
    /// [`MAX_SOURCES`]; at least 1.
    #[cfg(test)]
    fn max_sources(self, max_sources: usize) -> Self {
        Self {
            max_sources: max_sources.max(1),
            ..self
        }
    }
}

/// The outcome of [`Receiver::push`].
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Pushed {
    /// The packet is held until [`Receiver::pop`] returns it.
    Held,

    /// The packet was discarded as a duplicate of one held.
    Duplicate,

    /// The packet was discarded because it arrived after the receiver
    /// returned a later packet: it was too late or a duplicate of one
    /// returned.
    Late,

    /// The packet was discarded because its sequence number jumped too far
    /// from the others', as described in [RFC 3550 appendix
    /// A.1](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.1). If
    /// the next packet follows it, the sender is assumed to have restarted,
    /// and the next packet returned is a [`Continuity::Discontinuity`].
    Stray,

    /// The packet is from a source other than the selected one. It's tracked
    /// for statistics but won't be returned.
    Unselected {
        /// True for the first packet reported as unselected from this
        /// source, so the caller can log once per source.
        first: bool,
    },

    /// The packet was discarded because its payload type isn't one of the
    /// stream's, and it isn't from the selected source.
    Filtered,

    /// As [`Pushed::Filtered`], and the packet looks like RTCP read as RTP: it
    /// has the marker bit and a payload type of 72–76, as an RTCP packet type
    /// of 200–204 would.
    FilteredRtcp,
}

/// A packet returned by [`Receiver::pop`].
#[derive(Debug)]
#[non_exhaustive]
pub struct Received<T> {
    /// The caller's item supplied to [`Receiver::push`].
    pub item: T,

    /// The packet's header.
    pub header: PacketHeader,

    /// The packet's timestamp on the stream's output timeline.
    pub timestamp: Timestamp,

    /// How this packet relates to the previous one returned.
    pub continuity: Continuity,

    /// The position a depacketizer pins to retain this packet's data and that
    /// of every packet returned after it.
    pin_pos: u64,
}

impl<T> Received<T> {
    /// Returns the packet's metadata, with the caller's context `ctx`.
    #[inline]
    pub fn meta<Ctx>(&self, ctx: Ctx) -> ReceivedPacketMeta<Ctx> {
        ReceivedPacketMeta::new(
            ctx,
            self.timestamp,
            self.header.payload_type(),
            self.header.sequence_number(),
            self.header.ssrc(),
            self.header.mark(),
            self.continuity,
        )
    }

    /// Builds the packet for a depacketizer, given its payload at stream
    /// positions `[payload_pos, payload_pos + payload_len)` in `buf`, the
    /// buffer passed to [`Receiver::push`].
    ///
    /// The packet's data stays pinned until the next call to
    /// [`Receiver::push`] or [`Receiver::pop`]; a depacketizer pins it for
    /// longer as needed.
    ///
    /// # Panics
    ///
    /// As [`ReceivedPacketRef::new`].
    pub fn packet_ref<'b, Ctx>(
        &self,
        ctx: Ctx,
        buf: &'b MarkBuf,
        payload_pos: u64,
        payload_len: u16,
    ) -> ReceivedPacketRef<'b, Ctx> {
        ReceivedPacketRef::new(self.meta(ctx), buf, payload_pos, payload_len)
            .with_pin_pos(self.pin_pos)
    }

    /// The position to pass to [`ReceivedPacketRef::with_pin_pos`].
    #[inline]
    pub(crate) fn pin_pos(&self) -> u64 {
        self.pin_pos
    }
}

/// The outcome of [`Receiver::rtcp`].
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct RtcpOutcome {
    /// The RTP timestamp of the sender report beginning the compound packet,
    /// placed on the output timeline, if it's from the selected source (or,
    /// before one is selected, the expected one; see
    /// [`ReceiverOptions::ssrc`]).
    pub rtp_timestamp: Option<Timestamp>,

    /// Set if the compound packet begins with a sender report from a source
    /// other than the selected (or expected) one.
    pub other_source: Option<OtherSource>,
}

/// A sender report from a source other than the selected one, as in
/// [`RtcpOutcome::other_source`].
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct OtherSource {
    /// The sender report's SSRC.
    pub ssrc: u32,

    /// The selected (or expected) source's SSRC.
    pub expected: u32,
}

/// Reception statistics for one source, as for a receiver report block
/// ([RFC 3550 section
/// 6.4.1](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.1)).
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct ReceptionReport {
    /// The source's SSRC.
    pub ssrc: u32,

    /// The fraction of packets lost since the previous report, in 256ths.
    pub fraction_lost: u8,

    /// The cumulative number of packets lost, within the 24-bit signed range.
    pub cumulative_lost: i32,

    /// The extended highest sequence number received.
    pub extended_highest_seq: u32,

    /// The interarrival jitter, in RTP timestamp units.
    pub jitter: u32,

    /// The middle 32 bits of the last sender report's NTP timestamp, or 0.
    pub lsr: u32,

    /// The delay since the last sender report, in units of 1/65536 seconds,
    /// or 0.
    pub dlsr: u32,
}

/// Counts of packets a [`Receiver`] discarded or gave up on, and of other
/// events.
///
/// `late` through `lost` are for the selected source only.
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
pub struct ReceiverCounters {
    /// Packets discarded as [`Pushed::Late`].
    pub late: u64,

    /// Packets discarded as [`Pushed::Duplicate`].
    pub duplicates: u64,

    /// Packets discarded as [`Pushed::Stray`].
    pub strays: u64,

    /// Times the sender restarted its sequence numbers.
    pub restarts: u64,

    /// Missing packets given up on.
    pub lost: u64,

    /// Packets discarded as [`Pushed::Filtered`].
    pub filtered: u64,

    /// Packets discarded as [`Pushed::FilteredRtcp`].
    pub filtered_rtcp: u64,

    /// Packets discarded because they're from a source other than the
    /// selected one.
    pub unselected: u64,

    /// Sources seen, including those since forgotten.
    pub sources: u64,

    /// RTCP BYE packets received.
    pub byes: u64,

    /// Packets discarded because their timestamps couldn't be represented,
    /// which is only possible with a hostile sender.
    pub timestamp_overflows: u64,
}

/// Receives one RTP session, such as an RTSP stream: an interleaved channel
/// pair or a UDP port pair. The counterpart of [`super::Sender`].
///
/// An RTP session can carry several sources, each identified by an SSRC, with
/// its own sequence numbers and timestamps ([RFC 3550 section
/// 8](https://datatracker.ietf.org/doc/html/rfc3550#section-8)). In RTSP,
/// though, a stream is one source's packets ([RFC 2326 section
/// 1.3](https://datatracker.ietf.org/doc/html/rfc2326#section-1.3)), which a
/// unicast server may name in the `SETUP` response's `Transport` header
/// ([section
/// 12.39](https://datatracker.ietf.org/doc/html/rfc2326#section-12.39)).
/// Packets from other sources come from broken servers: stale data from an
/// earlier session (old live555 versions over TCP), or another stream's
/// packets on this stream's channel. Some servers also send packets whose
/// payload type disagrees with the SDP. The receiver works around these.
///
/// The receiver plays one source, returning its packets in sequence order
/// with timestamps on one continuous output timeline, and drops other
/// packets. If [`ReceiverOptions::ssrc`] is set, it plays that source and no
/// other. Receiving never fails: each pushed packet is eventually returned by
/// [`Receiver::pop`] or dropped. [`Receiver::push`]'s result says if a packet
/// is dropped on arrival, the [`Continuity`] of each returned packet says if
/// sequence numbers were skipped before it, and [`Receiver::counters`] counts
/// drops. The receiver's memory is bounded however hostile its input.
///
/// This is sans-I/O and works with packets in place within a [`MarkBuf`]. The
/// caller parses each packet's header via [`PacketHeader::validate`], then:
///
/// 1.  advances the buffer's `unparsed()` position past the packet and calls
///     [`Receiver::push`], which pins the packet's data in the buffer.
/// 2.  calls [`Receiver::pop`] until it returns `None`, and for each packet,
///     builds a [`ReceivedPacketRef`] via [`Received::packet_ref`] for a
///     depacketizer.
/// 3.  calls `pop` again by [`Receiver::poll_timeout`], to give up on missing
///     packets.
///
/// It also takes RTCP compound packets, via [`Receiver::rtcp`].
///
/// `T` is the caller's item for each packet, returned with it by `pop`; it
/// might hold the packet's context and payload range.
///
/// ## Current approach
///
/// The details below describe the current implementation. They aren't
/// promised: they may change in any release, as better heuristics are found.
///
/// 1.  The receiver drops packets whose payload type isn't one of the
///     stream's, such as another stream's packets sent on this stream's
///     channel. A server whose RTP payload type disagrees with its SDP is
///     misconfigured; all of its packets are dropped.
/// 2.  It sorts the rest by SSRC into a table of a few sources, each with its
///     own reorder buffer, sequence number statistics, jitter, timestamp
///     extension, and sender report. When the table is full, a new source
///     replaces the least recently heard one other than the selected one.
/// 3.  It selects the source to play: the expected one if
///     [`ReceiverOptions::ssrc`] is set; otherwise the first to send two
///     packets in sequence, as in [RFC 3550 appendix
///     A.1](https://datatracker.ietf.org/doc/html/rfc3550#appendix-A.1), or
///     the only source heard, once its first packet has waited a second.
///     Until then, packets are held. Once selected, a source stays selected.
/// 4.  It maps the selected source's timestamps onto the output timeline.
pub struct Receiver<T> {
    payload_types: PayloadTypeSet,
    clock_rate: NonZeroU32,
    options: ReceiverOptions,
    sources: Vec<Source<T>>,
    selected: Option<u32>,
    output: Output,
    counters: ReceiverCounters,
}

impl<T> std::fmt::Debug for Receiver<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Receiver")
            .field("payload_types", &self.payload_types)
            .field("expected_ssrc", &self.options.ssrc.map(Hex))
            .field("selected_ssrc", &self.selected.map(Hex))
            .field("sources", &self.sources)
            .field("counters", &self.counters)
            .finish()
    }
}

/// Formats an SSRC as hex.
struct Hex(u32);

impl std::fmt::Debug for Hex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:08x}", self.0)
    }
}

/// Returns true if `header` looks like an RTCP packet read as RTP: an RTCP
/// packet type of 200–204 is a marker bit and a payload type of 72–76.
fn is_rtcp(header: &PacketHeader) -> bool {
    header.mark() && (72..=76).contains(&header.payload_type())
}

/// A set of RTP payload types, such as those on a stream's SDP `m=` line.
///
/// Collect one from payload types via [`FromIterator`], e.g.
/// `[96, 97].into_iter().collect()`.
#[derive(Copy, Clone, Default, PartialEq, Eq, Hash)]
pub struct PayloadTypeSet(u128);

impl PayloadTypeSet {
    /// Returns an empty set.
    #[inline]
    pub const fn new() -> Self {
        Self(0)
    }

    /// Adds `payload_type`, returning true if it wasn't already present.
    ///
    /// # Panics
    ///
    /// Panics if `payload_type` isn't a valid RTP payload type, i.e. is 128
    /// or more. Those from [`PacketHeader::payload_type`] always are.
    #[inline]
    pub fn insert(&mut self, payload_type: u8) -> bool {
        assert!(
            payload_type < 128,
            "invalid RTP payload type {payload_type}"
        );
        let bit = 1 << payload_type;
        let new = self.0 & bit == 0;
        self.0 |= bit;
        new
    }

    /// Returns true if `payload_type` is present.
    #[inline]
    pub fn contains(&self, payload_type: u8) -> bool {
        payload_type < 128 && self.0 & (1 << payload_type) != 0
    }

    /// Returns true if the set is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0 == 0
    }

    /// Iterates through the payload types, in ascending order.
    pub fn iter(&self) -> impl Iterator<Item = u8> + '_ {
        (0..128u8).filter(|&pt| self.contains(pt))
    }
}

impl FromIterator<u8> for PayloadTypeSet {
    /// Collects payload types; panics as [`PayloadTypeSet::insert`] does.
    fn from_iter<I: IntoIterator<Item = u8>>(iter: I) -> Self {
        let mut set = Self::new();
        for pt in iter {
            set.insert(pt);
        }
        set
    }
}

impl std::fmt::Debug for PayloadTypeSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<T> Receiver<T> {
    /// Creates a receiver for a stream with the given payload types (from its
    /// SDP `m=` line) and clock rate.
    pub fn new(
        payload_types: PayloadTypeSet,
        clock_rate: NonZeroU32,
        options: ReceiverOptions,
    ) -> Self {
        Self {
            payload_types,
            clock_rate,
            output: Output::new(clock_rate, options.initial_rtptime),
            options,
            sources: Vec::new(),
            selected: None,
            counters: ReceiverCounters::default(),
        }
    }

    /// Returns the selected source's SSRC, if any.
    #[inline]
    pub fn selected_ssrc(&self) -> Option<u32> {
        self.selected
    }

    /// Returns the SSRC this receiver plays: the selected one or, before one
    /// is selected, the expected one.
    #[inline]
    fn reference_ssrc(&self) -> Option<u32> {
        self.selected.or(self.options.ssrc)
    }

    /// Returns counts of packets discarded or given up on so far.
    pub fn counters(&self) -> ReceiverCounters {
        let mut c = self.counters;
        if let Some(s) = self.selected.and_then(|ssrc| self.source(ssrc)) {
            let r = s.reorder_counters();
            c.late = r.late;
            c.duplicates = r.duplicates;
            c.strays = r.strays;
            c.restarts = r.restarts;
            c.lost = r.skipped;
        }
        c
    }

    fn source(&self, ssrc: u32) -> Option<&Source<T>> {
        self.sources.iter().find(|s| s.ssrc == ssrc)
    }

    fn source_mut(&mut self, ssrc: u32) -> Option<&mut Source<T>> {
        self.sources.iter_mut().find(|s| s.ssrc == ssrc)
    }

    /// Returns true if `ssrc` may yet be selected.
    fn is_candidate(&self, ssrc: u32) -> bool {
        self.selected.is_none() && self.options.ssrc.is_none_or(|e| e == ssrc)
    }

    /// Returns the index of the source for `ssrc`, creating it for a packet
    /// with sequence number `seq` if needed, or `None` if the table is full of
    /// sources which can't be forgotten.
    fn find_or_create(&mut self, ssrc: u32, seq: Option<u16>, now: Instant) -> Option<usize> {
        if let Some(i) = self.sources.iter().position(|s| s.ssrc == ssrc) {
            return Some(i);
        }
        if self.sources.len() >= self.options.max_sources {
            let (i, _) = self
                .sources
                .iter()
                .enumerate()
                .filter(|(_, s)| Some(s.ssrc) != self.selected)
                .min_by_key(|(_, s)| s.last_heard)?;
            let s = self.sources.swap_remove(i);
            self.counters.unselected += crate::to_u64(s.len());
        }
        let mut initial_sequence_number = None;
        if self.is_candidate(ssrc)
            && let (Some(initial), Some(seq)) = (self.options.initial_sequence_number, seq)
        {
            // Apply the initial sequence number only if it plausibly refers to
            // this source, so a stray source doesn't start with every packet
            // late.
            let d = seq.wrapping_sub(initial);
            if d < MAX_DROPOUT || d.wrapping_neg() <= MAX_MISORDER {
                initial_sequence_number = Some(initial);
            }
        }
        self.sources.push(Source::new(
            ssrc,
            self.options.reorder,
            initial_sequence_number,
            now,
        ));
        self.counters.sources += 1;
        if self.selected.is_none() && self.options.ssrc == Some(ssrc) {
            self.selected = Some(ssrc);
        }
        Some(self.sources.len() - 1)
    }

    /// Adds a validated RTP packet received at `now`, whose data starts at
    /// `pos` in `buf`. `item` comes back with it from [`Receiver::pop`].
    ///
    /// Packets should be pushed in the order they were received.
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
        let ssrc = header.ssrc();
        if !self.payload_types.contains(header.payload_type()) {
            return if is_rtcp(&header) {
                self.counters.filtered_rtcp += 1;
                Pushed::FilteredRtcp
            } else {
                self.counters.filtered += 1;
                Pushed::Filtered
            };
        }
        let candidate = self.is_candidate(ssrc);
        let Some(i) = self.find_or_create(ssrc, Some(header.sequence_number()), now) else {
            self.counters.unselected += 1;
            return Pushed::Unselected { first: false };
        };
        let clock_rate = self.clock_rate;
        let s = &mut self.sources[i];
        let pushed = s.push(buf, header, pos, now, clock_rate, item);
        if self.selected.is_none() && candidate && s.is_valid() {
            self.selected = Some(ssrc);
        }
        if candidate || self.selected == Some(ssrc) {
            return match pushed {
                reorder::Pushed::Held => Pushed::Held,
                reorder::Pushed::Duplicate => Pushed::Duplicate,
                reorder::Pushed::Late => Pushed::Late,
                reorder::Pushed::Stray => Pushed::Stray,
            };
        }
        let s = &mut self.sources[i];
        let first = !std::mem::replace(&mut s.reported_unselected, true);
        Pushed::Unselected { first }
    }

    /// Returns the next packet of the selected source that's due: in sequence,
    /// or given up waiting for its predecessors.
    ///
    /// A packet is due when it's next in sequence, or when giving up on any
    /// missing packets before it, because a held packet has waited
    /// [`ReorderOptions::max_delay`] or more than
    /// [`ReorderOptions::max_packets`] are held. Other sources' due packets
    /// are dropped.
    ///
    /// `buf` must be the buffer passed to [`Receiver::push`]. The returned
    /// packet's data stays pinned until the next call to `push` or `pop`.
    pub fn pop(&mut self, buf: &MarkBuf, now: Instant) -> Option<Received<T>> {
        if self.selected.is_none()
            && let Some((ssrc, t)) = self.lone_candidate()
            && t <= now
        {
            self.selected = Some(ssrc);
        }
        let selected = self.selected;
        let none_selected = selected.is_none();
        for s in &mut self.sources {
            if Some(s.ssrc) == selected {
                continue;
            }
            if none_selected && self.options.ssrc.is_none_or(|e| e == s.ssrc) {
                // A candidate: hold its packets until a source is selected,
                // up to its limit.
                let mut overflows = 0;
                while let Some(p) = s.pop(buf, None, &mut overflows) {
                    s.note_dropped(&p.reordered);
                    self.counters.unselected += 1;
                }
                self.counters.timestamp_overflows += overflows;
            } else {
                self.counters.unselected += s.drain(buf, now);
            }
        }
        let ssrc = selected?;
        let s = self
            .sources
            .iter_mut()
            .find(|s| s.ssrc == ssrc)
            .expect("selected source is in the table");
        loop {
            let p = s.pop(buf, Some(now), &mut self.counters.timestamp_overflows)?;
            let rtp_timestamp = p.reordered.header.timestamp();
            let Some(timestamp) = self.output.map(p.timestamp, rtp_timestamp) else {
                self.counters.timestamp_overflows += 1;
                s.note_dropped(&p.reordered);
                continue;
            };
            return Some(Received {
                item: p.reordered.item,
                header: p.reordered.header,
                timestamp,
                continuity: p.continuity,
                pin_pos: p.reordered.pin_pos,
            });
        }
    }

    /// Before a source is selected, returns the only candidate source holding
    /// packets, if there's exactly one, and when to select it anyway.
    fn lone_candidate(&self) -> Option<(u32, Instant)> {
        let mut holding = self
            .sources
            .iter()
            .filter(|s| self.is_candidate(s.ssrc))
            .filter_map(|s| Some((s.ssrc, s.earliest_arrival()? + LONE_SOURCE_DELAY)));
        let first = holding.next()?;
        holding.next().is_none().then_some(first)
    }

    /// Returns when [`Receiver::pop`] should next be called, absent another
    /// [`Receiver::push`], or `None` if no packets are waiting on time.
    ///
    /// This may be in the past, if a packet is due now.
    pub fn poll_timeout(&self) -> Option<Instant> {
        let lone = self
            .selected
            .is_none()
            .then(|| self.lone_candidate())
            .flatten()
            .map(|(_, t)| t);
        self.sources
            .iter()
            .filter(|s| self.selected.is_some() || !self.is_candidate(s.ssrc))
            .filter_map(Source::poll_timeout)
            .chain(lone)
            .min()
    }

    /// Processes an RTCP compound packet received at `now`.
    ///
    /// Routes each sender report to its source, and ends the sources listed
    /// in each goodbye (BYE). A sender report from an unknown source doesn't
    /// create one, unless it's the expected one.
    ///
    /// Errors if the compound packet is malformed, without changing state.
    pub fn rtcp(&mut self, compound: &[u8], now: Instant) -> Result<RtcpOutcome, String> {
        crate::rtcp::ReceivedCompoundPacket::validate(compound)?;
        let mut outcome = RtcpOutcome {
            rtp_timestamp: None,
            other_source: None,
        };
        let mut rest = compound;
        let mut first = true;
        while !rest.is_empty() {
            let (pkt, r) = crate::rtcp::PacketRef::parse(rest).expect("validated above");
            rest = r;
            let is_first = std::mem::take(&mut first);
            match pkt.payload_type() {
                PT_SR => {
                    // As before, tolerate a malformed sender report.
                    let Ok(Some(sr)) = pkt.as_sender_report() else {
                        continue;
                    };
                    let ssrc = sr.ssrc();
                    let reference = self.reference_ssrc();
                    if is_first
                        && let Some(expected) = reference
                        && expected != ssrc
                    {
                        outcome.other_source = Some(OtherSource { ssrc, expected });
                    }
                    let Some(i) = (if self.options.ssrc == Some(ssrc) {
                        self.find_or_create(ssrc, None, now)
                    } else {
                        self.sources.iter().position(|s| s.ssrc == ssrc)
                    }) else {
                        continue;
                    };
                    let rtp_timestamp = sr.rtp_timestamp();
                    let ext = self.sources[i].sender_report(sr.ntp_timestamp(), rtp_timestamp, now);
                    if self.selected != Some(ssrc) {
                        continue;
                    }
                    let ts = ext.and_then(|ext| self.output.map(ext, rtp_timestamp));
                    if is_first {
                        outcome.rtp_timestamp = ts;
                    }
                }
                PT_BYE => {
                    self.counters.byes += 1;
                    let raw = pkt.raw();
                    let n = usize::from(pkt.count());
                    for chunk in raw[4..].as_chunks::<4>().0.iter().take(n) {
                        let ssrc = u32::from_be_bytes(*chunk);
                        if self.selected == Some(ssrc) {
                            if let Some(s) = self.source_mut(ssrc) {
                                s.bye = true;
                            }
                        } else if let Some(i) = self.sources.iter().position(|s| s.ssrc == ssrc) {
                            let s = self.sources.swap_remove(i);
                            self.counters.unselected += crate::to_u64(s.len());
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(outcome)
    }

    /// Returns reception statistics for the selected source as of `now`, for
    /// a receiver report block, and starts a new reporting interval. Returns
    /// `None` if no source is selected or no packet has arrived from it since
    /// the last report.
    pub fn reception_report(&mut self, now: Instant) -> Option<ReceptionReport> {
        let ssrc = self.selected?;
        self.source_mut(ssrc)?.reception_report(now)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rtp::build_raw_rtp;

    const RATE: NonZeroU32 = NonZeroU32::new(90_000).unwrap();

    struct Fixture {
        buf: MarkBuf,
        r: Receiver<()>,
        t0: Instant,
    }

    impl Fixture {
        fn new(payload_types: &[u8], options: ReceiverOptions) -> Self {
            crate::testutil::init_logging();
            Self {
                buf: MarkBuf::new(1 << 16),
                r: Receiver::new(payload_types.iter().copied().collect(), RATE, options),
                t0: Instant::now(),
            }
        }

        fn at(&self, ms: u64) -> Instant {
            self.t0 + Duration::from_millis(ms)
        }

        /// Pushes a packet with timestamp `seq * 3000` at `ms`.
        fn push(&mut self, seq: u16, payload_type: u8, ssrc: u32, ms: u64) -> Pushed {
            self.push_raw(seq, u32::from(seq) * 3000, payload_type, ssrc, true, ms)
        }

        fn push_raw(
            &mut self,
            seq: u16,
            ts: u32,
            payload_type: u8,
            ssrc: u32,
            mark: bool,
            ms: u64,
        ) -> Pushed {
            let raw = build_raw_rtp(seq, ts, payload_type, ssrc, mark, *b"x").unwrap();
            let pos = self.buf.end();
            self.buf.extend(&raw);
            self.buf.advance_unparsed(self.buf.end());
            let header = PacketHeader::validate(&raw[..]).unwrap().0;
            let t = self.at(ms);
            self.r.push(&self.buf, header, pos, t, ())
        }

        /// Pops all due packets, returning `(ssrc, seq, elapsed, continuity)`.
        fn pop(&mut self, ms: u64) -> Vec<(u32, u16, i64, Continuity)> {
            let t = self.at(ms);
            std::iter::from_fn(|| self.r.pop(&self.buf, t))
                .map(|p| {
                    (
                        p.header.ssrc(),
                        p.header.sequence_number(),
                        p.timestamp.elapsed(),
                        p.continuity,
                    )
                })
                .collect()
        }

        fn seqs(&mut self, ms: u64) -> Vec<u16> {
            self.pop(ms).into_iter().map(|p| p.1).collect()
        }

        fn rtcp(&mut self, data: &[u8], ms: u64) -> RtcpOutcome {
            let t = self.at(ms);
            self.r.rtcp(data, t).unwrap()
        }
    }

    fn tcp() -> ReceiverOptions {
        ReceiverOptions::default().reorder(ReorderOptions::default().max_delay(Duration::ZERO))
    }

    /// RFC 3550 section 6.4.1: a sender report from `ssrc` at
    /// `rtp_timestamp`, with no report blocks.
    fn sender_report(ssrc: u32, rtp_timestamp: u32) -> Vec<u8> {
        let mut data = b"\x80\xc8\x00\x06".to_vec();
        data.extend_from_slice(&ssrc.to_be_bytes());
        data.extend_from_slice(&[0xe4, 0x36, 0x2f, 0x99, 0xcc, 0xcc, 0xcc, 0xcc]);
        data.extend_from_slice(&rtp_timestamp.to_be_bytes());
        data.extend_from_slice(&[0; 8]); // packet and octet counts.
        data
    }

    /// RFC 3550 section 6.6: a goodbye from `ssrcs`.
    fn goodbye(ssrcs: &[u32]) -> Vec<u8> {
        let mut data = vec![0x80 | u8::try_from(ssrcs.len()).unwrap(), PT_BYE, 0, 0];
        data[3] = u8::try_from(ssrcs.len()).unwrap();
        for s in ssrcs {
            data.extend_from_slice(&s.to_be_bytes());
        }
        data
    }

    /// Without an expected SSRC, the first source to send two packets in
    /// sequence is selected. Its first packet is held meanwhile, even on TCP.
    /// A single misrouted packet arriving first (as in #119) isn't selected.
    #[test]
    fn selects_first_valid_source() {
        let mut f = Fixture::new(&[96], tcp());
        assert_eq!(f.push(30_000, 96, 0x4832_3634, 0), Pushed::Held);
        assert_eq!(f.push(10, 96, 0x110, 0), Pushed::Held);
        assert_eq!(f.pop(0), []);
        assert_eq!(f.r.poll_timeout(), None); // two candidates.
        assert_eq!(f.push(11, 96, 0x110, 0), Pushed::Held);
        assert_eq!(f.r.selected_ssrc(), Some(0x110));
        assert_eq!(
            f.pop(0),
            [
                (0x110, 10, 0, Continuity::Contiguous),
                (0x110, 11, 3000, Continuity::Contiguous),
            ]
        );

        // The other source's packets are dropped, without disrupting this one.
        assert_eq!(
            f.push(30_001, 96, 0x4832_3634, 0),
            Pushed::Unselected { first: true }
        );
        assert_eq!(
            f.push(30_002, 96, 0x4832_3634, 0),
            Pushed::Unselected { first: false }
        );
        assert_eq!(f.push(12, 96, 0x110, 0), Pushed::Held);
        assert_eq!(f.seqs(0), [12]);
        let c = f.r.counters();
        assert_eq!((c.unselected, c.sources, c.strays, c.lost), (3, 2, 0, 0));
    }

    /// Without an expected SSRC, a lone source which sends one packet, as a
    /// sparse metadata stream might, is selected after a second.
    #[test]
    fn selects_lone_source() {
        let mut f = Fixture::new(&[96], tcp());
        assert_eq!(f.push(10, 96, 0x110, 0), Pushed::Held);
        assert_eq!(f.seqs(999), [0u16; 0]);
        assert_eq!(f.r.poll_timeout(), Some(f.at(1000)));
        assert_eq!(f.seqs(1000), [10]);
        assert_eq!(f.r.selected_ssrc(), Some(0x110));
    }

    /// With an expected SSRC (e.g. from `SETUP`), it's selected on its first
    /// packet, and another source's packets of the stream's payload type, as
    /// from a stale live555 session, are dropped without disrupting the
    /// reorder buffer (R4) or erroring.
    #[test]
    fn expected_ssrc() {
        let mut f = Fixture::new(&[96], tcp().ssrc(0x110));
        assert_eq!(f.push(1, 96, 0x110, 0), Pushed::Held);
        assert_eq!(f.seqs(0), [1]);
        for seq in [500, 501, 502] {
            assert!(matches!(
                f.push(seq, 96, 0x999, 0),
                Pushed::Unselected { .. }
            ));
            assert_eq!(f.seqs(0), []);
        }
        assert_eq!(f.push(2, 96, 0x110, 0), Pushed::Held);
        assert_eq!(f.pop(0), [(0x110, 2, 3000, Continuity::Contiguous)]);
        let c = f.r.counters();
        assert_eq!((c.strays, c.restarts, c.unselected), (0, 0, 3));
    }

    /// Checks skipping another stream's packets on this stream's channel, as
    /// a Rubetek door intercom sends them: its H.264 video (pt 96, ssrc 0x110)
    /// is set up alone, yet its PCMA audio (pt 8, ssrc 0x111) and the audio's
    /// RTCP sender reports (pt 72 when read as RTP) come on the same channel.
    /// They're skipped even before the video's first packet, and never taken
    /// as the stream's source. A packet with the stream's payload type and
    /// another SSRC is from another source, and isn't returned.
    #[test]
    fn other_stream_on_the_channel() {
        // The SETUP response's `ssrc=0x110` isn't understood, so the SSRC
        // isn't known in advance.
        let mut f = Fixture::new(&[96], tcp());
        assert_eq!(f.push(23161, 8, 0x111, 0), Pushed::Filtered);
        assert_eq!(
            f.push_raw(0x1c, 0, 72, 0xec8e_2b37, true, 0),
            Pushed::FilteredRtcp
        );
        assert_eq!(f.push(1, 96, 0x110, 0), Pushed::Held);
        assert_eq!(f.push(23162, 8, 0x111, 0), Pushed::Filtered);
        assert_eq!(f.push(2, 96, 0x110, 0), Pushed::Held);
        assert_eq!(f.seqs(0), [1, 2]);
        assert_eq!(f.push(3, 96, 0x112, 0), Pushed::Unselected { first: true });
        assert_eq!(f.seqs(0), []);
        let c = f.r.counters();
        assert_eq!((c.filtered, c.filtered_rtcp, c.unselected), (2, 1, 1));
    }

    /// The payload type filter uses all of the stream's formats.
    #[test]
    fn payload_types() {
        let mut f = Fixture::new(&[96, 97], tcp().ssrc(1));
        assert_eq!(f.push(1, 97, 1, 0), Pushed::Held);
        assert_eq!(f.push(2, 96, 1, 0), Pushed::Held);
        assert_eq!(f.seqs(0), [1, 2]);
    }

    #[test]
    #[should_panic(expected = "invalid RTP payload type 128")]
    fn invalid_payload_type() {
        let _: PayloadTypeSet = [96, 128].into_iter().collect();
    }

    #[test]
    fn payload_type_set() {
        let mut s: PayloadTypeSet = [97, 0, 127, 97].into_iter().collect();
        assert_eq!(s.iter().collect::<Vec<_>>(), [0, 97, 127]);
        assert!(s.contains(127) && !s.contains(96) && !s.contains(200));
        assert!(s.insert(96));
        assert!(!s.insert(96));
        assert_eq!(format!("{s:?}"), "{0, 96, 97, 127}");
        assert!(PayloadTypeSet::new().is_empty());
    }

    /// The payload type filter applies even to the expected SSRC.
    #[test]
    fn known_ssrc_payload_type_filtered() {
        let mut f = Fixture::new(&[96], tcp().ssrc(1));
        assert_eq!(f.push(1, 98, 1, 0), Pushed::Filtered);
        assert_eq!(f.push(2, 96, 1, 0), Pushed::Held);
        assert_eq!(f.seqs(0), [2]);
    }

    /// Checks skipping Geovision's extra payload type 50 packets. On a
    /// GV-EBD4701 running V1.02_2021_04_08, these seem to appear after every
    /// IDR frame, with the same sequence number as the final packet in that
    /// frame. They're from the stream's own source, which has sent packets of
    /// the stream's payload type, so the filter drops them.
    #[test]
    fn geovision_pt50_packet() {
        let mut f = Fixture::new(&[105], tcp().ssrc(0xd25614e));
        assert_eq!(f.push(0x1234, 105, 0xd25614e, 0), Pushed::Held);
        assert_eq!(f.push(0x1234, 50, 0xd25614e, 0), Pushed::Filtered);
        assert_eq!(f.seqs(0), [0x1234]);
        let c = f.r.counters();
        assert_eq!((c.late, c.duplicates, c.filtered), (0, 0, 1));
    }

    /// Sequence number loss, late packets, and restarts within the selected
    /// source come through as before.
    #[test]
    fn late_and_restart() {
        let mut f = Fixture::new(&[96], tcp().ssrc(1));
        let mut got = Vec::new();
        for (seq, pushed) in [
            (1000, Pushed::Held),
            (1001, Pushed::Held),
            (1003, Pushed::Held),
            (1002, Pushed::Late),
            (10, Pushed::Stray),
            (11, Pushed::Held),
        ] {
            assert_eq!(f.push(seq, 96, 1, 0), pushed, "{seq}");
            got.extend(f.pop(0).into_iter().map(|p| (p.1, p.3)));
        }
        assert_eq!(
            got,
            [
                (1000, Continuity::Contiguous),
                (1001, Continuity::Contiguous),
                (1003, Continuity::from_loss(1)),
                (11, Continuity::Discontinuity),
            ]
        );
        let c = f.r.counters();
        assert_eq!((c.late, c.strays, c.restarts, c.lost), (1, 1, 1, 1));
    }

    #[test]
    fn initial_expectations() {
        let opts = tcp()
            .ssrc(1)
            .initial_sequence_number(5)
            .initial_rtptime(100);
        let mut f = Fixture::new(&[96], opts);
        f.push_raw(7, 190, 96, 1, true, 0);
        assert_eq!(f.pop(0), [(1, 7, 90, Continuity::from_loss(2))]);

        // A wrapping start.
        let mut f = Fixture::new(&[96], tcp().ssrc(1).initial_rtptime(0xffff_fff0));
        f.push_raw(7, 0x10, 96, 1, true, 0);
        assert_eq!(f.pop(0), [(1, 7, 0x20, Continuity::Contiguous)]);

        // An initial sequence number far from the source's is ignored, so its
        // packets aren't all late.
        let mut f = Fixture::new(&[96], tcp().ssrc(1).initial_sequence_number(5));
        assert_eq!(f.push(20_000, 96, 1, 0), Pushed::Held);
        assert_eq!(f.seqs(0), [20_000]);
    }

    /// A sender report from another source isn't placed on the timeline, so
    /// it can't set the start, and doesn't create a source.
    #[test]
    fn stray_sender_report() {
        let mut f = Fixture::new(&[96], tcp().ssrc(0x110));
        let o = f.rtcp(&sender_report(0x111, 1_000_000), 0);
        assert_eq!(
            o.other_source,
            Some(OtherSource {
                ssrc: 0x111,
                expected: 0x110
            })
        );
        assert_eq!(o.rtp_timestamp, None);
        f.push_raw(1, 3_000, 96, 0x110, true, 0);
        assert_eq!(f.pop(0)[0].2, 0);

        // Before any source is known, a report doesn't select one.
        let mut f = Fixture::new(&[96], tcp());
        let o = f.rtcp(&sender_report(0x111, 1_000_000), 0);
        assert_eq!(
            o,
            RtcpOutcome {
                rtp_timestamp: None,
                other_source: None,
            }
        );
        assert_eq!(f.r.selected_ssrc(), None);
        assert_eq!(f.r.counters().sources, 0);
    }

    /// A sender report from the expected source before any RTP sets the
    /// timeline's start, though it's stamped later than the next RTP packet.
    #[test]
    fn sender_report_sets_start() {
        let mut f = Fixture::new(&[96], tcp().ssrc(0x110));
        let o = f.rtcp(&sender_report(0x110, 3_090), 0);
        assert_eq!(o.rtp_timestamp.unwrap().elapsed(), 0);
        assert_eq!(o.other_source, None);
        assert_eq!(f.r.selected_ssrc(), Some(0x110));
        f.push_raw(1, 3_000, 96, 0x110, true, 0);
        assert_eq!(f.pop(0)[0].2, -90);
    }

    /// Every sender report in a compound packet goes to its source; only the
    /// first's timestamp is returned.
    #[test]
    fn compound_sender_reports() {
        let mut f = Fixture::new(&[96], tcp().ssrc(1));
        f.push(1, 96, 1, 0);
        f.push(2, 96, 1, 0);
        f.seqs(0);
        let mut c = sender_report(2, 0);
        c.extend(sender_report(1, 3_000));
        let o = f.rtcp(&c, 0);
        assert_eq!(o.rtp_timestamp, None);
        assert_eq!(o.other_source.unwrap().ssrc, 2);
        let rr = f.r.reception_report(f.at(500)).unwrap();
        assert_eq!((rr.ssrc, rr.lsr, rr.dlsr), (1, 0x2f99_cccc, 32_768));
    }

    /// A BYE from a non-selected source forgets it; from the selected one, it
    /// keeps playing (switching isn't implemented).
    #[test]
    fn bye_ends_sources() {
        let mut f = Fixture::new(&[96], ReceiverOptions::default().ssrc(1));
        f.push(1, 96, 1, 0);
        f.push(100, 96, 2, 0);
        assert_eq!(f.r.counters().sources, 2);
        f.rtcp(&goodbye(&[2, 1]), 0);
        assert_eq!(f.r.sources.len(), 1);
        assert_eq!(f.seqs(50), [1]);
        let c = f.r.counters();
        assert_eq!((c.byes, c.unselected), (1, 1));
        f.push(2, 96, 1, 0);
        assert_eq!(f.seqs(50), [2]);
    }

    /// The source table is bounded; the least recently heard non-selected
    /// source is forgotten to make room.
    #[test]
    fn max_sources() {
        let mut f = Fixture::new(&[96], tcp().ssrc(1).max_sources(2));
        f.push(1, 96, 1, 0);
        f.seqs(0);
        f.push(1, 96, 2, 1);
        f.push(1, 96, 3, 2);
        assert_eq!(
            f.r.sources.iter().map(|s| s.ssrc).collect::<Vec<_>>(),
            [1, 3]
        );
        let mut f = Fixture::new(&[96], tcp().ssrc(1).max_sources(1));
        f.push(1, 96, 1, 0);
        assert_eq!(f.push(1, 96, 2, 0), Pushed::Unselected { first: false });
        assert_eq!(f.seqs(0), [1]);
    }

    /// Over UDP, the selected source's packets are reordered; an unselected
    /// source's are dropped once due.
    #[test]
    fn udp_reorder() {
        let mut f = Fixture::new(&[96], ReceiverOptions::default().ssrc(1));
        f.push(2, 96, 1, 0);
        f.push(1, 96, 1, 0);
        f.push(1, 96, 2, 0);
        assert_eq!(f.seqs(0), []);
        assert_eq!(f.r.poll_timeout(), Some(f.at(50)));
        assert_eq!(f.seqs(50), [1, 2]);
        assert_eq!(f.r.counters().unselected, 1);
        assert_eq!(f.r.poll_timeout(), None);
    }

    /// `Received::packet_ref` supplies the pin position, so a depacketizer
    /// accumulating reordered packets retains their data (R5).
    #[test]
    fn packet_ref_pin_pos() {
        let mut f = Fixture::new(&[96], ReceiverOptions::default().ssrc(1));
        f.push(2, 96, 1, 0);
        let pos1 = f.buf.end();
        f.push(1, 96, 1, 0);
        let t = f.at(50);
        let p = f.r.pop(&f.buf, t).unwrap();
        assert_eq!(p.header.sequence_number(), 1);
        let pkt = p.packet_ref((), &f.buf, pos1 + 12, 1);
        assert_eq!(pkt.pin_pos(), pos1 - 13);
        assert_eq!(pkt.payload().to_vec(), b"x");
    }
}
