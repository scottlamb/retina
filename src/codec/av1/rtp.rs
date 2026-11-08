// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! AV1 RTP depacketizer: RTP packets in, temporal units in Low Overhead
//! Bitstream Format out (every OBU with obu_has_size_field = 1, as
//! AV1-ISOBMFF §2.4 requires of a sample).
//!
//! Reference: RTP Payload Format For AV1, AOMedia v1.0.0 (cited as
//! "RTP §x"). Behaviour cross-checked against GStreamer's rtpav1depay.
//!
//! Policy for damaged input: a temporal unit is emitted only when every
//! packet of it is known to have arrived and every OBU in it is complete.
//! Anything else is dropped whole and counted; the next emitted unit carries
//! the count in `loss` so a recorder can mark the discontinuity.

use std::collections::VecDeque;
use std::fmt;

use super::obu::{
    self, OBU_PADDING, OBU_TEMPORAL_DELIMITER, OBU_TILE_LIST, ObuError, read_leb128_usize,
};

/// Bound on OBU elements parsed from one RTP packet. A packet needs at least
/// two bytes per element (length + OBU header), so even a jumbo payload stays
/// well under this.
const MAX_ELEMENTS_PER_PACKET: usize = 4096;

#[derive(Debug, Clone, Copy)]
pub struct Av1RtpPacket<'a> {
    /// Extended (unwrapped) RTP timestamp, as retina's
    /// `Timestamp::timestamp()` gives.
    pub timestamp: i64,
    pub mark: bool,
    /// Packets lost immediately before this one.
    pub loss: u16,
    /// RTP payload: aggregation header + OBU elements.
    pub payload: &'a [u8],
}

/// A temporal delimiter OBU with its (zero) size field: header 0x12 (type 2,
/// has_size_field), obu_size 0.
pub const TEMPORAL_DELIMITER: [u8; 2] = [0x12, 0x00];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TemporalUnit {
    pub timestamp: i64,
    /// Low Overhead Bitstream Format: one temporal delimiter OBU (`12 00`)
    /// first, then every OBU re-written with obu_has_size_field = 1 and the
    /// size field; delimiters, padding and tile list OBUs from the packets
    /// removed; extension headers kept.
    ///
    /// The leading delimiter is what GStreamer's `rtpav1depay` emits and
    /// `isofmp4mux` stores, so samples written from these units are byte for
    /// byte the samples GStreamer writes for the same stream. (AV1-ISOBMFF §2.4
    /// only recommends against delimiters in samples; decoders accept them.)
    pub data: Vec<u8>,
    /// `obu::is_random_access(&data)`; false when that could not be parsed
    /// (counted in `Stats::random_access_parse_errors`).
    pub random_access: bool,
    /// Packets lost (as reported by the caller) or discarded by the
    /// depacketizer since the previous emitted unit, including those of
    /// units dropped in between. Non-zero means the stream is discontinuous
    /// before or within this unit's timestamp.
    pub loss: u16,
    /// N bit seen on the first packet (RTP §4.4: first packet of a coded
    /// video sequence).
    pub new_coded_video_sequence: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DepacketizeError {
    /// The RTP payload was empty (no aggregation header).
    EmptyPayload,
    /// An OBU element's length or framing was invalid.
    BadElement(&'static str),
    /// An OBU inside the packet was malformed.
    Obu(ObuError),
    /// The previous packet ended with an unfinished OBU fragment (Y = 1) but
    /// this one does not continue it (Z = 0) (RTP §4.4).
    FragmentNotContinued,
    /// A packet with M = 1 left an OBU fragment open (Y = 1); an OBU cannot
    /// span temporal units (RTP §4.4, §5).
    FragmentAtMarker,
    /// The temporal unit exceeded `Limits::max_tu_bytes`.
    TemporalUnitTooLarge,
    /// The temporal unit exceeded `Limits::max_obus_per_tu`, or the packet
    /// carried more than the per-packet element bound.
    TooManyObus,
    /// A completed unit is waiting in `pull()`; this packet would complete
    /// another. Nothing was changed: pull, then push the packet again.
    PendingNotPulled,
}

impl fmt::Display for DepacketizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DepacketizeError::EmptyPayload => write!(f, "AV1 RTP: empty payload"),
            DepacketizeError::BadElement(why) => write!(f, "AV1 RTP: bad OBU element: {why}"),
            DepacketizeError::Obu(e) => write!(f, "AV1 RTP: {e}"),
            DepacketizeError::FragmentNotContinued => {
                write!(f, "AV1 RTP: OBU fragment not continued (Y=1 then Z=0)")
            }
            DepacketizeError::FragmentAtMarker => {
                write!(f, "AV1 RTP: OBU fragment open at marker packet")
            }
            DepacketizeError::TemporalUnitTooLarge => {
                write!(f, "AV1 RTP: temporal unit exceeds byte limit")
            }
            DepacketizeError::TooManyObus => write!(f, "AV1 RTP: too many OBUs"),
            DepacketizeError::PendingNotPulled => {
                write!(f, "AV1 RTP: previous temporal unit not pulled")
            }
        }
    }
}

impl std::error::Error for DepacketizeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DepacketizeError::Obu(e) => Some(e),
            _ => None,
        }
    }
}

impl From<ObuError> for DepacketizeError {
    fn from(e: ObuError) -> Self {
        DepacketizeError::Obu(e)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    pub max_tu_bytes: usize,
    pub max_obus_per_tu: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            max_tu_bytes: 16 * 1024 * 1024,
            max_obus_per_tu: 4096,
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stats {
    pub tus_emitted: u64,
    /// Units dropped because of loss, a malformed packet, an incomplete OBU
    /// or a limit.
    pub tus_dropped: u64,
    /// Packets that did not end up in an emitted unit for those reasons
    /// (packets of a unit already being discarded, stray late packets, and
    /// the packets of dropped units).
    pub packets_dropped: u64,
    /// Emitted units whose random-access check could not parse the sequence
    /// or frame header; they are emitted with `random_access = false`.
    pub random_access_parse_errors: u64,
}

/// A temporal unit being assembled.
struct Building {
    timestamp: i64,
    data: Vec<u8>,
    obus: usize,
    packets: u64,
    loss: u16,
    new_cvs: bool,
    /// Bytes of an OBU element whose remaining fragments are still to come
    /// (the last packet had Y = 1).
    fragment: Option<Vec<u8>>,
}

pub struct Depacketizer {
    limits: Limits,
    cur: Option<Building>,
    /// Packets of this timestamp are discarded until the marker or a new
    /// timestamp: the unit is already known to be damaged.
    discard_ts: Option<i64>,
    /// Timestamp of the last unit closed by its marker or by the next
    /// timestamp; a later packet carrying it is stray.
    closed_ts: Option<i64>,
    /// Loss to report on the next emitted unit.
    carry_loss: u16,
    /// Completed units waiting for pull(). Normally at most one; a single
    /// packet can complete two (the previous unit by its new timestamp when
    /// the marker was never sent, and its own unit by its marker), and push
    /// refuses to run while any is waiting, so this never exceeds two.
    pending: VecDeque<TemporalUnit>,
    stats: Stats,
}

/// How a packet's elements are delimited (RTP §4.4, aggregation header).
struct AggregationHeader {
    z: bool,
    y: bool,
    w: u8,
    n: bool,
}

fn parse_aggregation_header(b: u8) -> AggregationHeader {
    AggregationHeader {
        z: b & 0x80 != 0,
        y: b & 0x40 != 0,
        w: (b >> 4) & 0x03,
        n: b & 0x08 != 0,
    }
}

/// Split a payload (after the aggregation header) into OBU elements and call
/// `f(index, is_last, element)` for each (RTP §4.3, §4.4): with W = 0 every
/// element carries a leb128 length; with W = 1..3 there are exactly W
/// elements and only the first W - 1 carry one, the last taking the rest.
fn for_each_element(
    mut rest: &[u8],
    w: u8,
    mut f: impl FnMut(usize, bool, &[u8]) -> Result<(), DepacketizeError>,
) -> Result<(), DepacketizeError> {
    if rest.is_empty() {
        return Err(DepacketizeError::BadElement("no OBU element"));
    }
    let mut index = 0usize;
    loop {
        if index >= MAX_ELEMENTS_PER_PACKET {
            return Err(DepacketizeError::TooManyObus);
        }
        let last_by_count = w != 0 && index.checked_add(1) == Some(usize::from(w));
        let element;
        if last_by_count {
            element = rest;
            rest = &[];
        } else {
            let (len, used) = read_leb128_usize(rest)
                .map_err(|_| DepacketizeError::BadElement("bad element length"))?;
            let after = rest
                .get(used..)
                .ok_or(DepacketizeError::BadElement("truncated"))?;
            let (e, r) = after
                .split_at_checked(len)
                .ok_or(DepacketizeError::BadElement("element longer than packet"))?;
            element = e;
            rest = r;
        }
        if element.is_empty() {
            return Err(DepacketizeError::BadElement("empty element"));
        }
        let is_last = last_by_count || (w == 0 && rest.is_empty());
        if !is_last && rest.is_empty() {
            // W said more elements follow than the packet holds.
            return Err(DepacketizeError::BadElement("fewer elements than W"));
        }
        f(index, is_last, element)?;
        if is_last {
            return Ok(());
        }
        index = index.saturating_add(1);
    }
}

impl Building {
    fn new(timestamp: i64, loss: u16, new_cvs: bool) -> Self {
        Building {
            timestamp,
            data: Vec::new(),
            obus: 0,
            packets: 0,
            loss,
            new_cvs,
            fragment: None,
        }
    }

    /// Append one complete OBU (as carried in RTP: obu_size optional) in Low
    /// Overhead Bitstream Format.
    fn push_obu(&mut self, obu_bytes: &[u8], limits: &Limits) -> Result<(), DepacketizeError> {
        let (header, hdr_bytes, payload) = obu::split_obu_any(obu_bytes)?;
        // RTP §5: temporal delimiters and tile lists are not to be sent; drop
        // them if they are. Padding carries nothing a sample needs, and
        // AV1-ISOBMFF §2.4 asks samples not to contain it.
        if matches!(
            header.obu_type,
            OBU_TEMPORAL_DELIMITER | OBU_TILE_LIST | OBU_PADDING
        ) {
            return Ok(());
        }
        let obus = self
            .obus
            .checked_add(1)
            .ok_or(DepacketizeError::TooManyObus)?;
        if obus > limits.max_obus_per_tu {
            return Err(DepacketizeError::TooManyObus);
        }
        // header + at most 8 leb128 bytes + payload.
        let grow = hdr_bytes
            .len()
            .checked_add(8)
            .and_then(|n| n.checked_add(payload.len()))
            .ok_or(DepacketizeError::TemporalUnitTooLarge)?;
        let total = self
            .data
            .len()
            .checked_add(grow)
            .ok_or(DepacketizeError::TemporalUnitTooLarge)?;
        if total > limits.max_tu_bytes {
            return Err(DepacketizeError::TemporalUnitTooLarge);
        }
        obu::write_obu_with_size(hdr_bytes, payload, &mut self.data);
        self.obus = obus;
        Ok(())
    }

    /// Feed the packet's elements into this unit. `Ok(false)` means the
    /// packet began with a continuation (Z = 1) for which no fragment was in
    /// progress: the start of that OBU is lost, so the unit is damaged.
    fn push_packet(
        &mut self,
        agg: &AggregationHeader,
        elements: &[u8],
        limits: &Limits,
    ) -> Result<bool, DepacketizeError> {
        if self.fragment.is_some() && !agg.z {
            return Err(DepacketizeError::FragmentNotContinued);
        }
        let mut damaged = false;
        for_each_element(elements, agg.w, |index, is_last, element| {
            let continues = index == 0 && agg.z;
            let unfinished = is_last && agg.y;
            if continues {
                let Some(mut frag) = self.fragment.take() else {
                    // RTP §4.4: Z = 1 with nothing in progress; the leading
                    // fragment cannot be used.
                    damaged = true;
                    return Ok(());
                };
                let len = frag
                    .len()
                    .checked_add(element.len())
                    .and_then(|n| n.checked_add(self.data.len()))
                    .ok_or(DepacketizeError::TemporalUnitTooLarge)?;
                if len > limits.max_tu_bytes {
                    return Err(DepacketizeError::TemporalUnitTooLarge);
                }
                frag.extend_from_slice(element);
                if unfinished {
                    self.fragment = Some(frag);
                    return Ok(());
                }
                return self.push_obu(&frag, limits);
            }
            if unfinished {
                let len = element
                    .len()
                    .checked_add(self.data.len())
                    .ok_or(DepacketizeError::TemporalUnitTooLarge)?;
                if len > limits.max_tu_bytes {
                    return Err(DepacketizeError::TemporalUnitTooLarge);
                }
                self.fragment = Some(element.to_vec());
                return Ok(());
            }
            self.push_obu(element, limits)
        })?;
        Ok(!damaged)
    }
}

/// Counters only: the buffered media is not printed.
impl fmt::Debug for Depacketizer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Depacketizer")
            .field("stats", &self.stats())
            .finish()
    }
}

impl Depacketizer {
    pub fn new(limits: Limits) -> Self {
        Depacketizer {
            limits,
            cur: None,
            discard_ts: None,
            closed_ts: None,
            carry_loss: 0,
            pending: VecDeque::with_capacity(2),
            stats: Stats::default(),
        }
    }

    /// Counters for health.
    pub fn stats(&self) -> Stats {
        self.stats
    }

    /// The next complete temporal unit, if one is ready. Call until None
    /// after each push: one packet can complete two units (see `push`).
    pub fn pull(&mut self) -> Option<TemporalUnit> {
        self.pending.pop_front()
    }

    fn add_loss(&mut self, n: u64) {
        let n = u16::try_from(n).unwrap_or(u16::MAX);
        self.carry_loss = self.carry_loss.saturating_add(n);
    }

    /// Drop the unit in progress (if any) and discard the rest of `ts`.
    /// `this_packet` counts the packet being handled as dropped too.
    fn drop_current(&mut self, discard: Option<i64>, this_packet: bool) {
        let mut packets = u64::from(this_packet);
        if let Some(b) = self.cur.take() {
            packets = packets.saturating_add(b.packets);
            self.carry_loss = self.carry_loss.saturating_add(b.loss);
            self.stats.tus_dropped = self.stats.tus_dropped.saturating_add(1);
        } else if this_packet {
            // A unit that never got a packet in is still a lost unit.
            self.stats.tus_dropped = self.stats.tus_dropped.saturating_add(1);
        }
        self.stats.packets_dropped = self.stats.packets_dropped.saturating_add(packets);
        self.add_loss(packets);
        self.discard_ts = discard;
    }

    /// Close the unit in progress as complete and make it pending.
    fn finish_current(&mut self) {
        let Some(b) = self.cur.take() else {
            return;
        };
        self.closed_ts = Some(b.timestamp);
        if b.data.is_empty() {
            // Only temporal delimiters or padding: nothing to record.
            return;
        }
        let random_access = match obu::is_random_access(&b.data) {
            Ok(v) => v,
            Err(_) => {
                self.stats.random_access_parse_errors =
                    self.stats.random_access_parse_errors.saturating_add(1);
                false
            }
        };
        let loss = self.carry_loss.saturating_add(b.loss);
        self.carry_loss = 0;
        self.stats.tus_emitted = self.stats.tus_emitted.saturating_add(1);
        let mut data = Vec::with_capacity(b.data.len().saturating_add(TEMPORAL_DELIMITER.len()));
        data.extend_from_slice(&TEMPORAL_DELIMITER);
        data.extend_from_slice(&b.data);
        self.pending.push_back(TemporalUnit {
            timestamp: b.timestamp,
            data,
            random_access,
            loss,
            new_coded_video_sequence: b.new_cvs,
        });
    }

    /// Feed one RTP packet in arrival order. A malformed packet returns Err
    /// and discards the partial TU; the depacketizer stays usable.
    ///
    /// A packet that would complete a unit while one is still waiting for
    /// pull() is refused with `PendingNotPulled` and changes nothing. One
    /// packet with M = 1 and a new timestamp, arriving after a unit whose
    /// marker was not sent, completes both units; pull() returns them in
    /// order.
    pub fn push(&mut self, pkt: Av1RtpPacket<'_>) -> Result<(), DepacketizeError> {
        let ts_changed = self
            .cur
            .as_ref()
            .is_some_and(|b| b.timestamp != pkt.timestamp);
        if !self.pending.is_empty() && (pkt.mark || ts_changed) {
            return Err(DepacketizeError::PendingNotPulled);
        }

        // A new timestamp ends whatever came before (RTP §4.2: all packets of
        // a unit share its timestamp; the marker packet was lost or not
        // sent). The old unit is complete only if no packet went missing in
        // between and no OBU fragment is open.
        if ts_changed {
            let complete = pkt.loss == 0 && self.cur.as_ref().is_some_and(|b| b.fragment.is_none());
            if complete {
                self.finish_current();
            } else {
                // Its late packets must not start a unit of their own.
                let old = self.cur.as_ref().map(|b| b.timestamp);
                self.drop_current(None, false);
                self.closed_ts = old;
            }
        }
        if self.discard_ts.is_some_and(|ts| ts != pkt.timestamp) {
            self.discard_ts = None;
        }

        if self.discard_ts == Some(pkt.timestamp) {
            self.stats.packets_dropped = self.stats.packets_dropped.saturating_add(1);
            self.add_loss(u64::from(pkt.loss).saturating_add(1));
            if pkt.mark {
                self.discard_ts = None;
                self.closed_ts = Some(pkt.timestamp);
            }
            return Ok(());
        }

        if self.cur.is_none() && self.closed_ts == Some(pkt.timestamp) {
            // Late or duplicated packet of a unit already closed.
            self.stats.packets_dropped = self.stats.packets_dropped.saturating_add(1);
            self.add_loss(u64::from(pkt.loss));
            return Ok(());
        }

        let Some((&agg_byte, elements)) = pkt.payload.split_first() else {
            self.drop_at(&pkt, true);
            self.add_loss(u64::from(pkt.loss));
            return Err(DepacketizeError::EmptyPayload);
        };
        let agg = parse_aggregation_header(agg_byte);

        // Loss inside a unit leaves a hole in it (RTP §4.4 cannot repair it).
        if pkt.loss > 0 && self.cur.is_some() {
            self.drop_at(&pkt, true);
            self.add_loss(u64::from(pkt.loss));
            return Ok(());
        }

        let limits = self.limits;
        let cur = self
            .cur
            .get_or_insert_with(|| Building::new(pkt.timestamp, pkt.loss, agg.n));
        cur.packets = cur.packets.saturating_add(1);
        match cur.push_packet(&agg, elements, &limits) {
            Ok(true) => {}
            Ok(false) => {
                self.drop_at(&pkt, false);
                return Ok(());
            }
            Err(e) => {
                self.drop_at(&pkt, false);
                return Err(e);
            }
        }
        if pkt.mark {
            if self.cur.as_ref().is_some_and(|b| b.fragment.is_some()) {
                self.drop_current(None, false);
                self.closed_ts = Some(pkt.timestamp);
                return Err(DepacketizeError::FragmentAtMarker);
            }
            self.finish_current();
        }
        Ok(())
    }

    /// Drop the unit at `pkt` and discard the rest of its timestamp until its
    /// marker, unless this packet is the marker.
    fn drop_at(&mut self, pkt: &Av1RtpPacket<'_>, this_packet: bool) {
        let discard = if pkt.mark {
            self.closed_ts = Some(pkt.timestamp);
            None
        } else {
            Some(pkt.timestamp)
        };
        self.drop_current(discard, this_packet);
    }
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::panic,
    clippy::arithmetic_side_effects
)]
mod tests {
    use super::obu::{OBU_FRAME, OBU_METADATA, OBU_TILE_GROUP, iter_obus, write_leb128};
    use super::*;

    /// An OBU as RTP carries it by default: no obu_size.
    fn obu(t: u8, payload: &[u8]) -> Vec<u8> {
        let mut v = vec![t << 3];
        v.extend_from_slice(payload);
        v
    }

    /// The same OBU in Low Overhead Bitstream Format.
    /// What a unit carries: the leading temporal delimiter, then `body`.
    fn td(body: Vec<u8>) -> Vec<u8> {
        let mut v = TEMPORAL_DELIMITER.to_vec();
        v.extend_from_slice(&body);
        v
    }

    fn lobf(t: u8, payload: &[u8]) -> Vec<u8> {
        let mut v = vec![(t << 3) | 2];
        write_leb128(payload.len() as u64, &mut v);
        v.extend_from_slice(payload);
        v
    }

    fn agg(z: bool, y: bool, w: u8, n: bool) -> u8 {
        (u8::from(z) << 7) | (u8::from(y) << 6) | (w << 4) | (u8::from(n) << 3)
    }

    /// Payload: aggregation header + elements framed for W.
    fn payload(z: bool, y: bool, w: u8, n: bool, elements: &[Vec<u8>]) -> Vec<u8> {
        let mut v = vec![agg(z, y, w, n)];
        for (i, e) in elements.iter().enumerate() {
            let last_unprefixed = w != 0 && i + 1 == elements.len();
            if !last_unprefixed {
                write_leb128(e.len() as u64, &mut v);
            }
            v.extend_from_slice(e);
        }
        v
    }

    fn pkt(_seq: u16, ts: i64, mark: bool, loss: u16, payload: &[u8]) -> Av1RtpPacket<'_> {
        Av1RtpPacket {
            timestamp: ts,
            mark,
            loss,
            payload,
        }
    }

    fn frame_payload(tag: u8, len: usize) -> Vec<u8> {
        (0..len).map(|i| tag.wrapping_add(i as u8)).collect()
    }

    #[test]
    fn single_packet_tu() {
        let mut d = Depacketizer::new(Limits::default());
        let fp = frame_payload(0x10, 20);
        let p = payload(false, false, 1, true, &[obu(OBU_FRAME, &fp)]);
        d.push(pkt(1, 9000, true, 0, &p)).unwrap();
        let tu = d.pull().unwrap();
        assert_eq!(tu.timestamp, 9000);
        assert_eq!(tu.data, td(lobf(OBU_FRAME, &fp)));
        assert!(tu.new_coded_video_sequence);
        assert_eq!(tu.loss, 0);
        assert!(!tu.random_access);
        assert!(d.pull().is_none());
        assert_eq!(d.stats().tus_emitted, 1);
    }

    #[test]
    fn aggregation_w0_and_w1_to_w3() {
        let parts = [
            (OBU_METADATA, frame_payload(1, 3)),
            (OBU_FRAME, frame_payload(2, 40)),
            (OBU_TILE_GROUP, frame_payload(3, 7)),
        ];
        for w in 0u8..=3 {
            let count = if w == 0 { 3 } else { usize::from(w) };
            let elements: Vec<Vec<u8>> = parts[..count].iter().map(|(t, p)| obu(*t, p)).collect();
            let expected: Vec<u8> = parts[..count]
                .iter()
                .flat_map(|(t, p)| lobf(*t, p))
                .collect();
            let mut d = Depacketizer::new(Limits::default());
            let p = payload(false, false, w, false, &elements);
            d.push(pkt(1, 100, true, 0, &p)).unwrap();
            assert_eq!(d.pull().unwrap().data, td(expected), "W={w}");
        }
    }

    #[test]
    fn w_larger_than_elements_is_malformed() {
        let mut d = Depacketizer::new(Limits::default());
        // W = 3 but only one length-prefixed element and nothing after it.
        let mut p = vec![agg(false, false, 3, false)];
        let e = obu(OBU_FRAME, &[1, 2, 3]);
        write_leb128(e.len() as u64, &mut p);
        p.extend_from_slice(&e);
        assert!(matches!(
            d.push(pkt(1, 100, true, 0, &p)),
            Err(DepacketizeError::BadElement(_))
        ));
    }

    #[test]
    fn obu_fragmented_over_three_packets() {
        let fp = frame_payload(0x40, 29);
        let whole = obu(OBU_FRAME, &fp); // 30 bytes
        let (a, rest) = whole.split_at(10);
        let (b, c) = rest.split_at(10);
        let p1 = payload(false, true, 1, false, &[a.to_vec()]);
        let p2 = payload(true, true, 1, false, &[b.to_vec()]);
        let p3 = payload(true, false, 1, false, &[c.to_vec()]);
        let mut d = Depacketizer::new(Limits::default());
        d.push(pkt(1, 100, false, 0, &p1)).unwrap();
        d.push(pkt(2, 100, false, 0, &p2)).unwrap();
        assert!(d.pull().is_none());
        d.push(pkt(3, 100, true, 0, &p3)).unwrap();
        assert_eq!(d.pull().unwrap().data, td(lobf(OBU_FRAME, &fp)));
    }

    #[test]
    fn fragment_then_more_elements_in_last_packet() {
        // The continuation completes and another OBU follows in the same
        // packet (W = 2).
        let fp = frame_payload(0x40, 15);
        let whole = obu(OBU_FRAME, &fp);
        let (a, b) = whole.split_at(6);
        let md = frame_payload(9, 4);
        let p1 = payload(false, true, 1, false, &[a.to_vec()]);
        let p2 = payload(true, false, 2, false, &[b.to_vec(), obu(OBU_METADATA, &md)]);
        let mut d = Depacketizer::new(Limits::default());
        d.push(pkt(1, 5, false, 0, &p1)).unwrap();
        d.push(pkt(2, 5, true, 0, &p2)).unwrap();
        let mut expected = lobf(OBU_FRAME, &fp);
        expected.extend(lobf(OBU_METADATA, &md));
        assert_eq!(d.pull().unwrap().data, td(expected));
    }

    #[test]
    fn marker_lost_timestamp_change() {
        let one = payload(false, false, 1, false, &[obu(OBU_FRAME, &[1, 2, 3])]);
        let two = payload(false, false, 1, false, &[obu(OBU_FRAME, &[4, 5, 6])]);

        // With a reported loss the old unit may have lost its tail: dropped.
        let mut d = Depacketizer::new(Limits::default());
        d.push(pkt(1, 100, false, 0, &one)).unwrap();
        d.push(pkt(3, 200, true, 1, &two)).unwrap();
        let tu = d.pull().unwrap();
        assert_eq!(tu.timestamp, 200);
        assert_eq!(tu.data, td(lobf(OBU_FRAME, &[4, 5, 6])));
        assert!(tu.loss >= 1);
        assert_eq!(d.stats().tus_dropped, 1);
        assert_eq!(d.stats().packets_dropped, 1);

        // With no loss and no open fragment every packet arrived: the old
        // unit is complete and is emitted when the new timestamp shows up.
        let mut d = Depacketizer::new(Limits::default());
        d.push(pkt(1, 100, false, 0, &one)).unwrap();
        d.push(pkt(2, 200, false, 0, &two)).unwrap();
        let tu = d.pull().unwrap();
        assert_eq!((tu.timestamp, tu.loss), (100, 0));
        assert_eq!(tu.data, td(lobf(OBU_FRAME, &[1, 2, 3])));
        // The packet that closed it was kept for the next unit.
        let three = payload(false, false, 1, false, &[obu(OBU_FRAME, &[7])]);
        d.push(pkt(3, 200, true, 0, &three)).unwrap();
        let mut expected = lobf(OBU_FRAME, &[4, 5, 6]);
        expected.extend(lobf(OBU_FRAME, &[7]));
        assert_eq!(d.pull().unwrap().data, td(expected));

        // An open fragment at the timestamp change: the old unit is dropped.
        let mut d = Depacketizer::new(Limits::default());
        let frag = payload(false, true, 1, false, &[obu(OBU_FRAME, &[1, 2])]);
        d.push(pkt(1, 100, false, 0, &frag)).unwrap();
        d.push(pkt(2, 200, true, 0, &two)).unwrap();
        assert_eq!(d.pull().unwrap().timestamp, 200);
        assert_eq!(d.stats().tus_dropped, 1);
    }

    #[test]
    fn loss_mid_tu_drops_the_unit() {
        let a = payload(false, false, 1, false, &[obu(OBU_FRAME, &[1])]);
        let b = payload(false, false, 1, false, &[obu(OBU_TILE_GROUP, &[2])]);
        let c = payload(false, false, 1, false, &[obu(OBU_TILE_GROUP, &[3])]);
        let mut d = Depacketizer::new(Limits::default());
        d.push(pkt(1, 100, false, 0, &a)).unwrap();
        d.push(pkt(3, 100, false, 1, &b)).unwrap();
        // The rest of that unit is discarded, marker included.
        d.push(pkt(4, 100, true, 0, &c)).unwrap();
        assert!(d.pull().is_none());
        let s = d.stats();
        assert_eq!((s.tus_dropped, s.packets_dropped, s.tus_emitted), (1, 3, 0));
        // The next unit is clean and reports the discontinuity.
        d.push(pkt(5, 200, true, 0, &a)).unwrap();
        let tu = d.pull().unwrap();
        assert_eq!(tu.timestamp, 200);
        assert!(tu.loss >= 1);
        // A stray late packet of the closed unit is ignored.
        d.push(pkt(2, 200, true, 0, &a)).unwrap();
        assert!(d.pull().is_none());
    }

    #[test]
    fn malformed_leb128_is_an_error_and_recoverable() {
        let mut bad = vec![agg(false, false, 0, false)];
        bad.extend_from_slice(&[0xFF; 9]);
        let mut d = Depacketizer::new(Limits::default());
        assert!(matches!(
            d.push(pkt(1, 100, true, 0, &bad)),
            Err(DepacketizeError::BadElement(_))
        ));
        // A length running past the packet.
        let mut long = vec![agg(false, false, 0, false), 50];
        long.extend_from_slice(&obu(OBU_FRAME, &[1]));
        assert!(d.push(pkt(2, 200, true, 0, &long)).is_err());
        assert_eq!(d.stats().tus_dropped, 2);
        let good = payload(false, false, 1, false, &[obu(OBU_FRAME, &[1])]);
        d.push(pkt(3, 300, true, 0, &good)).unwrap();
        assert_eq!(d.pull().unwrap().timestamp, 300);
    }

    #[test]
    fn oversize_tu_is_dropped() {
        let limits = Limits {
            max_tu_bytes: 64,
            max_obus_per_tu: 3,
        };
        let mut d = Depacketizer::new(limits);
        let big = payload(false, false, 1, false, &[obu(OBU_FRAME, &[0; 100])]);
        assert_eq!(
            d.push(pkt(1, 100, false, 0, &big)),
            Err(DepacketizeError::TemporalUnitTooLarge)
        );
        // Discarding continues to the marker without another error.
        let small = payload(false, false, 1, false, &[obu(OBU_FRAME, &[1])]);
        d.push(pkt(2, 100, true, 0, &small)).unwrap();
        assert!(d.pull().is_none());

        // Fragments are bounded too.
        let frag = payload(false, true, 1, false, &[vec![0x30; 40]]);
        d.push(pkt(3, 200, false, 0, &frag)).unwrap();
        let more = payload(true, true, 1, false, &[vec![0; 40]]);
        assert_eq!(
            d.push(pkt(4, 200, false, 0, &more)),
            Err(DepacketizeError::TemporalUnitTooLarge)
        );

        // OBU count.
        let four: Vec<Vec<u8>> = (0..4).map(|i| obu(OBU_FRAME, &[i])).collect();
        let p = payload(false, false, 0, false, &four);
        assert_eq!(
            d.push(pkt(5, 300, true, 0, &p)),
            Err(DepacketizeError::TooManyObus)
        );
        d.push(pkt(6, 400, true, 0, &small)).unwrap();
        assert_eq!(d.pull().unwrap().timestamp, 400);
        assert_eq!(d.stats().tus_dropped, 3);
    }

    #[test]
    fn continuation_with_nothing_in_progress() {
        // Joining mid-unit: the leading fragment's OBU start is lost, so the
        // unit is incomplete and dropped whole; no error is reported.
        let p = payload(
            true,
            false,
            2,
            false,
            &[vec![1, 2, 3], obu(OBU_FRAME, &[4, 5])],
        );
        let mut d = Depacketizer::new(Limits::default());
        d.push(pkt(1, 100, false, 0, &p)).unwrap();
        let tail = payload(false, false, 1, false, &[obu(OBU_TILE_GROUP, &[6])]);
        d.push(pkt(2, 100, true, 0, &tail)).unwrap();
        assert!(d.pull().is_none());
        assert_eq!(d.stats().tus_dropped, 1);
        let good = payload(false, false, 1, false, &[obu(OBU_FRAME, &[1])]);
        d.push(pkt(3, 200, true, 0, &good)).unwrap();
        assert!(d.pull().unwrap().loss >= 1);
    }

    #[test]
    fn fragment_not_continued_is_malformed() {
        let p1 = payload(false, true, 1, false, &[obu(OBU_FRAME, &[1, 2])]);
        let p2 = payload(false, false, 1, false, &[obu(OBU_FRAME, &[3])]);
        let mut d = Depacketizer::new(Limits::default());
        d.push(pkt(1, 100, false, 0, &p1)).unwrap();
        assert_eq!(
            d.push(pkt(2, 100, true, 0, &p2)),
            Err(DepacketizeError::FragmentNotContinued)
        );
        // Y = 1 on the marker packet.
        assert_eq!(
            d.push(pkt(3, 200, true, 0, &p1)),
            Err(DepacketizeError::FragmentAtMarker)
        );
        assert!(d.pull().is_none());
    }

    #[test]
    fn temporal_delimiter_padding_and_tile_list_removed() {
        let elements = vec![
            obu(OBU_TEMPORAL_DELIMITER, &[]),
            obu(OBU_FRAME, &[1, 2]),
            obu(OBU_PADDING, &[0, 0, 0]),
            obu(OBU_TILE_LIST, &[9]),
        ];
        let p = payload(false, false, 0, false, &elements);
        let mut d = Depacketizer::new(Limits::default());
        d.push(pkt(1, 100, true, 0, &p)).unwrap();
        assert_eq!(d.pull().unwrap().data, td(lobf(OBU_FRAME, &[1, 2])));

        // A unit of nothing but a temporal delimiter yields nothing.
        let td = payload(false, false, 1, false, &[obu(OBU_TEMPORAL_DELIMITER, &[])]);
        d.push(pkt(2, 200, true, 0, &td)).unwrap();
        assert!(d.pull().is_none());
    }

    #[test]
    fn obu_with_size_field_already_present() {
        let fp = [7u8, 8, 9];
        let with_size = lobf(OBU_FRAME, &fp);
        let p = payload(false, false, 1, false, std::slice::from_ref(&with_size));
        let mut d = Depacketizer::new(Limits::default());
        d.push(pkt(1, 100, true, 0, &p)).unwrap();
        assert_eq!(d.pull().unwrap().data, td(with_size));

        // Extension header kept; size rewritten minimally.
        let mut ext = vec![(OBU_FRAME << 3) | 0x04 | 0x02, 0b0100_1000, 0x83, 0x00];
        ext.extend_from_slice(&fp);
        let p = payload(false, false, 1, false, &[ext]);
        d.push(pkt(2, 200, true, 0, &p)).unwrap();
        let tu = d.pull().unwrap();
        assert_eq!(
            tu.data,
            td(vec![(OBU_FRAME << 3) | 0x06, 0b0100_1000, 3, 7, 8, 9])
        );
        let o = iter_obus(&tu.data).nth(1).unwrap().unwrap();
        assert_eq!((o.header.temporal_id, o.header.spatial_id), (2, 1));

        // obu_size that disagrees with the element length.
        let mut wrong = vec![(OBU_FRAME << 3) | 0x02, 5];
        wrong.extend_from_slice(&fp);
        let p = payload(false, false, 1, false, &[wrong]);
        assert_eq!(
            d.push(pkt(3, 300, true, 0, &p)),
            Err(DepacketizeError::Obu(ObuError::SizeMismatch))
        );
    }

    #[test]
    fn one_packet_completes_two_units() {
        // Sender never sets the marker on the first unit; the next unit is a
        // single marker packet.
        let a = payload(false, false, 1, false, &[obu(OBU_FRAME, &[1])]);
        let b = payload(false, false, 1, false, &[obu(OBU_FRAME, &[2])]);
        let mut d = Depacketizer::new(Limits::default());
        d.push(pkt(1, 100, false, 0, &a)).unwrap();
        d.push(pkt(2, 200, true, 0, &b)).unwrap();
        assert_eq!(d.pull().unwrap().timestamp, 100);
        assert_eq!(d.pull().unwrap().timestamp, 200);
        assert!(d.pull().is_none());
        assert_eq!(d.stats().tus_emitted, 2);
    }

    #[test]
    fn pending_unit_is_not_lost() {
        let a = payload(false, false, 1, false, &[obu(OBU_FRAME, &[1])]);
        let b = payload(false, false, 1, false, &[obu(OBU_FRAME, &[2])]);
        let mut d = Depacketizer::new(Limits::default());
        d.push(pkt(1, 100, true, 0, &a)).unwrap();
        assert_eq!(
            d.push(pkt(2, 200, true, 0, &b)),
            Err(DepacketizeError::PendingNotPulled)
        );
        assert_eq!(d.pull().unwrap().timestamp, 100);
        d.push(pkt(2, 200, true, 0, &b)).unwrap();
        assert_eq!(d.pull().unwrap().timestamp, 200);
        assert_eq!(d.stats().packets_dropped, 0);
    }

    #[test]
    fn empty_payload_and_empty_element() {
        let mut d = Depacketizer::new(Limits::default());
        assert_eq!(
            d.push(pkt(1, 100, true, 0, &[])),
            Err(DepacketizeError::EmptyPayload)
        );
        assert!(d.push(pkt(2, 200, true, 0, &[0x00, 0x00])).is_err());
        assert!(d.push(pkt(3, 300, true, 0, &[0x10])).is_err());
        let good = payload(false, false, 1, false, &[obu(OBU_FRAME, &[1])]);
        d.push(pkt(4, 400, true, 0, &good)).unwrap();
        assert!(d.pull().is_some());
    }
}

/// The depacketizer and OBU helpers against real encoder output: libaom and SVT-AV1 streams
/// payloaded by GStreamer's `rtpav1pay` (`mtu=600`, so OBUs are fragmented), compared with
/// `av1parse`'s temporal units. The vectors and the script that makes them are in `testdata/`.
#[cfg(test)]
mod fixture_tests {
    use super::super::obu::{
        self, OBU_TEMPORAL_DELIMITER, av1c_record, codec_string, find_sequence_header, iter_obus,
        parse_sequence_header,
    };
    use super::{Av1RtpPacket, Depacketizer, Limits};

    struct Record {
        flag: u8,
        data: Vec<u8>,
    }

    fn fixture(name: &str) -> Vec<u8> {
        let path = format!(
            "{}/src/codec/av1/testdata/{name}",
            env!("CARGO_MANIFEST_DIR")
        );
        std::fs::read(&path).unwrap_or_else(|e| panic!("{path}: {e}"))
    }

    /// Records framed by gen_fixtures.py: u32 BE length, u8 flags, data.
    fn records(name: &str) -> Vec<Record> {
        let raw = fixture(name);
        let mut out = Vec::new();
        let mut rest = &raw[..];
        while !rest.is_empty() {
            let len = u32::from_be_bytes(rest[..4].try_into().unwrap()) as usize;
            out.push(Record {
                flag: rest[4],
                data: rest[5..5 + len].to_vec(),
            });
            rest = &rest[5 + len..];
        }
        out
    }

    struct Rtp<'a> {
        seq: u16,
        ts: u32,
        mark: bool,
        payload: &'a [u8],
    }

    /// Fixed header, CSRCs, header extension and padding (RFC 3550 §5.1, §5.3.1).
    fn parse_rtp(b: &[u8]) -> Option<Rtp<'_>> {
        if b.len() < 12 || b[0] >> 6 != 2 {
            return None;
        }
        let cc = usize::from(b[0] & 0x0F);
        let mut off = 12 + 4 * cc;
        if b[0] & 0x10 != 0 {
            let ext = b.get(off + 2..off + 4)?;
            off += 4 + 4 * usize::from(u16::from_be_bytes([ext[0], ext[1]]));
        }
        let mut end = b.len();
        if b[0] & 0x20 != 0 {
            end = end.checked_sub(usize::from(*b.last()?))?;
        }
        Some(Rtp {
            seq: u16::from_be_bytes([b[2], b[3]]),
            ts: u32::from_be_bytes([b[4], b[5], b[6], b[7]]),
            mark: b[1] & 0x80 != 0,
            payload: b.get(off..end)?,
        })
    }

    /// Temporal delimiters removed, every OBU re-written with a minimal size field.
    fn normalise(tu: &[u8]) -> Vec<u8> {
        let mut out = Vec::new();
        for o in iter_obus(tu) {
            let o = o.unwrap();
            if o.header.obu_type == OBU_TEMPORAL_DELIMITER {
                continue;
            }
            out.push(o.raw[0] | 0x02);
            out.extend_from_slice(&o.raw[1..o.header.header_len]);
            obu::write_leb128(o.payload.len() as u64, &mut out);
            out.extend_from_slice(o.payload);
        }
        out
    }

    fn depacketize(name: &str) -> Vec<super::TemporalUnit> {
        let mut d = Depacketizer::new(Limits::default());
        let mut out = Vec::new();
        let mut last_seq: Option<u16> = None;
        for r in records(&format!("{name}.rtp")) {
            let p = parse_rtp(&r.data).expect("RTP header");
            let loss = last_seq.map_or(0, |s| p.seq.wrapping_sub(s).wrapping_sub(1));
            last_seq = Some(p.seq);
            d.push(Av1RtpPacket {
                timestamp: i64::from(p.ts),
                mark: p.mark,
                loss,
                payload: p.payload,
            })
            .unwrap();
            while let Some(tu) = d.pull() {
                out.push(tu);
            }
        }
        let s = d.stats();
        assert_eq!((s.tus_dropped, s.packets_dropped), (0, 0), "{name}: {s:?}");
        assert_eq!(s.random_access_parse_errors, 0);
        out
    }

    fn check(name: &str, width: u32, height: u32, color_description: bool) {
        let refs = records(&format!("{name}.tu"));
        let tus = depacketize(name);
        assert_eq!(tus.len(), refs.len(), "{name}: TU count");
        let mut fragmented = false;
        for r in records(&format!("{name}.rtp")) {
            let p = parse_rtp(&r.data).unwrap();
            fragmented |= p.payload[0] & 0xC0 != 0;
        }
        assert!(fragmented, "{name}: fixture should exercise fragmentation");

        for (i, (tu, r)) in tus.iter().zip(&refs).enumerate() {
            assert_eq!(
                normalise(&tu.data),
                normalise(&r.data),
                "{name}: TU {i} bytes"
            );
            let mut minimal = super::TEMPORAL_DELIMITER.to_vec();
            minimal.extend_from_slice(&normalise(&tu.data));
            assert_eq!(
                tu.data, minimal,
                "{name}: TU {i} is not one delimiter then minimal LOBF"
            );
            assert_eq!(
                tu.random_access,
                r.flag == 1,
                "{name}: TU {i} random access"
            );
            assert_eq!(tu.loss, 0);
            assert_eq!(obu::is_random_access(&r.data).unwrap(), r.flag == 1);
        }
        assert_eq!(tus.iter().filter(|t| t.random_access).count(), 2, "{name}");
        assert!(tus[0].random_access && tus[0].new_coded_video_sequence);

        let seq_obu = find_sequence_header(&tus[0].data).unwrap().unwrap();
        let seq_payload = iter_obus(seq_obu).next().unwrap().unwrap().payload;
        let info = parse_sequence_header(seq_payload).unwrap();
        assert_eq!(
            (info.max_frame_width, info.max_frame_height),
            (width, height)
        );
        assert_eq!((info.seq_profile, info.bit_depth), (0, 8));
        assert_eq!(info.color_description_present, color_description);

        // GStreamer always writes the long form, taking the colour fields from
        // its caps colorimetry (bt601 here). Where the stream carries a colour
        // description (SVT-AV1 writes 6/6/6) ours is the long form too and must
        // match it whole; where it carries none (libaom) ours is the short form
        // and must equal GStreamer's first four fields.
        let gst = String::from_utf8(fixture(&format!("{name}.codec.txt"))).unwrap();
        let gst = gst.trim();
        if info.color_description_present {
            assert_eq!(codec_string(&info), gst, "{name}: codec string");
        } else {
            let gst_short: Vec<&str> = gst.split('.').take(4).collect();
            assert_eq!(
                codec_string(&info),
                gst_short.join("."),
                "{name}: codec string"
            );
        }

        let av1c = av1c_record(seq_obu, &info).unwrap();
        assert_eq!(av1c, fixture(&format!("{name}.av1c")), "{name}: av1C");
    }

    #[test]
    fn libaom_640x360() {
        check("aom_640x360", 640, 360, false);
    }

    #[test]
    fn svtav1_320x180() {
        check("svt_320x180", 320, 180, true);
    }

    /// xorshift64* with a fixed seed: reproducible without a dependency.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    #[test]
    fn mutated_packets_never_panic() {
        let mut corpus: Vec<Vec<u8>> = Vec::new();
        for name in ["aom_640x360", "svt_320x180"] {
            corpus.extend(records(&format!("{name}.rtp")).into_iter().map(|r| r.data));
        }
        let mut rng = Rng(0x5EED_A1B2_C3D4_0001);
        let mut d = Depacketizer::new(Limits {
            max_tu_bytes: 64 * 1024,
            max_obus_per_tu: 64,
        });
        let mut emitted = 0usize;
        let mut i = 0usize;
        let mut held: Option<Vec<u8>> = None;
        for _ in 0..20_000 {
            let mut p = corpus[i % corpus.len()].clone();
            i += 1;
            match rng.below(10) {
                0 => {
                    // Flip up to four bytes anywhere, header included.
                    for _ in 0..1 + rng.below(4) {
                        let at = rng.below(p.len());
                        p[at] ^= 1 << rng.below(8);
                    }
                }
                1 => p.truncate(rng.below(p.len() + 1)),
                2 => i = i.saturating_sub(1), // duplicate: the same packet comes again
                3 => {
                    // Reorder: hold this one back and send it after the next.
                    if let Some(h) = held.replace(p.clone()) {
                        p = h;
                    } else {
                        continue;
                    }
                }
                4 => i += rng.below(3), // drop the next packet or two
                5 => {
                    // Random garbage payload behind a valid header.
                    let n = rng.below(64);
                    p.truncate(12);
                    p.extend((0..n).map(|_| rng.next() as u8));
                }
                _ => {}
            }
            let Some(r) = parse_rtp(&p) else { continue };
            let pkt = Av1RtpPacket {
                timestamp: i64::from(r.ts),
                mark: r.mark,
                loss: (rng.below(8) == 0) as u16,
                payload: r.payload,
            };
            let _ = d.push(pkt);
            while let Some(tu) = d.pull() {
                emitted += 1;
                assert!(tu.data.starts_with(&super::TEMPORAL_DELIMITER));
                for (k, o) in iter_obus(&tu.data).enumerate() {
                    let o = o.expect("emitted TU must be valid LOBF");
                    assert_eq!(
                        o.header.obu_type == OBU_TEMPORAL_DELIMITER,
                        k == 0,
                        "exactly one delimiter, first"
                    );
                }
                let _ = obu::is_random_access(&tu.data);
                let _ = find_sequence_header(&tu.data).map(|s| {
                    s.map(|s| {
                        if let Some(Ok(o)) = iter_obus(s).next()
                            && let Ok(info) = parse_sequence_header(o.payload)
                        {
                            let _ = codec_string(&info);
                            let _ = av1c_record(s, &info);
                        }
                    })
                });
            }
        }
        let s = d.stats();
        assert!(emitted > 100, "too few TUs survived: {emitted} {s:?}");
        assert!(s.tus_dropped > 0);
    }
}
