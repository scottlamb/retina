// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Timestamp extension and mapping: a source's 32-bit (wrapping) RTP
//! timestamps to 64-bit ones ([`Extender`]), and those onto a stream's
//! continuous output timeline ([`Output`]).

use std::num::NonZeroU32;

use crate::Timestamp;

/// Extends one source's 32-bit (wrapping) RTP timestamps to `i64`, from that
/// source's own base.
///
/// Each timestamp is taken as the nearest one, modulo 2^32, to the previous
/// one: a difference of more than `i32::MAX` is a jump backward. This never
/// fails except on `i64` overflow, which takes about 2^32 packets each making
/// the largest possible jump: only possible with a hostile sender.
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct Extender {
    /// The latest extended timestamp, once one is known.
    last: Option<i64>,
}

impl Extender {
    /// Returns the extension of `rtp_timestamp` relative to the latest, or
    /// `None` on overflow, without advancing.
    fn extend(&self, rtp_timestamp: u32) -> Option<i64> {
        let Some(last) = self.last else {
            return Some(i64::from(rtp_timestamp));
        };
        let delta = (rtp_timestamp as i32).wrapping_sub(last as i32);
        last.checked_add(i64::from(delta))
    }

    /// Extends the timestamp of the next RTP packet in sequence order,
    /// advancing to it. Returns `None` on overflow, leaving the state
    /// unchanged.
    pub(crate) fn advance_to(&mut self, rtp_timestamp: u32) -> Option<i64> {
        let ts = self.extend(rtp_timestamp)?;
        self.last = Some(ts);
        Some(ts)
    }

    /// Extends a timestamp without advancing, as for a sender report. Its
    /// timestamp commonly refers to a time slightly before the latest RTP
    /// packet's. If no timestamp is known yet, this one becomes the base.
    pub(crate) fn place(&mut self, rtp_timestamp: u32) -> Option<i64> {
        let ts = self.extend(rtp_timestamp)?;
        self.last.get_or_insert(ts);
        Some(ts)
    }
}

/// A stream's output timeline: maps the selected source's extended timestamps
/// onto [`Timestamp`]s with a fixed clock rate and normal play time zero.
#[derive(Clone, Debug)]
pub(crate) struct Output {
    clock_rate: NonZeroU32,

    /// The RTP timestamp which is time 0 in normal play time, once known.
    start: Option<u32>,

    /// Added to the selected source's extended timestamps to get output
    /// timestamps, once the source is anchored.
    offset: Option<i64>,
}

impl Output {
    pub(crate) fn new(clock_rate: NonZeroU32, start: Option<u32>) -> Self {
        Self {
            clock_rate,
            start,
            offset: None,
        }
    }

    /// Forgets the selected source's mapping, so the next call to
    /// [`Output::map`] anchors a new one.
    #[allow(dead_code)] // for switching sources.
    pub(crate) fn unanchor(&mut self) {
        self.offset = None;
    }

    /// Maps the selected source's extended timestamp `ext`, whose 32-bit form
    /// is `rtp_timestamp`, onto the output timeline. Returns `None` on
    /// overflow or if the elapsed time underflows `i64`.
    ///
    /// The first call anchors the source: if the start isn't known yet, it
    /// becomes `rtp_timestamp`, and `rtp_timestamp` maps to the nearest
    /// timestamp to the start, modulo 2^32.
    pub(crate) fn map(&mut self, ext: i64, rtp_timestamp: u32) -> Option<Timestamp> {
        let offset = match self.offset {
            Some(o) => o,
            None => {
                let start = *self.start.get_or_insert(rtp_timestamp);
                let anchored =
                    i64::from(start) + i64::from((rtp_timestamp as i32).wrapping_sub(start as i32));
                let o = anchored.checked_sub(ext)?;
                self.offset = Some(o);
                o
            }
        };
        let timestamp = ext.checked_add(offset)?;
        Timestamp::new(timestamp, self.clock_rate, self.start.expect("set above"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const RATE: NonZeroU32 = NonZeroU32::new(90_000).unwrap();

    /// Extends and maps a sequence of RTP packet timestamps, returning their
    /// elapsed times.
    fn elapsed(start: Option<u32>, rtp: &[u32]) -> Vec<i64> {
        let mut e = Extender::default();
        let mut o = Output::new(RATE, start);
        rtp.iter()
            .map(|&ts| o.map(e.advance_to(ts).unwrap(), ts).unwrap().elapsed())
            .collect()
    }

    #[test]
    fn timeline() {
        // Normal usage.
        assert_eq!(elapsed(Some(42), &[83, 453]), [83 - 42, 453 - 42]);

        // Any jump is allowed, forward or backward.
        assert_eq!(
            elapsed(Some(100), &[100 + 10 * 90_000 + 1, 99]),
            [10 * 90_000 + 1, -1]
        );

        // Wraparound is normal too, including relative to the start.
        assert_eq!(elapsed(Some(u32::MAX), &[5]), [6]);
        assert_eq!(elapsed(Some(0xffff_fff0), &[0x10, 0x20]), [0x20, 0x30]);
        assert_eq!(elapsed(None, &[u32::MAX, 5]), [0, 6]);

        // No initial rtptime: the first packet is the start.
        assert_eq!(elapsed(None, &[218250000]), [0]);
    }

    /// A sender report placed before any RTP packet, stamped slightly later
    /// than it, sets the start.
    #[test]
    fn place_before_rtp() {
        let mut e = Extender::default();
        let mut o = Output::new(RATE, None);
        let sr = e.place(1_000).unwrap();
        assert_eq!(o.map(sr, 1_000).unwrap().elapsed(), 0);
        let rtp = e.advance_to(990).unwrap();
        assert_eq!(o.map(rtp, 990).unwrap().elapsed(), -10);
        let sr = e.place(985).unwrap();
        assert_eq!(o.map(sr, 985).unwrap().elapsed(), -15);
        let rtp = e.advance_to(3_990).unwrap();
        assert_eq!(o.map(rtp, 3_990).unwrap().elapsed(), 2_990);
    }

    #[test]
    fn overflow() {
        let mut e = Extender {
            last: Some(i64::MAX - 1),
        };
        assert_eq!(e.advance_to(((i64::MAX - 1) as u32).wrapping_add(2)), None);
        assert_eq!(e.last, Some(i64::MAX - 1));
        let mut o = Output::new(RATE, Some(0));
        let ts = e.advance_to((i64::MAX - 1) as u32).unwrap();
        assert!(o.map(ts, ts as u32).is_some());
    }

    #[test]
    fn cast() {
        let a = 0x1_FFFF_FFFFi64;
        let b = 0x1_0000_0000i64;
        assert_eq!(a as i32, -1);
        assert_eq!(b as i32, 0);
    }
}
