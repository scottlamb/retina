// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [`Receiver`]: tracks a received RTP stream's SSRC, sequence numbers, and
//! timestamps.

use std::num::{NonZeroU16, NonZeroU32};

use super::timeline::{Timeline, TimestampReason};
use super::{Continuity, PacketHeader, ReceivedPacketMeta};
use crate::rtcp::SenderReportRef;
use crate::{NtpTimestamp, Timestamp};

/// An error from [`Receiver::new`]: the options are unacceptable.
///
/// This is opaque; its [`std::fmt::Display`] output describes the problem.
#[derive(Clone, Debug)]
pub struct OptionsError(pub(super) String);

impl std::fmt::Display for OptionsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for OptionsError {}

/// Options for a [`Receiver`].
#[derive(Clone, Debug)]
pub struct ReceiverOptions {
    pub(crate) ssrc: Option<u32>,
    pub(crate) initial_sequence_number: Option<u16>,
    pub(crate) initial_rtptime: Option<u32>,
    pub(crate) max_forward_jump_secs: Option<NonZeroU32>,
    pub(crate) learn_ssrc_from_sender_report: bool,
}

impl Default for ReceiverOptions {
    fn default() -> Self {
        Self {
            ssrc: None,
            initial_sequence_number: None,
            initial_rtptime: None,
            max_forward_jump_secs: None,
            learn_ssrc_from_sender_report: true,
        }
    }
}

impl ReceiverOptions {
    /// Sets the expected SSRC, e.g. (for a client receiving via `PLAY`) from
    /// the `SETUP` response's `Transport` header. By default, the receiver
    /// learns the SSRC from the first packet.
    #[inline]
    pub fn ssrc(self, ssrc: u32) -> Self {
        Self {
            ssrc: Some(ssrc),
            ..self
        }
    }

    /// Sets the expected first sequence number, e.g. (for a client receiving
    /// via `PLAY`) from the `PLAY` response's `RTP-Info` header. By default,
    /// the receiver learns it from the first packet.
    #[inline]
    pub fn initial_sequence_number(self, seq: u16) -> Self {
        Self {
            initial_sequence_number: Some(seq),
            ..self
        }
    }

    /// Sets the RTP timestamp which is time 0 in normal play time, e.g. (for a
    /// client receiving via `PLAY`) from the `PLAY` response's `RTP-Info`
    /// header. By default, this is the first packet's (or sender report's)
    /// timestamp.
    #[inline]
    pub fn initial_rtptime(self, rtptime: u32) -> Self {
        Self {
            initial_rtptime: Some(rtptime),
            ..self
        }
    }

    /// Enforces that each RTP packet's timestamp is no earlier than the
    /// previous one's and at most `secs` later. By default, any jump is
    /// allowed.
    #[inline]
    pub fn max_forward_jump_secs(self, secs: Option<NonZeroU32>) -> Self {
        Self {
            max_forward_jump_secs: secs,
            ..self
        }
    }

    /// Sets whether a sender report can establish the SSRC when it isn't yet
    /// known. Defaults to true.
    #[inline]
    pub fn learn_ssrc_from_sender_report(self, learn: bool) -> Self {
        Self {
            learn_ssrc_from_sender_report: learn,
            ..self
        }
    }
}

/// An error from [`Receiver::rtp`] or [`Receiver::sender_report`].
///
/// The receiver's state is unchanged by the offending packet; the caller
/// decides whether to continue.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ReceiveError {
    /// An RTP packet's SSRC doesn't match the expected one.
    #[non_exhaustive]
    WrongSsrc {
        expected: u32,
        received: u32,
        sequence_number: u16,
    },

    /// An RTP packet's sequence number is before the expected one.
    ///
    /// Sequence numbers are compared as wrapping 16-bit values; a jump forward
    /// of more than `0x8000` is indistinguishable from a step backward. To
    /// tolerate reordering, duplicates, or a sender restarting its sequence
    /// numbers, pass packets through a [`super::Reorderer`] first.
    #[non_exhaustive]
    OutOfOrder {
        ssrc: u32,
        expected: u16,
        received: u16,
    },

    /// A timestamp is unacceptable, e.g. it jumped more than allowed by
    /// [`ReceiverOptions::max_forward_jump_secs`].
    #[non_exhaustive]
    Timestamp {
        /// The SSRC and sequence number of the RTP packet, or `None` for a
        /// sender report.
        rtp: Option<(u32, u16)>,

        /// Why the timestamp was rejected.
        reason: TimestampReason,
    },
}

impl std::fmt::Display for ReceiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReceiveError::WrongSsrc {
                expected,
                received,
                sequence_number,
            } => write!(
                f,
                "wrong ssrc {received:08x} at seq={sequence_number}; expecting ssrc {expected:08x}"
            ),
            ReceiveError::OutOfOrder {
                ssrc,
                expected,
                received,
            } => write!(
                f,
                "out-of-order packet or large loss: ssrc {ssrc:08x} seq={received}; \
                 expecting seq={expected}"
            ),
            ReceiveError::Timestamp {
                rtp: Some(_),
                reason,
            } => write!(f, "{reason}"),
            ReceiveError::Timestamp { rtp: None, reason } => write!(f, "{reason} in RTCP SR"),
        }
    }
}

impl std::error::Error for ReceiveError {}

/// How a sender report's SSRC relates to the receiver's.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum SsrcMatch {
    /// The SSRC matches the established one.
    Matched,

    /// No SSRC was established; this sender report established it.
    Learned,

    /// No SSRC was established, and
    /// [`ReceiverOptions::learn_ssrc_from_sender_report`] is false.
    Unknown,

    /// The SSRC differs from the established one. The caller decides whether
    /// to ignore the report, use it anyway, or treat it as an error.
    Mismatched { expected: u32 },
}

/// Information from [`Receiver::sender_report`].
#[derive(Copy, Clone, Debug)]
#[non_exhaustive]
pub struct SenderReportInfo {
    /// The report's SSRC.
    pub ssrc: u32,

    /// The report's RTP timestamp, placed on the receiver's timeline.
    pub timestamp: Timestamp,

    /// The report's wall clock time.
    pub ntp_timestamp: NtpTimestamp,

    /// How `ssrc` relates to the receiver's SSRC.
    pub ssrc_match: SsrcMatch,
}

/// Describes how the receiver formed its expectation for the stream's `ssrc`
/// or `seq`, for error messages.
#[derive(Copy, Clone, Debug)]
enum Source {
    Options,
    RtpPacket,
    SenderReport,
}

#[derive(Copy, Clone)]
struct Ssrc {
    source: Source,
    ssrc: u32,
}

impl std::fmt::Debug for Ssrc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{:08x} (from {:?})", self.ssrc, self.source)
    }
}

#[derive(Copy, Clone)]
struct Seq {
    source: Source,
    next: u16,
}

impl std::fmt::Debug for Seq {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{} (from {:?})", self.next, self.source)
    }
}

/// Receives a single RTP stream (one SSRC): checks SSRC and sequence numbers
/// and extends timestamps, producing the [`ReceivedPacketMeta`] that depacketizers
/// take. The counterpart of [`super::Sender`].
///
/// This is sans-I/O and doesn't touch payloads: the caller validates the
/// header via [`PacketHeader::validate`], calls [`Receiver::rtp`], and builds
/// a [`crate::rtp::ReceivedPacketRef`] however it buffers data.
///
/// It expects packets in sequence order, as from a [`super::Reorderer`],
/// returning [`ReceiveError::OutOfOrder`] otherwise.
/// [RFC 3550 section 8.2](https://tools.ietf.org/html/rfc3550#section-8.2)
/// allows the SSRC to change mid-session (after an RTCP BYE); this isn't
/// supported, but the caller can replace the `Receiver`.
///
/// Its `Debug` output summarizes its expectations, for error messages.
pub struct Receiver {
    timeline: Timeline,
    ssrc: Option<Ssrc>,
    seq: Option<Seq>,
    learn_ssrc_from_sender_report: bool,

    /// True if [`Receiver::restart_sequence`] was called since the last packet.
    restarted: bool,

    /// RTP packets accepted by [`Receiver::rtp`].
    rtp_packets: u64,

    /// Packets lost, as indicated by gaps in sequence numbers.
    lost: u64,

    /// Sender reports seen by [`Receiver::sender_report`].
    sender_reports: u64,
}

impl std::fmt::Debug for Receiver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Receiver")
            .field("ssrc", &self.ssrc)
            .field("next_seq", &self.seq)
            .field("rtp_packets", &self.rtp_packets)
            .field("lost", &self.lost)
            .field("sender_reports", &self.sender_reports)
            .finish()
    }
}

impl Receiver {
    /// Creates a receiver for a stream with the given clock rate.
    ///
    /// Errors on a clock rate of 0 or one too high for
    /// [`ReceiverOptions::max_forward_jump_secs`].
    pub fn new(clock_rate: u32, options: ReceiverOptions) -> Result<Self, OptionsError> {
        let timeline = Timeline::new(
            options.initial_rtptime,
            clock_rate,
            options.max_forward_jump_secs,
        )?;
        Ok(Self {
            timeline,
            ssrc: options.ssrc.map(|ssrc| Ssrc {
                source: Source::Options,
                ssrc,
            }),
            seq: options.initial_sequence_number.map(|next| Seq {
                source: Source::Options,
                next,
            }),
            learn_ssrc_from_sender_report: options.learn_ssrc_from_sender_report,
            restarted: false,
            rtp_packets: 0,
            lost: 0,
            sender_reports: 0,
        })
    }

    /// Returns the established SSRC, if any.
    #[inline]
    pub fn ssrc(&self) -> Option<u32> {
        self.ssrc.map(|s| s.ssrc)
    }

    /// Returns the expected next sequence number, if any.
    #[inline]
    pub fn next_sequence_number(&self) -> Option<u16> {
        self.seq.map(|s| s.next)
    }

    /// Returns the number of RTP packets accepted so far.
    #[inline]
    pub fn rtp_packets(&self) -> u64 {
        self.rtp_packets
    }

    /// Returns the number of packets lost so far, as indicated by gaps in
    /// sequence numbers. This excludes any lost at a
    /// [`Continuity::Discontinuity`].
    #[inline]
    pub fn lost(&self) -> u64 {
        self.lost
    }

    /// Notes that the sender restarted its sequence numbers, as indicated by
    /// [`super::Reordered::restarted`].
    ///
    /// The next packet establishes the expected sequence number, and its
    /// [`ReceivedPacketMeta::continuity`] is [`Continuity::Discontinuity`]. The SSRC
    /// and timestamp checks are unchanged.
    pub fn restart_sequence(&mut self) {
        self.seq = None;
        self.restarted = true;
    }

    /// Returns the number of sender reports seen so far.
    #[inline]
    pub fn sender_reports(&self) -> u64 {
        self.sender_reports
    }

    /// Processes a validated RTP header, returning its metadata.
    ///
    /// [`ReceivedPacketMeta::continuity`] reports gaps in sequence numbers.
    pub fn rtp<Ctx>(
        &mut self,
        ctx: Ctx,
        header: &PacketHeader,
    ) -> Result<ReceivedPacketMeta<Ctx>, ReceiveError> {
        let sequence_number = header.sequence_number();
        let ssrc = header.ssrc();
        if let Some(expected) = self.ssrc
            && expected.ssrc != ssrc
        {
            return Err(ReceiveError::WrongSsrc {
                expected: expected.ssrc,
                received: ssrc,
                sequence_number,
            });
        }
        let loss = match self.seq {
            Some(s) => sequence_number.wrapping_sub(s.next),
            None => 0,
        };
        if loss > 0x80_00 {
            return Err(ReceiveError::OutOfOrder {
                ssrc,
                expected: self.seq.expect("loss > 0 implies seq").next,
                received: sequence_number,
            });
        }
        let timestamp = self
            .timeline
            .advance_to(header.timestamp())
            .map_err(|reason| ReceiveError::Timestamp {
                rtp: Some((ssrc, sequence_number)),
                reason,
            })?;
        if self.ssrc.is_none() {
            self.ssrc = Some(Ssrc {
                source: Source::RtpPacket,
                ssrc,
            });
        }
        self.seq = Some(Seq {
            source: self.seq.map(|s| s.source).unwrap_or(Source::RtpPacket),
            next: sequence_number.wrapping_add(1),
        });
        self.rtp_packets += 1;
        let continuity = if std::mem::take(&mut self.restarted) {
            Continuity::Discontinuity
        } else {
            match NonZeroU16::new(loss) {
                None => Continuity::Contiguous,
                Some(n) => {
                    self.lost += u64::from(n.get());
                    Continuity::Lost(n)
                }
            }
        };
        Ok(ReceivedPacketMeta {
            ctx,
            timestamp,
            sequence_number,
            ssrc,
            mark: header.mark(),
            continuity,
            extensions: Default::default(),
        })
    }

    /// Processes a sender report, placing its RTP timestamp on the timeline.
    ///
    /// This doesn't advance the timeline: a sender report's timestamp commonly
    /// refers to a time slightly before the latest RTP packet's.
    pub fn sender_report(
        &mut self,
        sr: &SenderReportRef<'_>,
    ) -> Result<SenderReportInfo, ReceiveError> {
        let timestamp = self
            .timeline
            .place(sr.rtp_timestamp())
            .map_err(|reason| ReceiveError::Timestamp { rtp: None, reason })?;
        let ssrc = sr.ssrc();
        let ssrc_match = match self.ssrc {
            Some(s) if s.ssrc == ssrc => SsrcMatch::Matched,
            Some(s) => SsrcMatch::Mismatched { expected: s.ssrc },
            None if self.learn_ssrc_from_sender_report => {
                self.ssrc = Some(Ssrc {
                    source: Source::SenderReport,
                    ssrc,
                });
                SsrcMatch::Learned
            }
            None => SsrcMatch::Unknown,
        };
        self.sender_reports += 1;
        Ok(SenderReportInfo {
            ssrc,
            timestamp,
            ntp_timestamp: sr.ntp_timestamp(),
            ssrc_match,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rtp::build_raw_rtp;

    fn lost(n: u16) -> Continuity {
        Continuity::Lost(NonZeroU16::new(n).unwrap())
    }

    fn header(seq: u16, ts: u32, ssrc: u32) -> PacketHeader {
        let pkt = build_raw_rtp(seq, ts, 96, ssrc, true, *b"x").unwrap();
        PacketHeader::validate(&pkt[..]).unwrap().header
    }

    #[test]
    fn learns_and_checks_ssrc() {
        let mut r = Receiver::new(90_000, ReceiverOptions::default()).unwrap();
        let m = r.rtp((), &header(10, 1000, 0x1234)).unwrap();
        assert_eq!(
            (m.continuity, m.timestamp.elapsed()),
            (Continuity::Contiguous, 0)
        );
        assert_eq!(r.ssrc(), Some(0x1234));
        assert!(matches!(
            r.rtp((), &header(11, 1000, 0x5678)),
            Err(ReceiveError::WrongSsrc {
                expected: 0x1234,
                received: 0x5678,
                ..
            })
        ));

        // The rejected packet didn't change the state.
        assert_eq!(r.next_sequence_number(), Some(11));
        let m = r.rtp((), &header(13, 1090, 0x1234)).unwrap();
        assert_eq!((m.continuity, m.timestamp.elapsed()), (lost(2), 90));
        assert_eq!(r.rtp_packets(), 2);
    }

    #[test]
    fn out_of_order() {
        let mut r = Receiver::new(90_000, ReceiverOptions::default().ssrc(0xd25614e)).unwrap();
        r.rtp((), &header(2, 2, 0xd25614e)).unwrap();
        assert!(matches!(
            r.rtp((), &header(1, 1, 0xd25614e)),
            Err(ReceiveError::OutOfOrder {
                expected: 3,
                received: 1,
                ..
            })
        ));

        // The rejected packet shouldn't have adjusted time.
        let m = r.rtp((), &header(3, 3, 0xd25614e)).unwrap();
        assert_eq!(
            (m.continuity, m.timestamp.elapsed()),
            (Continuity::Contiguous, 1)
        );
    }

    #[test]
    fn restart_sequence() {
        let mut r = Receiver::new(90_000, ReceiverOptions::default()).unwrap();
        r.rtp((), &header(1000, 0, 1)).unwrap();
        r.restart_sequence();
        let m = r.rtp((), &header(10, 90, 1)).unwrap();
        assert_eq!(
            (m.continuity, m.timestamp.elapsed()),
            (Continuity::Discontinuity, 90)
        );
        let m = r.rtp((), &header(12, 180, 1)).unwrap();
        assert_eq!(m.continuity, lost(1));
        assert_eq!((r.rtp_packets(), r.lost()), (3, 1));
    }

    #[test]
    fn initial_expectations() {
        let opts = ReceiverOptions::default()
            .initial_sequence_number(5)
            .initial_rtptime(100);
        let mut r = Receiver::new(90_000, opts).unwrap();
        let m = r.rtp((), &header(7, 190, 1)).unwrap();
        assert_eq!((m.continuity, m.timestamp.elapsed()), (lost(2), 90));
    }

    #[test]
    fn bad_clock_rate() {
        Receiver::new(0, ReceiverOptions::default()).unwrap_err();
        Receiver::new(
            u32::MAX,
            ReceiverOptions::default().max_forward_jump_secs(NonZeroU32::new(10)),
        )
        .unwrap_err();
    }
}
