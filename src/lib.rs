// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! High-level RTSP library.
//!
//! The [`client`] module is the most mature. The [`codec`], [`rtp`], and
//! [`rtcp`] modules are usable on their own, by clients, servers, and proxies
//! alike. An RTSP server (`server`) and the send side of [`codec`] and [`rtp`]
//! are available under unstable features.

#![forbid(clippy::print_stderr, clippy::print_stdout)]
#![cfg_attr(docsrs, feature(doc_cfg))]
// Docs link to items behind the unstable features, which are missing or
// private without them. CI checks links with all features enabled.
#![cfg_attr(
    not(all(
        feature = "tokio",
        feature = "unstable-codec-analyzer",
        feature = "unstable-sans-io",
        feature = "unstable-server"
    )),
    allow(rustdoc::broken_intra_doc_links, rustdoc::private_intra_doc_links)
)]
// I prefer to use from_str_radix(..., 10) to explicitly note the base.
#![allow(clippy::from_str_radix_10)]

use rtsp::msg::Message;
use std::fmt::{Debug, Display};
use std::net::{IpAddr, SocketAddr};
use std::num::NonZeroU32;
use std::time::{Instant, SystemTime};

pub mod buf;
mod error;
mod hex;
#[doc(hidden)]
pub mod inputs;
mod mostly_ascii;

/// This is exposed for the fuzz tests. It is not a stable interface.
#[doc(hidden)]
pub mod testutil;

/// Wraps the supplied `ErrorInt` and returns it as an `Err`.
///
/// Like [`wrap!`], this uses whatever `Error` is in scope at the call site.
macro_rules! bail {
    ($e:expr) => {
        return Err(wrap!($e))
    };
}

/// Wraps the supplied `ErrorInt` in an `Error`.
///
/// `Error` resolves at the call site: `client::Error`, `server::Error`, or
/// the private `crate::error::Error` used by code they share. All three are
/// tuple structs around an `Arc<ErrorInt>`, and the latter converts to the
/// others via `From`.
macro_rules! wrap {
    ($e:expr) => {
        Error(std::sync::Arc::new($e))
    };
}

pub mod client;
pub mod codec;
pub mod rtcp;
pub mod rtp;
//mod error;
#[doc(hidden)]
pub mod rtsp;
#[cfg(feature = "unstable-server")]
pub mod server;
#[cfg(feature = "tokio")]
mod tokio;
#[cfg(any(feature = "tokio", feature = "unstable-sans-io"))]
mod udp_pair;

#[cfg(feature = "unstable-sans-io")]
#[cfg_attr(docsrs, doc(cfg(feature = "unstable-sans-io")))]
pub use udp_pair::UdpPair;

use error::ErrorInt;

/// A received RTSP message.
#[derive(Debug)]
struct ReceivedMessage {
    ctx: RtspMessageContext,
    msg: Message,
    body_pos: u64,
    body_len: u32,
}

/// An annotated RTP timestamp.
///
/// This couples together three pieces of information:
///
/// *   The stream's starting time, as a 32-bit RTP timestamp. When receiving, this is often
///     as stated in the RTSP `RTP-Info` header (see [`crate::rtp::ReceiverOptions::initial_rtptime`]
///     and [`crate::client::InitialTimestampPolicy`]); otherwise it's the first packet's (or
///     sender report's) timestamp. When sending, the caller chooses it.
///     According to [RFC 3550 section 5.1](https://datatracker.ietf.org/doc/html/rfc3550#section-5.1), "the initial
///     value of the timestamp SHOULD be random".
///
/// *   The codec-specific clock rate.
///
/// *   The timestamp as an `i64`. When receiving, its top bits are inferred from wraparounds
///     of 32-bit RTP timestamps: [`crate::rtp::Receiver`] treats timestamps that differ by more
///     than `i32::MAX` from previous timestamps as backwards jumps. When sending, the caller
///     chooses it, and [`crate::rtp::Sender`] maps it to a 32-bit RTP timestamp. It's allowed for
///     a timestamp to indicate a time *before* the stream's starting point.
///
/// In combination, these allow conversion to "normal play time" (NPT): seconds since start of
/// the stream.
///
/// According to [RFC 3550 section 5.1](https://datatracker.ietf.org/doc/html/rfc3550#section-5.1),
/// RTP timestamps "MUST be derived from a clock that increments monotonically". In practice,
/// many RTP senders violate this. [`crate::rtp::Receiver`] allows such violations unless
/// [`crate::rtp::ReceiverOptions::max_forward_jump_secs`] says otherwise.
///
/// [`Timestamp`] can't represent timestamps which overflow/underflow `i64` or
/// elapsed times (`elapsed = timestamp - start`) which underflow `i64`. [`crate::rtp::Receiver`]
/// will return error in these cases. This should rarely cause problems. It'd take ~2^32 packets
/// (~4 billion) to advance the time this far forward or backward even with a hostile sender.
///
/// The [`Display`] and [`Debug`] implementations currently display:
/// *   the bottom 32 bits, as seen in RTP packet headers. This advances at a
///     codec-specified clock rate.
/// *   the full timestamp.
/// *   NPT
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Timestamp {
    /// A timestamp which must be compared to `start`.
    timestamp: i64,

    /// The codec-specified clock rate, in Hz. Must be non-zero.
    clock_rate: NonZeroU32,

    /// The stream's starting time; see the type-level docs.
    start: u32,
}

impl Timestamp {
    /// Creates a new timestamp unless `timestamp - start` underflows.
    #[inline]
    pub fn new(timestamp: i64, clock_rate: NonZeroU32, start: u32) -> Option<Self> {
        timestamp.checked_sub(i64::from(start)).map(|_| Timestamp {
            timestamp,
            clock_rate,
            start,
        })
    }

    /// Returns time since some arbitrary point before the stream started.
    #[inline]
    pub fn timestamp(&self) -> i64 {
        self.timestamp
    }

    /// Returns timestamp of the start of the stream.
    #[inline]
    pub fn start(&self) -> u32 {
        self.start
    }

    /// Returns codec-specified clock rate, in Hz.
    #[inline]
    pub fn clock_rate(&self) -> NonZeroU32 {
        self.clock_rate
    }

    /// Returns elapsed time since the stream start in clock rate units.
    #[inline]
    pub fn elapsed(&self) -> i64 {
        self.timestamp - i64::from(self.start)
    }

    /// Returns elapsed time since the stream start in seconds, aka "normal play
    /// time" (NPT).
    #[inline]
    pub fn elapsed_secs(&self) -> f64 {
        (self.elapsed() as f64) / (self.clock_rate.get() as f64)
    }

    /// Returns `self + delta` unless it would overflow.
    pub fn try_add(&self, delta: u32) -> Option<Self> {
        // Check for `timestamp` overflow only. We don't need to check for
        // `timestamp - start` underflow because delta is non-negative.
        self.timestamp
            .checked_add(i64::from(delta))
            .map(|timestamp| Timestamp {
                timestamp,
                clock_rate: self.clock_rate,
                start: self.start,
            })
    }
}

impl Display for Timestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} (mod-2^32: {}), npt {:.03}",
            self.timestamp,
            self.timestamp as u32,
            self.elapsed_secs()
        )
    }
}

impl Debug for Timestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

/// The Unix epoch as an [`NtpTimestamp`].
pub const UNIX_EPOCH: NtpTimestamp = NtpTimestamp((2_208_988_800) << 32);

/// A wallclock time represented using the format of the Network Time Protocol.
///
/// NTP timestamps are in a fixed-point representation of seconds since
/// 0h UTC on 1 January 1900. The top 32 bits represent the integer part
/// (wrapping around every 2^32 seconds, about 136 years; NTP era 0 ends in
/// February 2036) and the bottom 32 bits represent the fractional part.
///
/// This is a simple wrapper around a `u64` in that format, with a `Display`
/// impl that writes the timestamp as a human-readable string. As the
/// timestamp doesn't say which era it's in, `Display` assumes it's between
/// the Unix epoch (1970) and `2106-02-07T06:28:15Z`; earlier times, such as
/// those of a misconfigured clock, display as later ones. Conversions to and
/// from [`SystemTime`] make the same assumption.
///
/// An `NtpTimestamp` isn't necessarily gathered from a real NTP server.
/// Reported NTP timestamps are allowed to jump backwards and/or be complete
/// nonsense.
///
/// The NTP timestamp of the Unix epoch is available via the constant [`UNIX_EPOCH`].
#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct NtpTimestamp(pub u64);

impl NtpTimestamp {
    /// Returns the local machine's realtime clock as an NTP timestamp.
    #[inline]
    pub fn now() -> Self {
        Self::from(SystemTime::now())
    }
}

/// Converts an unsigned Q32.32 fixed-point number of seconds to a `Duration`,
/// rounding to the nearest nanosecond.
fn q32_32_to_duration(v: u64) -> std::time::Duration {
    // `Duration::new` carries a rounded-up 1_000_000_000 nanoseconds.
    let nanos = ((v & 0xFFFF_FFFF) * 1_000_000_000 + (1 << 31)) >> 32;
    std::time::Duration::new(v >> 32, nanos as u32)
}

/// Converts a `Duration` to an unsigned Q32.32 fixed-point number of seconds,
/// wrapping every 2^32 seconds and rounding to the fixed-point precision.
fn duration_to_q32_32(d: std::time::Duration) -> u64 {
    // Nanoseconds are below 2^30, so the shift can't overflow. Rounding up
    // yields at most 2^32, which carries into the seconds.
    let frac = ((u64::from(d.subsec_nanos()) << 32) + 500_000_000) / 1_000_000_000;
    (d.as_secs() << 32).wrapping_add(frac)
}

impl From<SystemTime> for NtpTimestamp {
    /// Converts a [`SystemTime`].
    ///
    /// NTP timestamps wrap every 2^32 seconds, so times outside the range
    /// [`NtpTimestamp`] assumes (1970 through early 2106) have the same
    /// representation as some time within it, and don't round-trip.
    fn from(t: SystemTime) -> Self {
        NtpTimestamp(match t.duration_since(SystemTime::UNIX_EPOCH) {
            Ok(d) => UNIX_EPOCH.0.wrapping_add(duration_to_q32_32(d)),
            Err(e) => UNIX_EPOCH.0.wrapping_sub(duration_to_q32_32(e.duration())),
        })
    }
}

impl From<NtpTimestamp> for SystemTime {
    /// Converts to a [`SystemTime`] between the Unix epoch (1970) and early
    /// 2106, as described at [`NtpTimestamp`].
    fn from(t: NtpTimestamp) -> Self {
        SystemTime::UNIX_EPOCH + q32_32_to_duration(t.0.wrapping_sub(UNIX_EPOCH.0))
    }
}

impl std::fmt::Display for NtpTimestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let since_epoch = self.0.wrapping_sub(UNIX_EPOCH.0);
        let sec_since_epoch = (since_epoch >> 32) as u32;
        let ns = i32::try_from(((since_epoch & 0xFFFF_FFFF) * 1_000_000_000) >> 32)
            .expect("should be < 1_000_000_000");
        let tm = jiff::Timestamp::new(i64::from(sec_since_epoch), ns)
            .expect("u32 sec should be valid Timestamp");
        std::fmt::Display::fmt(&tm, f)
    }
}

impl std::fmt::Debug for NtpTimestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Write both the raw and display forms.
        write!(f, "{} /* {} */", self.0, self)
    }
}

/// A wall time taken from the local machine's realtime clock, used in error reporting.
///
/// This allows formatting via `Debug` and `Display` and conversion to [`SystemTime`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct WallTime(jiff::Timestamp);

impl WallTime {
    #[inline]
    fn now() -> Self {
        Self(jiff::Timestamp::now())
    }
}

impl Display for WallTime {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.0, f)
    }
}

impl From<WallTime> for SystemTime {
    #[inline]
    fn from(wall_time: WallTime) -> Self {
        wall_time.0.into()
    }
}

/// RTSP connection context.
///
/// This gives enough information to pick out the flow in a packet capture.
#[derive(Clone, Debug)]
pub struct ConnectionContext {
    local_addr: std::net::SocketAddr,
    peer_addr: std::net::SocketAddr,
    established_wall: WallTime,
}

impl ConnectionContext {
    #[doc(hidden)]
    pub fn dummy() -> Self {
        let addr = SocketAddr::new(IpAddr::V4(std::net::Ipv4Addr::UNSPECIFIED), 0);
        Self {
            local_addr: addr,
            peer_addr: addr,
            established_wall: WallTime::now(),
        }
    }
}

impl Display for ConnectionContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}(me)->{}@{}",
            self.local_addr, self.peer_addr, self.established_wall,
        )
    }
}

/// Context of a received message (or read error) within an RTSP connection.
///
/// When paired with a [`ConnectionContext`], this should allow picking the
/// message out of a packet capture.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct RtspMessageContext {
    /// The starting byte position within the input stream. The bottom 32 bits
    /// can be compared to the relative TCP sequence number.
    pos: u64,

    /// Time when the application parsed the message. Caveat: this may not
    /// closely match the time on a packet capture if the application is
    /// overloaded (or if `CLOCK_REALTIME` jumps).
    received_wall: WallTime,
    received: std::time::Instant,
}

impl RtspMessageContext {
    #[doc(hidden)]
    pub fn dummy() -> Self {
        Self {
            pos: 0,
            received_wall: WallTime::now(),
            received: std::time::Instant::now(),
        }
    }

    pub fn received(&self) -> std::time::Instant {
        self.received
    }

    pub fn pos(&self) -> u64 {
        self.pos
    }
}

impl Display for RtspMessageContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{}", self.pos, self.received_wall)
    }
}

/// Context for an active stream (RTP+RTCP session), either TCP or UDP. Owned version.
#[derive(Clone, Debug)]
pub struct StreamContext(StreamContextInner);

impl StreamContext {
    #[doc(hidden)]
    pub fn dummy() -> Self {
        StreamContext(StreamContextInner::Dummy)
    }
}

impl Display for StreamContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            StreamContextInner::Tcp(tcp) => {
                write!(
                    f,
                    "TCP, interleaved channel ids {}-{}",
                    tcp.rtp_channel_id,
                    tcp.rtp_channel_id + 1
                )
            }
            StreamContextInner::Udp(udp) => Display::fmt(udp, f),
            StreamContextInner::Dummy => write!(f, "dummy"),
        }
    }
}

#[derive(Clone, Debug)]
enum StreamContextInner {
    Tcp(TcpStreamContext),
    Udp(UdpStreamContext),
    Dummy,
}

/// Context for a UDP stream (aka UDP-based RTP transport). Unstable/internal. Exposed for benchmarks.
///
/// This stores only the RTP addresses; the RTCP addresses are assumed to use
/// the same IP and one port higher.
#[doc(hidden)]
#[derive(Copy, Clone, Debug)]
pub struct UdpStreamContext {
    local_ip: IpAddr,
    peer_ip: IpAddr,
    local_rtp_port: u16,
    peer_rtp_port: u16,
}

/// Context for a TCP stream. Unstable/internal. Exposed for benchmarks.
///
/// This stores only the RTP channel id; the RTCP channel id is assumed to be one higher.
#[doc(hidden)]
#[derive(Copy, Clone, Debug)]
pub struct TcpStreamContext {
    rtp_channel_id: u8,
}

impl Display for UdpStreamContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}-{}(me) -> {}:{}-{}",
            self.local_ip,
            self.local_rtp_port,
            self.local_rtp_port + 1,
            self.peer_ip,
            self.peer_rtp_port,
            self.peer_rtp_port + 1
        )
    }
}

/// Context for an RTP or RTCP packet, received either via RTSP interleaved data or UDP.
///
/// Should be paired with an [`ConnectionContext`] of the RTSP connection that started
/// the session. In the interleaved data case, it's assumed the packet was received over
/// that same connection.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PacketContext(PacketContextInner);

impl PacketContext {
    #[inline]
    pub fn received(&self) -> Instant {
        match self.0 {
            PacketContextInner::Tcp { msg_ctx } => msg_ctx.received,
            PacketContextInner::Udp { received, .. } => received,
            PacketContextInner::Dummy => Instant::now(),
        }
    }

    #[inline]
    pub fn received_wall(&self) -> WallTime {
        match self.0 {
            PacketContextInner::Tcp { msg_ctx } => msg_ctx.received_wall,
            PacketContextInner::Udp { received_wall, .. } => received_wall,
            PacketContextInner::Dummy => WallTime::now(),
        }
    }

    #[doc(hidden)]
    pub fn dummy() -> PacketContext {
        Self(PacketContextInner::Dummy)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum PacketContextInner {
    Tcp {
        msg_ctx: RtspMessageContext,
    },
    Udp {
        received: Instant,
        received_wall: WallTime,
    },
    Dummy,
}

impl Display for PacketContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            PacketContextInner::Udp { received_wall, .. } => {
                std::fmt::Display::fmt(&received_wall, f)
            }
            PacketContextInner::Tcp { msg_ctx } => std::fmt::Display::fmt(&msg_ctx, f),
            PacketContextInner::Dummy => write!(f, "dummy"),
        }
    }
}

// Let's assume pointers are either 32-bit or 64-bit so we can do the following
// infallible conversions.
#[cfg(any(feature = "h264", feature = "h265"))]
fn to_usize<V: Into<u32>>(v: V) -> usize {
    const {
        assert!(std::mem::size_of::<u32>() <= std::mem::size_of::<usize>());
    }
    v.into() as usize
}
fn to_u64(v: usize) -> u64 {
    const {
        assert!(std::mem::size_of::<usize>() <= std::mem::size_of::<u64>());
    }
    v as u64
}

#[cfg(test)]
mod test {
    use std::time::Duration;

    use super::*;

    #[test]
    fn ntp_system_time_round_trip() {
        let now = SystemTime::UNIX_EPOCH + Duration::new(1_792_000_000, 123_456_789);
        let last = SystemTime::UNIX_EPOCH + Duration::from_secs(u64::from(u32::MAX));
        for t in [
            now,
            SystemTime::UNIX_EPOCH,
            now + Duration::from_secs(1 << 30), // NTP era 1 (2036+).
            last,
        ] {
            assert_eq!(SystemTime::from(NtpTimestamp::from(t)), t, "{t:?}");
        }
        assert_eq!(SystemTime::from(UNIX_EPOCH), SystemTime::UNIX_EPOCH);

        // Times outside 1970 through 2106 wrap into it.
        assert_eq!(
            SystemTime::from(NtpTimestamp::from(
                SystemTime::UNIX_EPOCH - Duration::from_secs(1)
            )),
            last
        );

        // Rounding both ways makes every nanosecond value round-trip exactly.
        for nanos in (0..1_000_000_000).step_by(997) {
            let t = now + Duration::from_nanos(nanos);
            assert_eq!(SystemTime::from(NtpTimestamp::from(t)), t);
        }
    }

    #[test]
    fn ntp_display() {
        assert_eq!(UNIX_EPOCH.to_string(), "1970-01-01T00:00:00Z");
        assert_eq!(
            NtpTimestamp::from(SystemTime::UNIX_EPOCH + Duration::from_secs(u64::from(u32::MAX)))
                .to_string(),
            "2106-02-07T06:28:15Z"
        );
    }
}
