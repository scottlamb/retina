// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! High-level RTSP library.
//!
//! Currently this is useful for clients; it will be extended to support
//! servers and proxies.

#![forbid(clippy::print_stderr, clippy::print_stdout)]
// I prefer to use from_str_radix(..., 10) to explicitly note the base.
#![allow(clippy::from_str_radix_10)]

use bytes::Bytes;
use log::trace;
use rand::Rng;
use rtsp_types::Message;
use std::fmt::{Debug, Display};
use std::net::{IpAddr, SocketAddr, UdpSocket};
use std::num::NonZeroU32;
use std::ops::Range;

mod error;

mod hex;
pub mod rtcp;
pub mod rtp;

#[cfg(test)]
mod testutil;

pub use error::Error;

/// Wraps the supplied `ErrorInt` and returns it as an `Err`.
macro_rules! bail {
    ($e:expr) => {
        return Err(crate::error::Error(std::sync::Arc::new($e)))
    };
}

macro_rules! wrap {
    ($e:expr) => {
        crate::error::Error(std::sync::Arc::new($e))
    };
}

pub mod client;
pub mod codec;
//mod error;
mod tokio;

use error::ErrorInt;

/// A received RTSP message.
#[derive(Debug)]
struct ReceivedMessage {
    ctx: RtspMessageContext,
    msg: Message<Bytes>,
}

/// An annotated RTP timestamp.
///
/// This couples together three pieces of information:
///
/// *   The stream's starting time. In client use, this is often as received in the RTSP
///     `RTP-Info` header but may be controlled via [`crate::client::InitialTimestampPolicy`].
///     According to [RFC 3550 section 5.1](https://datatracker.ietf.org/doc/html/rfc3550#section-5.1), "the initial
///     value of the timestamp SHOULD be random".
///
/// *   The codec-specific clock rate.
///
/// *   The timestamp as an `i64`. In client use, its top bits should be inferred from wraparounds
///     of 32-bit RTP timestamps. The Retina client's policy is that timestamps that differ by more
///     than `i32::MAX` from previous timestamps are treated as backwards jumps. It's allowed for
///     a timestamp to indicate a time *before* the stream's starting point.
///
/// In combination, these allow conversion to "normal play time" (NPT): seconds since start of
/// the stream.
///
/// According to [RFC 3550 section 5.1](https://datatracker.ietf.org/doc/html/rfc3550#section-5.1),
/// RTP timestamps "MUST be derived from a clock that increments monotonically". In practice,
/// many RTP servers violate this. The Retina client allows such violations unless
/// [`crate::client::PlayOptions::enforce_timestamps_with_max_jump_secs`] says otherwise.
///
/// [`Timestamp`] can't represent timestamps which overflow/underflow `i64` can't be constructed or
/// elapsed times (`elapsed = timestamp - start`) which underflow `i64`. The client will return
/// error in these cases. This should rarely cause problems. It'd take ~2^32 packets (~4 billion)
/// to advance the time this far forward or backward even with a hostile server.
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

    /// The stream's starting time, as specified in the RTSP `RTP-Info` header.
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
/// (wrapping around every 68 years) and the bottom 32 bits represent the
/// fractional part.
///
/// This is a simple wrapper around a `u64` in that format, with a `Display`
/// impl that writes the timestamp as a human-readable string. Currently this
/// assumes the time is within 68 years of 1970; the string will be incorrect
/// after `2038-01-19T03:14:07Z`.
///
/// An `NtpTimestamp` isn't necessarily gathered from a real NTP server.
/// Reported NTP timestamps are allowed to jump backwards and/or be complete
/// nonsense.
///
/// The NTP timestamp of the Unix epoch is available via the constant [`UNIX_EPOCH`].
#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct NtpTimestamp(pub u64);

impl std::fmt::Display for NtpTimestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let date_time: chrono::DateTime<chrono::Local> = (*self).into();
        write!(f, "{}", date_time.format("%FT%T%.3f%:z"),)
    }
}

impl std::fmt::Debug for NtpTimestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Write both the raw and display forms.
        write!(f, "{} /* {} */", self.0, self)
    }
}

impl<TZ> TryFrom<chrono::DateTime<TZ>> for NtpTimestamp
where
    TZ: chrono::TimeZone,
{
    type Error = std::num::TryFromIntError;
    fn try_from(orig: chrono::DateTime<TZ>) -> Result<Self, Self::Error> {
        let epoch_naive = chrono::NaiveDate::from_ymd_opt(1900, 1, 1)
            .unwrap()
            .and_hms_opt(0, 0, 0)
            .unwrap();
        let epoch = chrono::TimeZone::from_local_datetime(&chrono::Utc, &epoch_naive).unwrap();
        let elapsed: chrono::Duration = orig.with_timezone(&chrono::Utc) - epoch;
        let sec_since_epoch: u32 = elapsed.num_seconds().try_into()?;
        let nanos = elapsed.to_std().unwrap().subsec_nanos();
        let frac = f64::from(nanos) / 1e9;
        let frac_int = (frac * f64::from(u32::MAX)).round() as u32;
        let val = (u64::from(sec_since_epoch) << 32) + u64::from(frac_int);
        Ok(NtpTimestamp(val))
    }
}

impl<TZ> From<NtpTimestamp> for chrono::DateTime<TZ>
where
    TZ: chrono::TimeZone,
    chrono::DateTime<TZ>: From<chrono::DateTime<chrono::Utc>>,
{
    fn from(orig: NtpTimestamp) -> Self {
        let since_epoch = orig.0.wrapping_sub(UNIX_EPOCH.0);
        let sec_since_epoch = (since_epoch >> 32) as u32;
        let frac_int = (since_epoch & 0xFFFF_FFFF) as u32;
        let frac = frac_int as f64 / f64::from(u32::MAX);
        let nanos = (frac * 1e9).round() as u32;
        let timedelta: chrono::Duration = chrono::Duration::try_seconds(sec_since_epoch.into())
            .unwrap()
            + chrono::Duration::nanoseconds(nanos.into());
        let date_time = chrono::DateTime::UNIX_EPOCH + timedelta;
        date_time.into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const ORIG_STR: &str = "2024-02-17T21:14:34.013+01:00";

    #[test]
    fn test_ntp_roundtrip() {
        let orig: chrono::DateTime<chrono::Utc> = ORIG_STR.parse().unwrap();
        let ntp_timestamp: NtpTimestamp = orig.try_into().unwrap();
        let display = format!("{ntp_timestamp}");
        let parsed: chrono::DateTime<chrono::Utc> = display.parse().unwrap();
        assert_eq!(orig, parsed);
    }

    #[test]
    fn test_ntp_roundtrip_raw() {
        let orig: chrono::DateTime<chrono::Utc> = ORIG_STR.parse().unwrap();
        let ntp_timestamp: NtpTimestamp = orig.try_into().unwrap();
        let parsed: chrono::DateTime<chrono::Utc> = ntp_timestamp.into();
        assert_eq!(orig, parsed);
    }

    #[test]
    fn test_ntp_decode() {
        let orig: chrono::DateTime<chrono::Utc> = ORIG_STR.parse().unwrap();
        let ntp_timestamp: NtpTimestamp = orig.try_into().unwrap();
        assert_eq!(ntp_timestamp, NtpTimestamp(16824201542114736079));
    }

    fn assert_roundtrip_equal(n0: NtpTimestamp) {
        let dt1 = chrono::DateTime::<chrono::Utc>::from(n0);
        let n1 = NtpTimestamp::try_from(dt1).unwrap();
        let dt2: chrono::DateTime<chrono::Utc> = n1.into();
        assert_eq!(dt1, dt2);
    }

    #[test]
    fn test_now() {
        let dt0 = chrono::Utc::now();
        let n0 = NtpTimestamp::try_from(dt0).unwrap();
        assert_roundtrip_equal(n0);
    }

    #[test]
    fn test_float_rounding() {
        // This magic number was found empirically to fail when conversion to a
        // floating-point fractional second did not round correctly. The bug has
        // now been fixed but this test ensures it does not occur again.
        assert_roundtrip_equal(NtpTimestamp(16834755242908219071));
    }
}

/// A wall time taken from the local machine's realtime clock, used in error reporting.
///
/// Currently this just allows formatting via `Debug` and `Display`.
#[derive(Copy, Clone, Debug)]
pub struct WallTime(chrono::DateTime<chrono::Utc>);

impl WallTime {
    fn now() -> Self {
        Self(chrono::Utc::now())
    }
}

impl Display for WallTime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.format("%FT%T"))
    }
}

/// RTSP connection context.
///
/// This gives enough information to pick out the flow in a packet capture.
#[derive(Copy, Clone, Debug)]
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
        // TODO: this current hardcodes the assumption we are the client.
        // Change if/when adding server code.
        write!(
            f,
            "{}(me)->{}@{}",
            &self.local_addr, &self.peer_addr, &self.established_wall,
        )
    }
}

/// Context of a received message (or read error) within an RTSP connection.
///
/// When paired with a [`ConnectionContext`], this should allow picking the
/// message out of a packet capture.
#[derive(Copy, Clone, Debug)]
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
        write!(f, "{}@{}", self.pos, &self.received_wall)
    }
}

/// Context for an active stream (RTP+RTCP session), either TCP or UDP. Owned version.
#[derive(Copy, Clone, Debug)]
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

#[derive(Copy, Clone, Debug)]
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
        // TODO: this assumes we are the client. Revisit when adding server support.
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
#[derive(Copy, Clone, Debug)]
pub struct PacketContext(PacketContextInner);

impl PacketContext {
    #[doc(hidden)]
    pub fn dummy() -> PacketContext {
        Self(PacketContextInner::Dummy)
    }
}

#[derive(Copy, Clone, Debug)]
enum PacketContextInner {
    Tcp { msg_ctx: RtspMessageContext },
    Udp { received_wall: WallTime },
    Dummy,
}

impl Display for PacketContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            PacketContextInner::Udp { received_wall } => std::fmt::Display::fmt(&received_wall, f),
            PacketContextInner::Tcp { msg_ctx } => std::fmt::Display::fmt(&msg_ctx, f),
            PacketContextInner::Dummy => write!(f, "dummy"),
        }
    }
}

/// Returns the range within `buf` that represents `subset`.
/// If `subset` is empty, returns None; otherwise panics if `subset` is not within `buf`.
pub(crate) fn as_range(buf: &[u8], subset: &[u8]) -> Option<std::ops::Range<usize>> {
    if subset.is_empty() {
        return None;
    }
    let subset_p = subset.as_ptr() as usize;
    let buf_p = buf.as_ptr() as usize;
    let off = match subset_p.checked_sub(buf_p) {
        Some(off) => off,
        None => panic!(
            "{}-byte subset not within {}-byte buf",
            subset.len(),
            buf.len()
        ),
    };
    let end = off + subset.len();
    assert!(end <= buf.len());
    Some(off..end)
}

/// A pair of local UDP sockets used for RTP and RTCP transmission.
///
/// The RTP port is always even, and the RTCP port is always the following (odd) integer.
struct UdpPair {
    rtp_port: u16,
    rtp_socket: UdpSocket,
    rtcp_socket: UdpSocket,
}

impl UdpPair {
    fn for_ip(ip_addr: IpAddr) -> Result<Self, std::io::Error> {
        const MAX_TRIES: usize = 10;
        const ALLOWED_RTP_RANGE: Range<u16> = 5000..65000; // stolen from ffmpeg's defaults.
        let mut rng = rand::thread_rng();
        for i in 0..MAX_TRIES {
            let rtp_port = rng.gen_range(ALLOWED_RTP_RANGE) & !0b1;
            debug_assert!(ALLOWED_RTP_RANGE.contains(&rtp_port));
            let rtp_addr = SocketAddr::new(ip_addr, rtp_port);
            let rtp_socket = match UdpSocket::bind(rtp_addr) {
                Ok(s) => s,
                Err(e) if e.kind() == std::io::ErrorKind::AddrInUse => {
                    trace!(
                        "Try {}/{}: unable to bind RTP addr {:?}",
                        i,
                        MAX_TRIES,
                        rtp_addr
                    );
                    continue;
                }
                Err(e) => return Err(e),
            };
            let rtcp_addr = SocketAddr::new(ip_addr, rtp_port + 1);
            let rtcp_socket = match UdpSocket::bind(rtcp_addr) {
                Ok(s) => s,
                Err(e) if e.kind() == std::io::ErrorKind::AddrInUse => {
                    trace!(
                        "Try {}/{}: unable to bind RTCP addr {:?}",
                        i,
                        MAX_TRIES,
                        rtcp_addr
                    );
                    continue;
                }
                Err(e) => return Err(e),
            };
            return Ok(Self {
                rtp_port,
                rtp_socket,
                rtcp_socket,
            });
        }
        Err(std::io::Error::new(
            std::io::ErrorKind::AddrInUse,
            format!(
                "Unable to find even/odd pair in {}:{}..{} after {} tries",
                ip_addr, ALLOWED_RTP_RANGE.start, ALLOWED_RTP_RANGE.end, MAX_TRIES
            ),
        ))
    }
}

#[cfg(test)]
mod test {
    use std::net::Ipv4Addr;

    use super::*;

    #[test]
    fn local_udp_pair() {
        // Just test that it succeeds.
        UdpPair::for_ip(IpAddr::V4(Ipv4Addr::LOCALHOST)).unwrap();
    }
}
