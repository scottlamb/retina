// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use bytes::Bytes;
//use failure::{bail, format_err, Error};
use once_cell::sync::Lazy;
use rtsp_types::Message;
use std::fmt::{Debug, Display};
use std::num::NonZeroU32;

mod error;
mod rtcp;

#[cfg(test)]
mod testutil;

pub use error::Error;

/// Wraps the supplied `ErrorInt` and returns it as an `Err`.
macro_rules! bail {
    ($e:expr) => {
        return Err(crate::error::Error(Box::new($e)))
    };
}

macro_rules! wrap {
    ($e:expr) => {
        crate::error::Error(Box::new($e))
    };
}

pub mod client;
pub mod codec;
//mod error;
mod tokio;

use error::ErrorInt;

pub static X_ACCEPT_DYNAMIC_RATE: Lazy<rtsp_types::HeaderName> = Lazy::new(|| {
    rtsp_types::HeaderName::from_static_str("x-Accept-Dynamic-Rate").expect("is ascii")
});
pub static X_DYNAMIC_RATE: Lazy<rtsp_types::HeaderName> =
    Lazy::new(|| rtsp_types::HeaderName::from_static_str("x-Dynamic-Rate").expect("is ascii"));

/// A received RTSP message.
#[derive(Debug)]
struct ReceivedMessage {
    ctx: RtspMessageContext,
    msg: Message<Bytes>,
}

/// A monotonically increasing timestamp within an RTP stream.
/// The [Display] and [Debug] implementations display:
/// *   the bottom 32 bits, as seen in RTP packet headers. This advances at a
///     codec-specified clock rate.
/// *   the full timestamp, with top bits accumulated as RTP packet timestamps wrap around.
/// *   a conversion to RTSP "normal play time" (NPT): zero-based and normalized to seconds.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Timestamp {
    /// A timestamp which must be compared to `start`. The top bits are inferred
    /// from wraparounds of 32-bit RTP timestamps. The `i64` itself is not
    /// allowed to overflow/underflow; similarly `timestamp - start` is not
    /// allowed to underflow.
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

pub const UNIX_EPOCH: NtpTimestamp = NtpTimestamp((2_208_988_800) << 32);

/// A wallclock time represented using the format of the Network Time Protocol.
/// This isn't necessarily gathered from a real NTP server. Reported NTP
/// timestamps are allowed to jump backwards and/or be complete nonsense.
#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct NtpTimestamp(pub u64);

impl std::fmt::Display for NtpTimestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let since_epoch = self.0.wrapping_sub(UNIX_EPOCH.0);
        let sec_since_epoch = (since_epoch >> 32) as u32;
        let tm = time::at(time::Timespec {
            sec: i64::from(sec_since_epoch),
            nsec: 0,
        });
        let ms = ((since_epoch & 0xFFFF_FFFF) * 1_000) >> 32;
        let zone_minutes = tm.tm_utcoff.abs() / 60;
        write!(
            f,
            "{}.{:03}{}{:02}:{:02}",
            tm.strftime("%FT%T").map_err(|_| std::fmt::Error)?,
            ms,
            if tm.tm_utcoff > 0 { '+' } else { '-' },
            zone_minutes / 60,
            zone_minutes % 60
        )
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
/// Currently this just allows formatting via `Debug` and `Display`.
#[derive(Copy, Clone, Debug)]
pub struct WallTime(time::Timespec);

impl WallTime {
    fn now() -> Self {
        Self(time::get_time())
    }
}

impl Display for WallTime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(
            &time::at(self.0)
                .strftime("%FT%T")
                .map_err(|_| std::fmt::Error)?,
            f,
        )
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
    established: std::time::Instant,
}

impl ConnectionContext {
    #[doc(hidden)]
    pub fn dummy() -> Self {
        use std::net::{IpAddr, Ipv4Addr, SocketAddr};
        let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
        Self {
            local_addr: addr,
            peer_addr: addr,
            established_wall: WallTime::now(),
            established: std::time::Instant::now(),
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
