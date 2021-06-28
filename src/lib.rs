// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use bytes::{Buf, BufMut, Bytes, BytesMut};
use failure::{bail, format_err, Error};
use once_cell::sync::Lazy;
use pretty_hex::PrettyHex;
use rtsp_types::{Data, Message};
use std::convert::TryFrom;
use std::fmt::{Debug, Display};
use std::num::NonZeroU32;

pub mod client;
pub mod codec;

pub static X_ACCEPT_DYNAMIC_RATE: Lazy<rtsp_types::HeaderName> = Lazy::new(|| {
    rtsp_types::HeaderName::from_static_str("x-Accept-Dynamic-Rate").expect("is ascii")
});
pub static X_DYNAMIC_RATE: Lazy<rtsp_types::HeaderName> =
    Lazy::new(|| rtsp_types::HeaderName::from_static_str("x-Dynamic-Rate").expect("is ascii"));

#[derive(Debug)]
pub struct ReceivedMessage {
    pub ctx: Context,
    pub msg: Message<Bytes>,
}

/// A monotonically increasing timestamp within an RTP stream.
/// The [Display] and [Debug] implementations display:
/// *   the bottom 32 bits, as seen in RTP packet headers. This advances at a
///     codec-specified clock rate.
/// *   the full timestamp, with top bits accumulated as RTP packet timestamps wrap around.
/// *   a conversion to RTSP "normal play time" (NPT): zero-based and normalized to seconds.
#[derive(Copy, Clone)]
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
    /// Creates a new timestamp, ensuring `timestamp - start` doesn't underflow.
    pub fn new(timestamp: i64, clock_rate: NonZeroU32, start: u32) -> Result<Self, Error> {
        match timestamp.checked_sub(i64::from(start)) {
            None => bail!("timestamp - start must not underflow"),
            Some(_) => Ok(Timestamp {
                timestamp,
                clock_rate,
                start,
            }),
        }
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

    pub fn try_add(&self, delta: u32) -> Result<Self, Error> {
        // Check for `timestamp` overflow only. We don't need to check for
        // `timestamp - start` underflow because delta is non-negative.
        Ok(Timestamp {
            timestamp: self
                .timestamp
                .checked_add(i64::from(delta))
                .ok_or_else(|| format_err!("overflow on {:?} + {}", &self, delta))?,
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

/// Context of a received message within an RTSP stream.
/// This is meant to help find the correct TCP stream and packet in a matching
/// packet capture.
#[derive(Copy, Clone)]
pub struct Context {
    conn_local_addr: std::net::SocketAddr,
    conn_peer_addr: std::net::SocketAddr,
    conn_established_wall: time::Timespec,
    conn_established: std::time::Instant,

    /// The byte position within the input stream. The bottom 32 bits can be
    /// compared to the TCP sequence number.
    msg_pos: u64,

    /// Time when the application parsed the message. Caveat: this may not
    /// closely match the time on a packet capture if the application is
    /// overloaded (or `CLOCK_REALTIME` jumps).
    msg_received_wall: time::Timespec,
    msg_received: std::time::Instant,
}

impl Context {
    #[doc(hidden)]
    pub fn dummy() -> Self {
        use std::net::{IpAddr, Ipv4Addr, SocketAddr};
        let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
        Self {
            conn_local_addr: addr,
            conn_peer_addr: addr,
            conn_established_wall: time::get_time(),
            conn_established: std::time::Instant::now(),
            msg_pos: 0,
            msg_received_wall: time::get_time(),
            msg_received: std::time::Instant::now(),
        }
    }

    pub fn conn_established(&self) -> std::time::Instant {
        self.conn_established
    }

    pub fn msg_received(&self) -> std::time::Instant {
        self.msg_received
    }

    pub fn msg_pos(&self) -> u64 {
        self.msg_pos
    }
}

impl Debug for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: this current hardcodes the assumption we are the client.
        // Change if/when adding server code.
        write!(
            f,
            "[{}(me)->{}@{} pos={}@{}]",
            &self.conn_local_addr,
            &self.conn_peer_addr,
            time::at(self.conn_established_wall)
                .strftime("%FT%T")
                .map_err(|_| std::fmt::Error)?,
            self.msg_pos,
            time::at(self.msg_received_wall)
                .strftime("%FT%T")
                .map_err(|_| std::fmt::Error)?
        )
    }
}

struct Codec {
    ctx: Context,
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

impl Codec {
    fn parse_msg(&self, src: &mut BytesMut) -> Result<Option<(usize, Message<Bytes>)>, Error> {
        if !src.is_empty() && src[0] == b'$' {
            // Fast path for interleaved data, avoiding MessageRef -> Message<&[u8]> ->
            // Message<Bytes> conversion. This speeds things up quite a bit in practice,
            // avoiding a bunch of memmove calls.
            if src.len() < 4 {
                return Ok(None);
            }
            let channel_id = src[1];
            let len = 4 + usize::from(u16::from_be_bytes([src[2], src[3]]));
            if src.len() < len {
                src.reserve(len - src.len());
                return Ok(None);
            }
            let mut msg = src.split_to(len);
            msg.advance(4);
            return Ok(Some((len, Message::Data(Data::new(channel_id, msg.freeze())))))
        }

        let (msg, len): (Message<&[u8]>, _) = match rtsp_types::Message::parse(src) {
            Ok((m, l)) => (m, l),
            Err(rtsp_types::ParseError::Error) => {
                let snippet = &src[0..std::cmp::min(128, src.len())];
                bail!(
                    "RTSP parse error at {:#?}: next bytes are {:#?}",
                    &self.ctx,
                    snippet.hex_dump()
                )
            }
            Err(rtsp_types::ParseError::Incomplete) => return Ok(None),
        };

        // Map msg's body to a Bytes representation and advance `src`. Awkward:
        // 1.  lifetime concerns require mapping twice: first so the message
        //     doesn't depend on the BytesMut, which needs to be split/advanced;
        //     then to get the proper Bytes body in place post-split.
        // 2.  rtsp_types messages must be AsRef<[u8]>, so we can't use the
        //     range as an intermediate body.
        // 3.  within a match because the rtsp_types::Message enum itself
        //     doesn't have body/replace_body/map_body methods.
        let msg = match msg {
            Message::Request(msg) => {
                let body_range = as_range(src, msg.body());
                let msg = msg.replace_body(rtsp_types::Empty);
                if let Some(r) = body_range {
                    let mut raw_msg = src.split_to(len);
                    raw_msg.advance(r.start);
                    raw_msg.truncate(r.len());
                    Message::Request(msg.replace_body(raw_msg.freeze()))
                } else {
                    src.advance(len);
                    Message::Request(msg.replace_body(Bytes::new()))
                }
            }
            Message::Response(msg) => {
                let body_range = as_range(src, msg.body());
                let msg = msg.replace_body(rtsp_types::Empty);
                if let Some(r) = body_range {
                    let mut raw_msg = src.split_to(len);
                    raw_msg.advance(r.start);
                    raw_msg.truncate(r.len());
                    Message::Response(msg.replace_body(raw_msg.freeze()))
                } else {
                    src.advance(len);
                    Message::Response(msg.replace_body(Bytes::new()))
                }
            }
            Message::Data(_) => unreachable!(),
        };
        Ok(Some((len, msg)))
    }
}

impl tokio_util::codec::Decoder for Codec {
    type Item = ReceivedMessage;
    type Error = failure::Error;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        let (len, msg) = match self.parse_msg(src) {
            Err(e) => return Err(e),
            Ok(None) => return Ok(None),
            Ok(Some((len, msg))) => (len, msg),
        };
        self.ctx.msg_received_wall = time::get_time();
        self.ctx.msg_received = std::time::Instant::now();
        let msg = ReceivedMessage { ctx: self.ctx, msg };
        self.ctx.msg_pos += u64::try_from(len).expect("usize fits in u64");
        Ok(Some(msg))
    }
}

impl tokio_util::codec::Encoder<rtsp_types::Message<bytes::Bytes>> for Codec {
    type Error = failure::Error;

    fn encode(
        &mut self,
        item: rtsp_types::Message<bytes::Bytes>,
        dst: &mut BytesMut,
    ) -> Result<(), Self::Error> {
        let mut w = std::mem::replace(dst, BytesMut::new()).writer();
        item.write(&mut w).expect("bytes Writer is infallible");
        *dst = w.into_inner();
        Ok(())
    }
}
