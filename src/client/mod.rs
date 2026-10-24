// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTSP client: connect to a server via [`Session`].
//!
//! [`Session`] does its I/O via tokio. Its protocol logic is also available
//! without any I/O or runtime, for callers who do their own, as
//! [`SessionCore`] and [`TeardownCore`]. The `polling-client` example drives
//! them with plain non-blocking sockets and a `poll(2)`-style loop. These
//! require the `unstable-sans-io` feature and are exempt from semver: they may
//! change in any release.

use std::convert::TryFrom;
use std::io;
use std::mem::MaybeUninit;
use std::net::SocketAddr;
use std::num::NonZeroU32;
use std::sync::{Arc, Mutex};
use std::task::Poll;
use std::time::Instant;
use std::{fmt::Debug, num::NonZeroU16, pin::Pin};

#[cfg(feature = "unstable-sans-io")]
pub use self::channel_mapping::ChannelType;
#[cfg(not(feature = "unstable-sans-io"))]
use self::channel_mapping::ChannelType;
use self::playing::PlayingCore;
#[cfg(not(feature = "unstable-sans-io"))]
use self::session_core::{SessionCore, SessionEvent, SetupTransport};
#[cfg(feature = "unstable-sans-io")]
pub use self::session_core::{SessionCore, SessionEvent, SetupTransport, UdpTransmit};
#[cfg(feature = "unstable-sans-io")]
pub use self::teardown::{TeardownAction, TeardownCore};
pub use self::timeline::Timeline;
use crate::inputs::Input as _;
use crate::rtsp::msg::{self as msg, OwnedMessage};
use bytes::Bytes;
use futures::{Future, ready};
use log::{debug, warn};
use tokio::net::UdpSocket;
use url::Url;

use crate::{Error, ErrorInt, RtspMessageContext, StreamContext};

mod channel_mapping;
mod conn;
pub(crate) mod parse;
mod playing;
mod receiver_report;

/// Internal API, public for a benchmark only.
#[doc(hidden)]
pub mod rtp;

mod session_core;
mod teardown;
mod timeline;

/// Assumed expiration time for stale live555 TCP sessions (case #2 of "Stale
/// sessions" in [`SessionGroup`]).
///
/// This constant is taken from
/// [here](https://github.com/rgaufman/live555/blob/41a5ec5f65bd626918a43951f743b4c9ffc52289/liveMedia/include/RTSPServer.hh#L35).
const LIVE555_EXPIRATION_SEC: u64 = 65;

/// A stale RTP session. See explanation at [`SessionGroup`].
struct StaleSession {
    seqnum: u64,

    /// The progress of the `TEARDOWN`, for [`SessionGroup::await_teardown`].
    teardown: StaleTeardown,

    maybe_playing: bool,
    has_tcp: bool,

    /// Upper bound of advertised expiration time.
    expires: Instant,
}

/// The progress of a stale session's `TEARDOWN`.
enum StaleTeardown {
    /// None is possible: the session was discovered via the live555 bug, so
    /// its id is unknown.
    Impossible,

    /// A [`TeardownCore`] is working on it, and no attempt has failed yet.
    Pending,

    /// A [`TeardownCore`] is working on it (or was dropped), and the latest
    /// attempt failed.
    Failed(Error),
}

/// A group of sessions, currently used only to track stale sessions.
///
/// Sessions are associated with a group via [`SessionOptions::session_group`].
///
/// This is an experimental API which may change in an upcoming Retina version.
///
/// ## Stale sessions
///
/// Stale sessions are ones which are no longer active on the client side
/// (no [`Session`] struct exists) but may still be in state `Ready`, `Playing`,
/// or `Recording` on the server. The client has neither seen a `TEARDOWN`
/// response nor believes they have reached their expiration time. They are
/// tracked in two cases:
///
/// 1.  Sessions being torn down via a [`TeardownCore`], including dropped
///     [`Session`]s, if the [`TeardownPolicy`] says to do so and a valid
///     `SETUP` response has been received.
///
///     The `TeardownCore` (for a dropped `Session`, driven by a tokio
///     background task) is responsible for attempting a `TEARDOWN` and
///     cleaning the session after success or expiration.
///     [`SessionGroup::await_teardown`] can be used to wait out this process.
///
///     In general, the tracked expiration time is worst-case. The exception is
///     if the sender hasn't responded to a keepalive request. In that case
///     there's theoretically no bound on when the server could see the request
///     and extend the session. Retina ignores this possibility.
///
/// 2.  TCP sessions discovered via unexpected RTSP interleaved data
///     packets. These are assumed to be due to a live555 bug in which
///     data continues to be sent on a stale file descriptor after a
///     connection is closed. The sessions' packets may be sent to unrelated
///     (even unauthenticated and/or non-RTSP!) connections after the file
///     descriptor is reused.  These sessions may have been started by a process
///     unknown to us and their session id is unknown, so in general it is not
///     possible to send a `TEARDOWN`.
///
///     These sessions are assumed to expire 65 seconds after discovery, a
///     constant taken from old live555 code.
///
/// Expired sessions are forgotten lazily, as the group is examined.
///
/// ## Time
///
/// Expiration times are [`std::time::Instant`]s, computed from the `now`
/// arguments supplied to [`SessionCore`] and [`TeardownCore`] (or, for
/// [`Session`], from tokio's clock). Supply `now` from the same clock to
/// [`SessionGroup::stale_sessions`].
///
/// ## Granularity
///
/// A `SessionGroup` can be of any granularity, but a typical use is to ensure
/// there are no stale sessions before starting a fresh session (see
/// [`SessionGroup::stale_sessions`] and `SessionGroup::await_stale_sessions`).
/// Groups should be sized to match that idea. If connecting to a live555 server
/// affected by the stale TCP session bug, it might be wise to have one group
/// per server, so that all such sessions can be drained before initiating new
/// connections. Otherwise it might be useful to have one group per describe
/// URL (potentially several per server) and have at most one active session per
/// URL.
#[derive(Default)]
pub struct SessionGroup {
    name: Option<String>,
    inner: Mutex<SessionGroupInner>,
}

#[derive(Default)]
struct SessionGroupInner {
    next_seqnum: u64,

    /// Stale sessions, unordered.
    sessions: Vec<StaleSession>,

    /// Incremented on every change, for [`SessionGroup::changed`].
    version: u64,

    /// Wakers to wake on the next change.
    wakers: Vec<std::task::Waker>,
}

/// The overall status of stale sessions that may be in state `Playing` and
/// belong to a particular group.
pub struct StaleSessionStatus {
    /// The maximum expire time of any such sessions.
    pub max_expires: Option<Instant>,

    /// The total number of sessions.
    pub num_sessions: usize,

    /// The `SessionGroupInner::next_seqnum` value as of when this was
    /// created, for `SessionGroup::await_stale_sessions`.
    next_seqnum: u64,
}

impl SessionGroup {
    /// Returns this group with an assigned name.
    ///
    /// Typically called before placing into an `Arc`, e.g.
    /// `Arc::new(SessionGroup::default().named("foo"))`.
    pub fn named(self, name: String) -> Self {
        SessionGroup {
            name: Some(name),
            ..self
        }
    }

    /// Returns the name of this session group, if any.
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    /// An identifier for this session group, for use in log messages.
    ///
    /// Currently uses the name if set, a pointer address otherwise.
    fn debug_id(&self) -> impl Debug + use<> {
        self.name.clone().unwrap_or_else(|| format!("{:p}", &self))
    }

    /// Locks the group, forgetting sessions which have expired as of `now`.
    fn lock_pruned(&self, now: Instant) -> std::sync::MutexGuard<'_, SessionGroupInner> {
        let mut l = self.inner.lock().unwrap();
        let before = l.sessions.len();
        l.sessions.retain(|s| s.expires > now);
        if l.sessions.len() != before {
            log::debug!(
                "Session group {:?} forgot {} expired sessions",
                self.debug_id(),
                before - l.sessions.len()
            );
            l.changed();
        }
        l
    }

    /// Returns the status of stale sessions in this group as of `now`.
    ///
    /// Currently this only returns information about sessions which may be in
    /// state `Playing`. That is, ones for which Retina has either sent a
    /// `PLAY` request (regardless of whether it received a response) or
    /// discovered as described in [`SessionGroup`].
    ///
    /// The caller might use this in a loop with `await_stale_sessions` to sleep
    /// until there are no such sessions, logging updates
    pub fn stale_sessions(&self, now: Instant) -> StaleSessionStatus {
        let l = self.lock_pruned(now);
        let playing = l.sessions.iter().filter(|s| s.maybe_playing);
        StaleSessionStatus {
            max_expires: playing.clone().map(|s| s.expires).max(),
            num_sessions: playing.count(),
            next_seqnum: l.next_seqnum,
        }
    }

    /// Returns a future which completes on the next change to the group: a
    /// session added or removed, or a failed `TEARDOWN` attempt.
    ///
    /// This doesn't depend on any particular async runtime. Expiration isn't
    /// a change; to wait until sessions expire, race this with a sleep until
    /// [`StaleSessionStatus::max_expires`], then check
    /// [`SessionGroup::stale_sessions`] again.
    pub fn changed(&self) -> impl Future<Output = ()> + Send + '_ {
        let version = self.inner.lock().unwrap().version;
        std::future::poll_fn(move |cx| {
            let mut l = self.inner.lock().unwrap();
            if l.version != version {
                return Poll::Ready(());
            }
            if !l.wakers.iter().any(|w| w.will_wake(cx.waker())) {
                l.wakers.push(cx.waker().clone());
            }
            Poll::Pending
        })
    }

    /// Waits for a reasonable attempt at `TEARDOWN` on all stale sessions that
    /// exist as of when this method is called, returning an error if any
    /// session's reasonable attempts fail.
    ///
    /// This has no timeout other than the sessions' expiration times. The
    /// caller can wrap the call in a timeout for an earlier time.
    ///
    /// Currently on `Session::drop`, a `TEARDOWN` loop is started in the
    /// background. This method waits for an attempt on an existing connection
    /// (if any) and in some cases the first attempt on a fresh connection.
    /// Retina may continue sending more attempts even after this method
    /// returns.
    ///
    /// Ignores the discovered live555 bug sessions, as it's impossible to send
    /// a `TEARDOWN` without knowing the session id. If desired, the caller can
    /// learn of the existence of the sessions through
    /// [`SessionGroup::stale_sessions`] and sleep until they expire.
    ///
    /// This doesn't depend on any particular async runtime, but it relies on
    /// something driving each session's [`TeardownCore`]. One dropped before
    /// finishing counts as a failed attempt.
    pub async fn await_teardown(&self) -> Result<(), Error> {
        let seqnums: Vec<u64> = {
            let l = self.inner.lock().unwrap();
            l.sessions
                .iter()
                .filter(|s| !matches!(s.teardown, StaleTeardown::Impossible))
                .map(|s| s.seqnum)
                .collect()
        };

        let mut overall_result = Ok(());
        for seqnum in seqnums {
            loop {
                let changed = self.changed();
                let r = {
                    let l = self.inner.lock().unwrap();
                    match l.sessions.iter().find(|s| s.seqnum == seqnum) {
                        // Removed, after success or giving up.
                        None => Some(Ok(())),
                        Some(s) => match &s.teardown {
                            StaleTeardown::Failed(e) => Some(Err(e.clone())),
                            _ => None,
                        },
                    }
                };
                if let Some(r) = r {
                    overall_result = overall_result.and(r);
                    break;
                }
                changed.await;
            }
        }
        overall_result
    }

    /// Waits for all of the sessions described by `status` to expire or be torn down.
    pub async fn await_stale_sessions(&self, status: &StaleSessionStatus) {
        loop {
            let changed = self.changed();
            let max_expires = {
                let now = tokio::time::Instant::now().into_std();
                let l = self.lock_pruned(now);
                let mut relevant = l
                    .sessions
                    .iter()
                    .filter(|s| s.maybe_playing && s.seqnum < status.next_seqnum);
                let max_expires = relevant.clone().map(|s| s.expires).max();
                log::trace!(
                    "Session group {:?} has {} relevant sessions numbered < {}",
                    self.debug_id(),
                    relevant.by_ref().count(),
                    status.next_seqnum
                );
                match max_expires {
                    None => return,
                    Some(e) => e,
                }
            };
            tokio::select! {
                _ = changed => {},
                _ = tokio::time::sleep_until(tokio::time::Instant::from_std(max_expires)) => {},
            }
        }
    }

    /// Adds a stale session, returning its seqnum.
    fn add(
        &self,
        now: Instant,
        teardown: StaleTeardown,
        maybe_playing: bool,
        has_tcp: bool,
        expires: Instant,
    ) -> u64 {
        let mut l = self.lock_pruned(now);
        let seqnum = l.next_seqnum;
        l.next_seqnum += 1;
        l.sessions.push(StaleSession {
            seqnum,
            teardown,
            maybe_playing,
            has_tcp,
            expires,
        });
        l.changed();
        seqnum
    }

    /// Records a failed `TEARDOWN` attempt for the session with `seqnum`, if
    /// it's still tracked.
    fn note_teardown_failure(&self, seqnum: u64, e: Error) {
        let mut l = self.inner.lock().unwrap();
        if let Some(s) = l.sessions.iter_mut().find(|s| s.seqnum == seqnum) {
            s.teardown = StaleTeardown::Failed(e);
            l.changed();
        }
    }

    /// Removes the session with `seqnum` removing true iff it existed. Notifies waiters.
    fn try_remove_seqnum(&self, seqnum: u64) -> bool {
        let mut l = self.inner.lock().unwrap();
        let i = l.sessions.iter().position(|s| s.seqnum == seqnum);
        match i {
            Some(i) => {
                l.sessions.swap_remove(i);
                l.changed();
                true
            }
            None => false,
        }
    }
}

impl SessionGroupInner {
    /// Notes a change, waking anyone waiting via [`SessionGroup::changed`].
    fn changed(&mut self) {
        self.version += 1;
        for w in self.wakers.drain(..) {
            w.wake();
        }
    }
}

/// Policy for when to send `TEARDOWN` requests.
///
/// Specify via [`SessionOptions::teardown`].
#[derive(Copy, Clone, Debug, Default, derive_more::Display)]
pub enum TeardownPolicy {
    /// Automatic.
    ///
    /// The current policy is as follows:
    ///
    /// *   Like `Always` if `Transport::Udp` is selected or if the server
    ///     appears to be using a using a [buggy live555
    ///     version](https://github.com/scottlamb/retina/issues/17) in which data
    ///     continues to be sent on a stale file descriptor after a connection is
    ///     closed.
    /// *   Otherwise (TCP, server not known to be buggy), tries a single `TEARDOWN`
    ///     on the existing connection. This is just in case; some servers appear
    ///     to be buggy but don't advertise buggy versions. After the single attempt,
    ///     closes the TCP connection and considers the session done.
    #[default]
    #[display("auto")]
    Auto,

    /// Always send `TEARDOWN` requests, regardless of transport.
    ///
    /// This tries repeatedly to tear down the session until success or expiration;
    /// [`SessionGroup`] will track it also.
    #[display("always")]
    Always,

    /// Never send `TEARDOWN` or track stale sessions.
    #[display("never")]
    Never,
}

impl std::str::FromStr for TeardownPolicy {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "auto" => TeardownPolicy::Auto,
            "never" => TeardownPolicy::Never,
            "always" => TeardownPolicy::Always,
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "bad TeardownPolicy {s}; expected auto, never, or always"
            ))),
        })
    }
}

/// Policy for handling the `rtptime` parameter normally seen in the `RTP-Info` header.
/// This parameter is used to map each stream's RTP timestamp to NPT ("normal play time"),
/// allowing multiple streams to be played in sync.
#[derive(Copy, Clone, Debug, Default, derive_more::Display)]
pub enum InitialTimestampPolicy {
    /// Default policy: currently `Require` when playing multiple streams,
    /// `Ignore` otherwise.
    #[default]
    #[display("default")]
    Default,

    /// Require the `rtptime` parameter be present and use it to set NPT. Use
    /// when accurate multi-stream NPT is important.
    #[display("require")]
    Require,

    /// Ignore the `rtptime` parameter and assume the first received packet for
    /// each stream is at NPT 0. Use with cameras that are known to set
    /// `rtptime` incorrectly.
    #[display("ignore")]
    Ignore,

    /// Use the `rtptime` parameter when playing multiple streams if it's
    /// specified for all of them; otherwise assume the first received packet
    /// for each stream is at NPT 0.
    #[display("permissive")]
    Permissive,
}

impl std::str::FromStr for InitialTimestampPolicy {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "default" => InitialTimestampPolicy::Default,
            "require" => InitialTimestampPolicy::Require,
            "ignore" => InitialTimestampPolicy::Ignore,
            "permissive" => InitialTimestampPolicy::Permissive,
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "bad InitialTimestampPolicy {s}; \
                 expected default, require, ignore or permissive"
            ))),
        })
    }
}

/// Policy for handling the `seq` parameter normally seen in the `RTP-Info` header.
#[derive(Copy, Clone, Debug, Default, derive_more::Display)]
#[non_exhaustive]
pub enum InitialSequenceNumberPolicy {
    /// Default policy: currently same as `IgnoreSuspiciousValues`.
    #[default]
    #[display("default")]
    Default,

    /// Always respect the value in the header if present.
    #[display("respect")]
    Respect,

    /// Ignore `0` and `1` values, which we consider "suspicious".
    ///
    /// Some cameras appear to send these fixed values then a completely
    /// different sequence number in the first RTP packet.
    ///
    /// *   The Hikvision DS-2CD2032-I appears to always send `seq=0` on its
    ///     metadata stream.
    /// *   The Tapo C320WS appears to always send `seq=1` in all streams.
    #[display("ignore-suspicious-values")]
    IgnoreSuspiciousValues,

    /// Always ignore, starting the sequence number from observed RTP packets.
    #[display("ignore")]
    Ignore,
}

impl std::str::FromStr for InitialSequenceNumberPolicy {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "default" => InitialSequenceNumberPolicy::Default,
            "respect" => InitialSequenceNumberPolicy::Respect,
            "ignore-suspicious-values" => InitialSequenceNumberPolicy::IgnoreSuspiciousValues,
            "ignore" => InitialSequenceNumberPolicy::Ignore,
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "bad InitialSequenceNumberPolicy {s}; \
                 expected default, respect, ignore-suspicious-values, or ignore"
            ))),
        })
    }
}

/// Policy for handling unknown `ssrc` value in RTCP messages.
#[derive(Copy, Clone, Debug, Default, derive_more::Display)]
#[non_exhaustive]
pub enum UnknownRtcpSsrcPolicy {
    /// Default policy: currently same as `DropPackets`.
    #[default]
    #[display("default")]
    Default,

    /// Abort the session on encountering an unknown `ssrc`.
    #[display("abort-session")]
    AbortSession,

    /// Drop RTCP packets with an unknown `ssrc`.
    #[display("drop-packets")]
    DropPackets,

    /// Process the packets as if they had the expected `ssrc`.
    #[display("process-packets")]
    ProcessPackets,
}

impl std::str::FromStr for UnknownRtcpSsrcPolicy {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "default" => UnknownRtcpSsrcPolicy::Default,
            "abort-session" => UnknownRtcpSsrcPolicy::AbortSession,
            "drop-packets" => UnknownRtcpSsrcPolicy::DropPackets,
            "process-packets" => UnknownRtcpSsrcPolicy::ProcessPackets,
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "bad UnknownRtcpSsrcPolicy {s}; \
                 expected default, abort-session, drop-packets, or process-packets"
            ))),
        })
    }
}

/// Options which must be known right as a session is created.
///
/// Decisions which can be deferred are in [`SetupOptions`] or [`PlayOptions`] instead.
#[derive(Default)]
pub struct SessionOptions {
    creds: Option<Credentials>,
    user_agent: Option<Box<str>>,
    session_group: Option<Arc<SessionGroup>>,
    teardown: TeardownPolicy,
    unassigned_channel_data: UnassignedChannelDataPolicy,
    session_id: SessionIdPolicy,
    max_message_size: Option<usize>,
    receiver_reports: ReceiverReportPolicy,
    bind_addr: Option<std::net::IpAddr>,
    backchannel: bool,
}

/// Policy for handling data received on unassigned RTSP interleaved channels.
#[derive(Copy, Clone, Default, derive_more::Display)]
pub enum UnassignedChannelDataPolicy {
    /// Automatic (default).
    ///
    /// The current policy (which may change) is as follows:
    ///
    /// *   if the server has sent a SDP `tool` attribute for which
    ///     [`Tool::has_live555_tcp_bug`] is true, use `AssumeStaleSession`.
    /// *   otherwise (prior to receiving the `DESCRIBE` response, if there was
    ///     no tool attribute, or if it does not match the known pattern),
    ///     use `Ignore`.
    #[default]
    #[display("auto")]
    Auto,

    /// Assume the data is due to the live555 stale TCP session bug described
    /// in "Stale sessions" under [`SessionGroup`].
    ///
    /// This session will return error, and the `SessionGroup` will track the
    /// expiration of a stale session.
    #[display("assume-stale-session")]
    AssumeStaleSession,

    /// Returns an error.
    #[display("error")]
    Error,

    /// Ignores the data.
    ///
    /// Some broken IP cameras appear to have some default assignment of streams
    /// to interleaved channels. If there is no `SETUP` for that stream before
    /// `PLAY`, they will send data anyway, on this channel. In this mode, such
    /// data messages are ignored.
    #[display("ignore")]
    Ignore,
}

impl std::str::FromStr for UnassignedChannelDataPolicy {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "auto" => UnassignedChannelDataPolicy::Auto,
            "assume-stale-session" => UnassignedChannelDataPolicy::AssumeStaleSession,
            "error" => UnassignedChannelDataPolicy::Error,
            "ignore" => UnassignedChannelDataPolicy::Ignore,
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "bad UnassignedChannelDataPolicy {s}; expected auto, assume-stale-session, error, \
                 or ignore"
            ))),
        })
    }
}

/// Policy for handling the session ID returned by the server in response to
/// `SETUP` requests.
#[derive(Copy, Clone, Debug, Default, derive_more::Display)]
pub enum SessionIdPolicy {
    /// Default policy: currently `RequireMatch`.
    #[default]
    #[display("default")]
    Default,

    /// Requires the server to return the same session ID for all `SETUP`
    /// requests in the session.
    #[display("require-match")]
    RequireMatch,

    /// Uses the session ID returned from the first `SETUP` request and ignores
    /// any subsequent changes. Required for some broken cameras.
    #[display("use-first")]
    UseFirst,
}

impl std::str::FromStr for SessionIdPolicy {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "default" => SessionIdPolicy::Default,
            "require-match" => SessionIdPolicy::RequireMatch,
            "use-first" => SessionIdPolicy::UseFirst,
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "bad SessionIdPolicy {s}; \
                 expected default, require-match or use-first"
            ))),
        })
    }
}

/// Policy for sending RTCP receiver reports to the server.
///
/// Receiver reports, as described in [RFC 3550 section
/// 6.4.2](https://datatracker.ietf.org/doc/html/rfc3550#section-6.4.2), tell
/// the server about packet loss and jitter. RFC 3550 section 6 says this
/// feedback "SHOULD be used in all environments".
///
/// Reports cover only streams Retina receives. A backchannel stream (see
/// [`SessionOptions::backchannel`]) gets none; Retina describes the media it
/// sends there in RTCP sender reports instead.
///
/// Specify via [`SessionOptions::receiver_reports`].
#[derive(Copy, Clone, Debug, Default, derive_more::Display)]
#[non_exhaustive]
pub enum ReceiverReportPolicy {
    /// Default policy: currently `Never`.
    #[default]
    #[display("default")]
    Default,

    /// Never send receiver reports.
    #[display("never")]
    Never,

    /// Send receiver reports while playing, for each stream on its RTCP
    /// interleaved channel or UDP port, about every 5 seconds.
    #[display("always")]
    Always,
}

impl ReceiverReportPolicy {
    fn enabled(self) -> bool {
        match self {
            ReceiverReportPolicy::Default | ReceiverReportPolicy::Never => false,
            ReceiverReportPolicy::Always => true,
        }
    }
}

impl std::str::FromStr for ReceiverReportPolicy {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "default" => ReceiverReportPolicy::Default,
            "never" => ReceiverReportPolicy::Never,
            "always" => ReceiverReportPolicy::Always,
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "bad ReceiverReportPolicy {s}; expected default, never, or always"
            ))),
        })
    }
}

/// The RTP packet transport to request.
///
/// Defaults to `Transport::Tcp`.
#[derive(Clone, Debug, derive_more::Display)]
#[non_exhaustive]
pub enum Transport {
    /// Sends RTP packets over the RTSP TCP connection via interleaved data.
    #[display("tcp")]
    Tcp(TcpTransportOptions),

    /// Sends RTP packets over UDP (experimental).
    ///
    /// This support is currently only suitable for a LAN for a couple reasons:
    /// *   There's no reorder buffer, so out-of-order packets are all dropped.
    /// *   RTCP RRs (receiver reports) aren't sent by default, so servers won't
    ///     have the correct information to measure packet loss and pace packets
    ///     appropriately. See [`SessionOptions::receiver_reports`].
    #[display("udp")]
    Udp(UdpTransportOptions),
}

impl Default for Transport {
    fn default() -> Self {
        Transport::Tcp(TcpTransportOptions::default())
    }
}

impl std::str::FromStr for Transport {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "tcp" => Transport::Tcp(TcpTransportOptions::default()),
            "udp" => Transport::Udp(UdpTransportOptions::default()),
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "bad Transport {s}; \
                 expected tcp or udp"
            ))),
        })
    }
}

/// Per-stream TCP transport options (placeholder for future expansion).
#[derive(Clone, Default, Debug)]
#[non_exhaustive]
pub struct TcpTransportOptions;

/// Per-stream UDP transport options (placeholder for future expansion).
#[derive(Clone, Default, Debug)]
#[non_exhaustive]
pub struct UdpTransportOptions;

impl SessionOptions {
    /// Uses the given credentials when/if the server requests digest authentication.
    #[inline]
    pub fn creds(mut self, creds: Option<Credentials>) -> Self {
        self.creds = creds;
        self
    }

    /// Binds outgoing connections (the RTSP TCP connection, and UDP data sockets when using UDP
    /// transport) to this local address. Useful when the host has several local addresses and the
    /// OS would otherwise pick a source address the server has no route back to (e.g. a link-local
    /// address beside a routable one). The port is chosen by the OS.
    pub fn bind(mut self, bind_addr: Option<std::net::IpAddr>) -> Self {
        self.bind_addr = bind_addr;
        self
    }

    /// Sends the given user agent string with each request.
    pub fn user_agent(mut self, user_agent: String) -> Self {
        self.user_agent = if user_agent.is_empty() {
            None
        } else {
            Some(user_agent.into_boxed_str())
        };
        self
    }

    pub fn session_group(mut self, session_group: Arc<SessionGroup>) -> Self {
        self.session_group = Some(session_group);
        self
    }

    pub fn teardown(mut self, teardown: TeardownPolicy) -> Self {
        self.teardown = teardown;
        self
    }

    pub fn unassigned_channel_data(mut self, policy: UnassignedChannelDataPolicy) -> Self {
        self.unassigned_channel_data = policy;
        self
    }

    pub fn session_id(mut self, policy: SessionIdPolicy) -> Self {
        self.session_id = policy;
        self
    }

    /// Limits the size in bytes (head and body combined) of each RTSP
    /// response (or request) read from the server.
    ///
    /// A larger message fails the session with an RTSP framing error rather
    /// than being buffered in full. The limit is checked as the head arrives
    /// and against its `Content-Length` before the body is read. It doesn't
    /// apply to interleaved data messages, which are inherently limited to a
    /// 4-byte head and a body under 64 KiB.
    ///
    /// There's no limit by default. Real servers' responses are small; a
    /// `DESCRIBE` response is typically a few KiB.
    pub fn max_message_size(mut self, max_message_size: usize) -> Self {
        self.max_message_size = Some(max_message_size);
        self
    }

    /// Sets the policy for sending RTCP receiver reports.
    ///
    /// See [`ReceiverReportPolicy`].
    pub fn receiver_reports(mut self, policy: ReceiverReportPolicy) -> Self {
        self.receiver_reports = policy;
        self
    }

    fn get_max_message_size(&self) -> usize {
        self.max_message_size.unwrap_or(usize::MAX)
    }

    /// Requests an ONVIF backchannel: media sent from the client to the server,
    /// such as audio for a camera's speaker. Defaults to false.
    ///
    /// When true, the `DESCRIBE` request carries the `Require:
    /// www.onvif.org/ver20/backchannel` header defined in the [ONVIF Streaming
    /// Specification](https://www.onvif.org/specs/stream/ONVIF-Streaming-Spec.pdf)
    /// section 5.3. A server which supports it adds media marked
    /// `a=sendonly`, such as audio for its speaker; these appear in
    /// [`Session::streams`] with [`Stream::direction`]
    /// [`StreamDirection::Sending`]. Set one up with [`Session::setup`] (TCP
    /// only) alongside the streams to receive, then send packets via
    /// [`Session::queue_rtp`]. The `SETUP` of a sending stream and the
    /// following `PLAY` and `TEARDOWN` requests also carry the `Require`
    /// header.
    ///
    /// A server which doesn't understand the header fails the `DESCRIBE` with
    /// status `551 Option not supported` (section 5.3.2); the error's
    /// description then suggests the backchannel as the cause. Retina doesn't
    /// retry. The spec says the client can try again without the backchannel;
    /// callers can check [`Error::status_code`] to decide.
    ///
    /// A failed `SETUP` of a sending stream, as of any stream, leaves it
    /// unused and the session usable: the caller may go on to set up others
    /// and `PLAY` without it.
    #[cfg(feature = "unstable-send")]
    pub fn backchannel(mut self, backchannel: bool) -> Self {
        self.backchannel = backchannel;
        self
    }
}

/// Per-stream options decided at `SETUP` time.
#[derive(Default)]
pub struct SetupOptions {
    transport: Transport,
}

impl SetupOptions {
    /// Sets the underlying transport to use.
    #[inline]
    pub fn transport(mut self, transport: Transport) -> Self {
        self.transport = transport;
        self
    }
}

/// Options which must be decided at `PLAY` time.
///
/// These are mostly adjustments for non-compliant server implementations.
/// See also [`SessionOptions`] for options which must be decided earlier.
#[derive(Default)]
pub struct PlayOptions {
    initial_timestamp: InitialTimestampPolicy,
    initial_seq: InitialSequenceNumberPolicy,
    enforce_timestamps_with_max_jump_secs: Option<NonZeroU32>,
    unknown_rtcp_ssrc: UnknownRtcpSsrcPolicy,
}

impl PlayOptions {
    /// Sets the policy for handling the `rtptime` parameter normally seem in the `RTP-Info` header.
    pub fn initial_timestamp(self, initial_timestamp: InitialTimestampPolicy) -> Self {
        Self {
            initial_timestamp,
            ..self
        }
    }

    pub fn initial_seq(self, initial_seq: InitialSequenceNumberPolicy) -> Self {
        Self {
            initial_seq,
            ..self
        }
    }

    pub fn unknown_rtcp_ssrc(self, unknown_rtcp_ssrc: UnknownRtcpSsrcPolicy) -> Self {
        Self {
            unknown_rtcp_ssrc,
            ..self
        }
    }

    /// If the `RTP-Time` specifies `seq=0` or `seq=1`, ignore it.
    ///
    /// `ignore_zero_seq(true)` is an outdated spelling of
    /// `initial_seq(InitialSequenceNumberPolicy::IgnoreSuspiciousValues)`,
    /// which is currently the default anyway.
    #[deprecated]
    pub fn ignore_zero_seq(self, ignore_zero_seq: bool) -> Self {
        Self {
            initial_seq: match ignore_zero_seq {
                true => InitialSequenceNumberPolicy::IgnoreSuspiciousValues,
                false => InitialSequenceNumberPolicy::Respect,
            },
            ..self
        }
    }

    /// Enforces that timestamps are non-decreasing and jump forward by no more
    /// than the given number of seconds.
    ///
    /// By default, no enforcement is done, and computed [crate::Timestamp]
    /// values will go backward if subsequent 32-bit RTP timestamps differ by
    /// more than `i32::MAX`.
    pub fn enforce_timestamps_with_max_jump_secs(self, secs: NonZeroU32) -> Self {
        Self {
            enforce_timestamps_with_max_jump_secs: Some(secs),
            ..self
        }
    }
}

#[derive(Debug)]
pub(crate) struct Presentation {
    pub streams: Box<[Stream]>,
    base_url: Url,
    pub control: Url,
    tool: Option<Tool>,
}

/// The server's version as declared in the `DESCRIBE` response's `a:tool` SDP attribute.
#[derive(Clone, Eq, PartialEq)]
pub struct Tool(Box<str>);

impl Tool {
    pub fn new(raw: &str) -> Self {
        Self(raw.into())
    }

    /// Returns if the given tool is known to be a live555 version that causes
    /// the stale TCP sessions described at [`SessionGroup`].
    pub fn has_live555_tcp_bug(&self) -> bool {
        if let Some(version) = self.0.strip_prefix("LIVE555 Streaming Media v") {
            version > "0000.00.00" && version < "2017.06.04"
        } else {
            false
        }
    }
}

impl std::fmt::Debug for Tool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&*self.0, f)
    }
}

impl std::ops::Deref for Tool {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(feature = "unstable-send")]
pub use direction::StreamDirection;
#[cfg(not(feature = "unstable-send"))]
pub(crate) use direction::StreamDirection;

/// Lets [`StreamDirection`] be public only with the `unstable-send` feature.
mod direction {
    /// The direction in which a [`Stream`](super::Stream)'s media flows, from
    /// the client's point of view.
    ///
    /// See [`Stream::direction`](super::Stream::direction).
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    #[non_exhaustive]
    pub enum StreamDirection {
        /// The server sends media; Retina receives it via
        /// [`Session<Playing>::next_item`](super::Session::next_item). This is the usual case.
        Receiving,

        /// Retina sends media to the server via [`Session<Playing>::queue_rtp`](super::Session::queue_rtp).
        ///
        /// This is an ONVIF backchannel stream ([ONVIF Streaming
        /// Specification](https://www.onvif.org/specs/stream/ONVIF-Streaming-Spec.pdf)
        /// section 5.3). A stream is sending if the backchannel was requested via
        /// [`SessionOptions::backchannel`](super::SessionOptions::backchannel) and the server's `DESCRIBE` response
        /// marks its media description `a=sendonly`, which ONVIF uses for media
        /// sent from the client to the server (section 5.3.2). A media description
        /// without a direction attribute has the session's ([RFC 8866 section
        /// 6.7](https://datatracker.ietf.org/doc/html/rfc8866#section-6.7)).
        Sending,
    }
}

/// Information about a stream offered within a presentation.
///
/// Currently if multiple formats are offered, this only describes the first.
pub struct Stream {
    state: StreamState,

    // See the matching accessors for descriptions of these fields.
    media: Box<str>,
    encoding_name: Box<str>,
    rtp_payload_type: u8,
    clock_rate_hz: u32,
    channels: Option<NonZeroU16>,
    framerate: Option<f32>,
    control: Option<Url>,
    direction: StreamDirection,

    /// The format-specific parameters from the SDP `fmtp` attribute.
    fmtp: Option<Box<str>>,

    /// Codec parameters as described in the SDP.
    parameters: Option<crate::codec::Parameters>,
}

impl std::fmt::Debug for Stream {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("Stream")
            .field("media", &self.media)
            .field("control", &self.control.as_ref().map(Url::as_str))
            .field("encoding_name", &self.encoding_name)
            .field("rtp_payload_type", &self.rtp_payload_type)
            .field("clock_rate", &self.clock_rate_hz)
            .field("channels", &self.channels)
            .field("framerate", &self.framerate)
            .field("direction", &self.direction)
            .field("fmtp", &self.fmtp)
            .field("parameters", &self.parameters)
            .field("state", &self.state)
            .finish()
    }
}

impl Stream {
    /// Returns the media type, as specified in the [IANA SDP parameters media
    /// registry](https://www.iana.org/assignments/sdp-parameters/sdp-parameters.xhtml#sdp-parameters-1).
    #[inline]
    pub fn media(&self) -> &str {
        &self.media
    }

    /// An encoding name, as specified in the [IANA media type
    /// registry](https://www.iana.org/assignments/media-types/media-types.xhtml), with
    /// ASCII characters in lowercase.
    ///
    /// Commonly used but not specified in that registry: the ONVIF types
    /// claimed in the
    /// [ONVIF Streaming Spec](https://www.onvif.org/specs/stream/ONVIF-Streaming-Spec.pdf):
    /// *   `vnd.onvif.metadata`
    /// *   `vnd.onvif.metadata.gzip`,
    /// *   `vnd.onvif.metadata.exi.onvif`
    /// *   `vnd.onvif.metadata.exi.ext`
    #[inline]
    pub fn encoding_name(&self) -> &str {
        &self.encoding_name
    }

    /// Returns the RTP payload type.
    ///
    /// See the [registry](https://www.iana.org/assignments/rtp-parameters/rtp-parameters.xhtml#rtp-parameters-1).
    /// It's common to use one of the dynamically assigned values, 96–127.
    #[inline]
    pub fn rtp_payload_type(&self) -> u8 {
        self.rtp_payload_type
    }

    /// Returns the RTP clock rate, in Hz.
    #[inline]
    pub fn clock_rate_hz(&self) -> u32 {
        self.clock_rate_hz
    }

    /// Returns the number of audio channels, if applicable (`media` is `audio`) and known.
    #[inline]
    pub fn channels(&self) -> Option<NonZeroU16> {
        self.channels
    }

    /// Returns the video framerate if present in SDP attributes.
    #[inline]
    pub fn framerate(&self) -> Option<f32> {
        self.framerate
    }

    /// Returns the specified control URL.
    ///
    /// This is needed with multiple streams to send `SETUP` requests and
    /// interpret the `PLAY` response's `RTP-Info` header.
    /// [RFC 2326 section C.3](https://datatracker.ietf.org/doc/html/rfc2326#appendix-C.3)
    /// says the server is allowed to omit it when there is only a single stream.
    #[inline]
    pub fn control(&self) -> Option<&Url> {
        self.control.as_ref()
    }

    /// Returns whether Retina receives or sends this stream's media.
    ///
    /// This is [`StreamDirection::Receiving`] unless
    /// [`SessionOptions::backchannel`] is set and the stream is an ONVIF
    /// backchannel; see [`StreamDirection::Sending`] for the exact conditions.
    #[cfg(feature = "unstable-send")]
    #[inline]
    pub fn direction(&self) -> StreamDirection {
        self.direction
    }
}

struct UdpSockets {
    rtp: UdpSocket,
    rtcp: UdpSocket,
}

impl UdpSockets {
    fn socket(&self, channel_type: ChannelType) -> &UdpSocket {
        match channel_type {
            ChannelType::Rtp => &self.rtp,
            ChannelType::Rtcp => &self.rtcp,
        }
    }
}

impl Stream {
    /// Returns codec-specific parameters for this stream as described in the
    /// `DESCRIBE` response's SDP, if available.
    ///
    /// Returns `None` on unknown codecs, bad parameters, or if the SDP doesn't
    /// supply them. Not all codecs guarantee parameters are provided in the
    /// SDP. Notably, H.264 allows parameters to be specified "in-band" (with
    /// the data packets) instead of or in addition to "out-of-band" (via SDP).
    ///
    /// This never changes. Current parameters, which may differ, are available
    /// from the stream's depacketizer via
    /// [`VideoFrameStart::parameters`](crate::codec::VideoFrameStart::parameters),
    /// [`VideoFrameEnd::parameters`](crate::codec::VideoFrameEnd::parameters),
    /// or [`Depacketizer::parameters`](crate::codec::Depacketizer::parameters).
    ///
    /// If there is no packet loss, parameters are generally available after
    /// the first frame. In the case of H.264, [RFC 6184 section
    /// 8.4](https://datatracker.ietf.org/doc/html/rfc6184#section-8.4) says
    /// "when parameter sets are added or updated, care SHOULD be taken to
    /// ensure that any parameter set is delivered prior to its usage."
    pub fn parameters(&self) -> Option<crate::codec::ParametersRef<'_>> {
        self.parameters
            .as_ref()
            .map(crate::codec::Parameters::as_ref)
    }

    /// Returns the payload format as described in the SDP.
    ///
    /// The encoding name is lowercase, as with [`Stream::encoding_name`].
    pub fn payload_format(&self) -> crate::codec::PayloadFormat {
        let mut f = crate::codec::PayloadFormat::new(
            self.media.to_string(),
            self.encoding_name.to_string(),
            self.clock_rate_hz,
        );
        if let Some(c) = self.channels {
            f = f.with_channels(c);
        }
        if let Some(fmtp) = &self.fmtp {
            f = f.with_fmtp(fmtp.to_string());
        }
        f
    }

    /// Creates a depacketizer for this stream, as described in the SDP.
    ///
    /// This is equivalent to [`crate::codec::Depacketizer::new`] with
    /// [`Stream::payload_format`].
    ///
    /// Returns an error if the codec is unsupported, the SDP's parameters
    /// for it are invalid, or this is a [`StreamDirection::Sending`] stream.
    ///
    /// Each depacketizer should be used with a single session; see
    /// [`crate::codec::VideoDepacketizer::push`].
    pub fn new_depacketizer<Ctx: Clone>(&self) -> Result<crate::codec::Depacketizer<Ctx>, Error> {
        if self.direction == StreamDirection::Sending {
            bail!(ErrorInt::InvalidArgument(
                "can't depacketize a sending stream (ONVIF backchannel)".to_owned()
            ));
        }
        crate::codec::Depacketizer::new(&self.payload_format())
    }

    /// Returns true if this stream has been set up via [`Session::setup`].
    ///
    /// Once playing, only streams which have been set up produce packets.
    #[inline]
    pub fn is_setup(&self) -> bool {
        !matches!(self.state, StreamState::Uninit)
    }

    /// Returns a context for this stream, if it has been set up.
    pub fn ctx(&self) -> Option<&StreamContext> {
        match &self.state {
            StreamState::Uninit => None,
            StreamState::Init(init) => Some(&init.ctx),
            StreamState::Playing { ctx, .. } => Some(ctx),
        }
    }
}

#[derive(Clone, Debug)]
enum StreamState {
    /// Uninitialized; no `SETUP` has yet been sent.
    Uninit,

    /// `SETUP` response has been received.
    Init(StreamStateInit),

    /// `PLAY` response has been received. Further state is in the session's
    /// [`PlayingCore`].
    Playing { ctx: StreamContext },
}

#[derive(Clone, Debug)]
struct StreamStateInit {
    /// The RTP synchronization source (SSRC), as defined in
    /// [RFC 3550](https://tools.ietf.org/html/rfc3550). This is normally
    /// supplied in the `SETUP` response's `Transport` header; when it is not,
    /// it is learned from the first packet. Reolink cameras, and some Dahua
    /// firmware, also write an `ssrc` in the `PLAY` response's `RTP-Info`
    /// header, which RTSP/1.0 does not define; that one is ignored.
    ssrc: Option<u32>,

    /// The initial RTP sequence number, as specified in the `PLAY` response's
    /// `RTP-Info` header. This field is only used during the `play()` call
    /// itself; by the time it returns, the stream will be in state `Playing`.
    initial_seq: Option<u16>,

    /// The initial RTP timestamp, as specified in the `PLAY` response's
    /// `RTP-Info` header. This field is only used during the `play()` call
    /// itself; by the time it returns, the stream will be in state `Playing`.
    initial_rtptime: Option<u32>,

    ctx: StreamContext,
}

/// Username and password authentication credentials.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Credentials {
    pub username: String,
    pub password: String,
}

/// Marker trait for the state of a [Session].
/// This doesn't closely match [RFC 2326
/// A.1](https://tools.ietf.org/html/rfc2326#appendix-A.1). In practice, we've
/// found that cheap IP cameras are more restrictive than RTSP suggests. Eg, a
/// `DESCRIBE` changes the connection's state such that another one will fail,
/// before assigning a session id. Thus [Session] represents something more like
/// an RTSP connection than an RTSP session.
#[doc(hidden)]
pub trait State {}

/// Initial state after a `DESCRIBE`; use via `Session<Described>`.
#[doc(hidden)]
pub struct Described(());
impl State for Described {}

/// State after a `PLAY`; use via `Session<Playing>`.
#[doc(hidden)]
pub struct Playing(());
impl State for Playing {}

/// An RTSP session.
///
/// The expected lifecycle is as follows:
///
/// 1. Create a session via [`Session::describe`].
/// 2. Examine the session's available streams via [`Session::streams`] and set
///    up one or more via [`Session::setup`].
/// 3. Start playing via [`Session::play`].
/// 4. Get packets via [`Session<Playing>::next_item`], and turn them into
///    frames by pushing them to depacketizers from [`Stream::new_depacketizer`].
///    If a [`StreamDirection::Sending`] stream (ONVIF backchannel) was set up,
///    send packets on it via [`Session<Playing>::queue_rtp`].
/// 5. Drop the session. Retina may issue a `TEARDOWN` in the background, depending on the
///    [`SessionOptions::teardown`] parameter.
/// 6. Possibly wait for `TEARDOWN` to complete; see
///    [`SessionOptions::session_group`] and [`SessionGroup::await_teardown`].
///
/// This does I/O for a [`SessionCore`], which holds the protocol logic.
///
/// ## tokio runtime
///
/// All `Session` operations are currently expected to be performed from
/// "within" a tokio runtime with both time and I/O resource drivers enabled.
/// Operations may panic or fail otherwise.
pub struct Session<S: State>(Box<SessionInner>, S);

struct SessionInner {
    /// The RTSP connection, used only for I/O. Currently there's expected to
    /// always be one, even while playing a RTP/AVP/UDP session. The only
    /// exception is during drop.
    conn: Option<crate::tokio::Connection>,

    /// The protocol state.
    core: SessionCore,

    /// Sockets for each stream in the presentation which is set up via UDP.
    udp: Box<[Option<UdpSockets>]>,

    /// Fires at the core's [`SessionCore::poll_timeout`]; only used in state
    /// `Playing`. Tests may disable it.
    keepalive_timer: Option<Pin<Box<tokio::time::Sleep>>>,

    /// The index within `udp` to start the next poll at. Round-robining
    /// between them rather than always starting at 0 should prevent one stream
    /// from starving the others.
    udp_next_poll_i: usize,
}

impl SessionInner {
    fn playing_core(&mut self) -> &mut PlayingCore {
        self.core
            .playing_mut()
            .expect("core is playing in state Playing")
    }
}

#[derive(Copy, Clone)]
#[repr(u8)]
pub(crate) enum SessionFlag {
    /// Set if the server may be in state Playing: we have sent a `PLAY`
    /// request, regardless of if the response has been received.
    MaybePlaying = 0x1,

    /// Set if one or more streams are configured to use TCP.
    TcpStreams = 0x2,

    /// Set if one or more streams are configured to use UDP.
    UdpStreams = 0x4,

    /// Set if a [`StreamDirection::Sending`] stream has been set up, so the
    /// session uses the ONVIF backchannel.
    Backchannel = 0x8,
}

/// The `Require` header value for the ONVIF backchannel, as defined in the
/// [ONVIF Streaming Specification](https://www.onvif.org/specs/stream/ONVIF-Streaming-Spec.pdf)
/// section 5.3.1.
const BACKCHANNEL_REQUIRE: &str = "www.onvif.org/ver20/backchannel";
const _: () = assert!(crate::rtsp::table::is_valid_header_value(
    BACKCHANNEL_REQUIRE.as_bytes()
));

/// Returns [`BACKCHANNEL_REQUIRE`] as a header value.
fn backchannel_require() -> msg::HeaderValue {
    msg::HeaderValue::try_from(BACKCHANNEL_REQUIRE)
        .expect("BACKCHANNEL_REQUIRE is checked to be a valid header value at compile time")
}

/// Checks that `url` is suitable for `DESCRIBE`, returning its host.
fn validate_url(url: &Url) -> Result<url::Host<&str>, String> {
    if url.scheme() != "rtsp" {
        return Err(format!(
            "Bad URL {}; only scheme rtsp supported",
            url.as_str()
        ));
    }
    if url.username() != "" || url.password().is_some() {
        // Url apparently doesn't even have a way to clear the credentials,
        // so this has to be an error.
        // TODO: that's not true; revisit this.
        return Err("URL must not contain credentials".to_owned());
    }
    url.host()
        .ok_or_else(|| format!("Must specify host in rtsp url {}", url))
}

/// Connects to the server named in `url`.
async fn connect(url: &Url, options: &SessionOptions) -> Result<crate::tokio::Connection, Error> {
    let host = validate_url(url).map_err(|e| wrap!(ErrorInt::InvalidArgument(e)))?;
    let port = url.port().unwrap_or(554);
    crate::tokio::Connection::connect(host, port, options.bind_addr)
        .await
        .map_err(|e| wrap!(ErrorInt::ConnectError(e)))
}

/// A sans-I/O core's buffer of bytes to write; see [`poll_write_transmit`].
trait TransmitCore {
    fn transmit_buf(&self) -> (&[u8], &[u8]);
    fn advance_transmit(&mut self, n: usize);
}

impl TransmitCore for SessionCore {
    fn transmit_buf(&self) -> (&[u8], &[u8]) {
        SessionCore::transmit_buf(self)
    }
    fn advance_transmit(&mut self, n: usize) {
        SessionCore::advance_transmit(self, n)
    }
}

impl TransmitCore for conn::ConnCore {
    fn transmit_buf(&self) -> (&[u8], &[u8]) {
        conn::ConnCore::transmit_buf(self)
    }
    fn advance_transmit(&mut self, n: usize) {
        conn::ConnCore::advance_transmit(self, n)
    }
}

impl TransmitCore for PlayingCore {
    fn transmit_buf(&self) -> (&[u8], &[u8]) {
        PlayingCore::transmit_buf(self)
    }
    fn advance_transmit(&mut self, n: usize) {
        PlayingCore::advance_transmit(self, n)
    }
}

/// Writes from `core`'s transmit buffer to `conn` until it's empty.
fn poll_write_transmit(
    cx: &mut std::task::Context<'_>,
    conn: &mut crate::tokio::Connection,
    core: &mut impl TransmitCore,
) -> Poll<Result<(), Error>> {
    loop {
        let bufs = core.transmit_buf();
        if bufs.0.is_empty() {
            return Poll::Ready(Ok(()));
        }
        let n = ready!(conn.poll_write_vectored(cx, bufs)).map_err(|e| Error(Arc::new(e)))?;
        core.advance_transmit(n);
    }
}

/// A sans-I/O core which completes one request at a time; see [`poll_request`].
trait RequestCore: TransmitCore {
    type Output;
    fn read_buf(&mut self) -> &mut crate::buf::MarkBuf;
    fn handle_eof(&mut self);
    fn read_error(&self, source: io::Error, now: std::time::Instant) -> Error;
    fn poll_done(&mut self, now: std::time::Instant) -> Option<Result<Self::Output, Error>>;
}

impl RequestCore for SessionCore {
    type Output = SessionEvent;
    fn read_buf(&mut self) -> &mut crate::buf::MarkBuf {
        SessionCore::read_buf(self)
    }
    fn handle_eof(&mut self) {
        SessionCore::handle_eof(self)
    }
    fn read_error(&self, source: io::Error, now: std::time::Instant) -> Error {
        SessionCore::read_error(self, source, now)
    }
    fn poll_done(&mut self, now: std::time::Instant) -> Option<Result<SessionEvent, Error>> {
        self.poll_event(now)
    }
}

impl RequestCore for conn::ConnCore {
    type Output = conn::Response;
    fn read_buf(&mut self) -> &mut crate::buf::MarkBuf {
        conn::ConnCore::read_buf(self)
    }
    fn handle_eof(&mut self) {
        self.eof = true;
    }
    fn read_error(&self, source: io::Error, now: std::time::Instant) -> Error {
        conn::ConnCore::read_error(self, source, now)
    }
    fn poll_done(&mut self, now: std::time::Instant) -> Option<Result<conn::Response, Error>> {
        self.poll_response(now)
    }
}

/// Does I/O on `conn` until `core`'s outstanding request completes.
///
/// The caller must have started a request, so that EOF ends it.
fn poll_request<C: RequestCore>(
    cx: &mut std::task::Context<'_>,
    conn: &mut crate::tokio::Connection,
    core: &mut C,
) -> Poll<Result<C::Output, Error>> {
    loop {
        // Use tokio's clock, to match the timer. Outside tests that pause
        // time, it's the same as `std::time::Instant::now()`.
        let now = tokio::time::Instant::now().into_std();
        if let Some(r) = core.poll_done(now) {
            return Poll::Ready(r);
        }

        // Write after `poll_done`, which may have queued a request (such as a
        // retry with authentication) that the server must see before it will
        // send anything more.
        if let Poll::Ready(Err(e)) = poll_write_transmit(cx, conn, core) {
            return Poll::Ready(Err(e));
        }
        match conn.poll_read(cx, core.read_buf()) {
            Poll::Ready(Ok(0)) => core.handle_eof(),
            Poll::Ready(Ok(_)) => {}
            Poll::Ready(Err(e)) => return Poll::Ready(Err(core.read_error(e, now))),
            Poll::Pending => return Poll::Pending,
        }
    }
}

/// Handles data on an unassigned RTSP channel of `conn`.
fn handle_unassigned_data(
    conn: &mut conn::ConnCore,
    msg_ctx: RtspMessageContext,
    channel_id: u8,
    data: Bytes,
    now: Instant,
) -> Result<(), Error> {
    let conn_ctx = &conn.ctx;
    let seen_unassigned = &mut conn.seen_unassigned;
    let options = &conn.options;
    let tool = conn.tool.as_ref();
    let live555 = match options.unassigned_channel_data {
        UnassignedChannelDataPolicy::Auto
            if tool.map(Tool::has_live555_tcp_bug).unwrap_or(false) =>
        {
            true
        }
        UnassignedChannelDataPolicy::AssumeStaleSession => true,
        UnassignedChannelDataPolicy::Error => false,
        UnassignedChannelDataPolicy::Ignore | UnassignedChannelDataPolicy::Auto => {
            if !*seen_unassigned {
                log::warn!(
                    "Ignoring data on unassigned RTSP interleaved data channel {}. \
                     This is the first such message. Following messages will be logged \
                     at trace priority only.\n\n\
                     conn: {}\nmsg: {}\ndata: {:#?}",
                    channel_id,
                    conn_ctx,
                    msg_ctx,
                    crate::hex::LimitedHex::new(&data, 128),
                );
                *seen_unassigned = true;
            } else {
                log::trace!(
                    "Ignoring data on unassigned RTSP interleaved data channel {}.\n\n\
                     conn: {}\nmsg: {}\ndata: {:#?}",
                    channel_id,
                    conn_ctx,
                    msg_ctx,
                    crate::hex::LimitedHex::new(&data, 128),
                );
            }
            return Ok(());
        }
    };

    if live555 {
        note_stale_live555_data(tool, options, conn_ctx, channel_id, &msg_ctx, now);
    }

    bail!(ErrorInt::RtspUnassignedChannelError {
        conn_ctx: *conn_ctx,
        msg_ctx,
        channel_id,
        data,
    });
}

/// Fills out `req` with authorization and `CSeq` headers, returning the `CSeq`.
fn fill_req(
    next_cseq: &mut u32,
    options: &SessionOptions,
    requested_auth: &mut Option<http_auth::PasswordClient>,
    req: &mut OwnedMessage,
) -> Result<u32, Error> {
    let cseq = *next_cseq;
    *next_cseq += 1;
    if let Some(auth) = requested_auth {
        let creds = options
            .creds
            .as_ref()
            .expect("creds were checked when filling request_auth");
        let authorization = auth
            .respond(&http_auth::PasswordParams {
                username: &creds.username,
                password: &creds.password,
                uri: req.request_uri_str(),
                method: req.method_str(),
                body: Some(&[]),
            })
            .map_err(|e| wrap!(ErrorInt::Internal(e.into())))?;
        let headers = req.headers_mut();
        headers.insert(
            msg::HeaderName::AUTHORIZATION,
            msg::HeaderValue::try_from(authorization).unwrap(),
        );
    }
    let headers = req.headers_mut();
    headers.insert(
        msg::HeaderName::CSEQ,
        msg::HeaderValue::try_from(cseq.to_string()).unwrap(),
    );

    let user_agent = if let Some(ref u) = options.user_agent {
        u
    } else {
        DEFAULT_USER_AGENT
    };
    headers.insert(
        msg::HeaderName::USER_AGENT,
        msg::HeaderValue::try_from(user_agent.to_string()).unwrap(),
    );

    Ok(cseq)
}

const DEFAULT_USER_AGENT: &str = concat!("retina_", env!("CARGO_PKG_VERSION"));

impl<S: State> Session<S> {
    /// Returns the available streams as described by the server.
    pub fn streams(&self) -> &[Stream] {
        self.0.core.streams()
    }

    /// Returns the server's version as declared in the `DESCRIBE` response's `a:tool` SDP
    /// attribute.
    pub fn tool(&self) -> Option<&Tool> {
        self.0.core.tool()
    }

    /// Returns a context for the RTSP connection, e.g. for error messages.
    pub fn conn_ctx(&self) -> &crate::ConnectionContext {
        self.0
            .conn
            .as_ref()
            .expect("conn is present until drop")
            .ctx()
    }
}

impl Session<Described> {
    /// Creates a new session from a `DESCRIBE` request on the given URL.
    ///
    /// This method is permissive; it will return success even if there are
    /// errors in the SDP that would prevent one or more streams from being
    /// depacketized correctly. The errors in question are returned from
    /// [`Stream::new_depacketizer`].
    ///
    /// Expects to be called from a tokio runtime.
    pub async fn describe(url: Url, options: SessionOptions) -> Result<Self, Error> {
        let conn = connect(&url, &options).await?;
        Self::describe_with_conn(conn, options, url).await
    }

    async fn describe_with_conn(
        conn: crate::tokio::Connection,
        options: SessionOptions,
        url: Url,
    ) -> Result<Self, Error> {
        let core = SessionCore::from_conn(conn::ConnCore::new(*conn.ctx(), options));
        let mut inner = Box::new(SessionInner {
            conn: Some(conn),
            core,
            udp: Box::new([]),
            keepalive_timer: None,
            udp_next_poll_i: 0,
        });
        inner.core.describe(url)?;
        let event = inner.drive().await?;
        debug_assert!(matches!(event, SessionEvent::Described), "{event:?}");
        inner.udp = inner.core.streams().iter().map(|_| None).collect();
        Ok(Session(inner, Described(())))
    }

    /// Returns the raw SDP (Session Description Protocol) session description of this URL.
    ///
    /// Retina interprets the SDP automatically, but the raw bytes may be useful for debugging.
    /// They're accessibled in the `Session<Described>` state. Currently, they're discarded on
    /// `play` to reduce memory usage.
    pub fn sdp(&self) -> &[u8] {
        self.0.core.sdp()
    }

    /// Sends a `SETUP` request for a stream.
    ///
    /// Note these can't reasonably be pipelined because subsequent requests
    /// are expected to adopt the previous response's `Session`. Likewise,
    /// the server may override the preferred interleaved channel id and it
    /// seems like a bad idea to try to assign more interleaved channels without
    /// inspect that first.
    ///
    /// A [`StreamDirection::Sending`] stream (ONVIF backchannel) can currently
    /// only be set up with [`Transport::Tcp`]; `SETUP` with
    /// [`Transport::Udp`] fails without sending a request.
    ///
    /// Panics if `stream_i >= self.streams().len()`.
    pub async fn setup(&mut self, stream_i: usize, options: SetupOptions) -> Result<(), Error> {
        let inner = &mut *self.0;
        let (transport, pair) = match options.transport {
            Transport::Tcp(_) => (SetupTransport::Tcp, None),
            Transport::Udp(_) => {
                // Bind an ephemeral UDP port on the same local address used to connect
                // to the RTSP server.
                let local_ip = inner.core.conn_ctx().local_addr.ip();
                let pair = crate::tokio::UdpPair::for_ip(local_ip)
                    .map_err(|e| wrap!(ErrorInt::Internal(e.into())))?;
                (
                    SetupTransport::Udp {
                        client_rtp_port: pair.rtp_port,
                    },
                    Some(pair),
                )
            }
        };
        inner.core.setup(stream_i, transport)?;
        let SessionEvent::SetUp { udp_peer, .. } = inner.drive().await? else {
            unreachable!("SETUP completes with SetUp");
        };
        if let (Some(pair), Some(peer)) = (pair, udp_peer) {
            let sockets = UdpSockets {
                rtp: pair.rtp_socket,
                rtcp: pair.rtcp_socket,
            };
            sockets
                .rtp
                .connect(peer)
                .await
                .map_err(|e| wrap!(ErrorInt::ConnectError(e)))?;
            sockets
                .rtcp
                .connect(SocketAddr::new(peer.ip(), peer.port() + 1))
                .await
                .map_err(|e| wrap!(ErrorInt::ConnectError(e)))?;

            // Punch a hole in connection-tracking firewalls, as described at
            // `SessionCore::poll_transmit_udp`.
            while let Some(t) = inner.core.poll_transmit_udp() {
                sockets
                    .socket(t.channel_type)
                    .send(&t.data)
                    .await
                    .map_err(|e| wrap!(ErrorInt::ConnectError(e)))?;
            }
            inner.udp[stream_i] = Some(sockets);
        }
        Ok(())
    }

    /// Sends a `PLAY` request for the entire presentation.
    ///
    /// The presentation must support aggregate control, as defined in [RFC 2326
    /// section 1.3](https://tools.ietf.org/html/rfc2326#section-1.3).
    ///
    /// If a [`StreamDirection::Sending`] stream has been set up, the request
    /// carries the ONVIF backchannel `Require` header, and the caller may send
    /// on it as soon as this returns.
    pub async fn play(mut self, policy: PlayOptions) -> Result<Session<Playing>, Error> {
        let inner = &mut *self.0;
        inner.core.play(policy)?;
        let event = inner.drive().await?;
        debug_assert!(matches!(event, SessionEvent::Playing), "{event:?}");
        let deadline = inner
            .core
            .poll_timeout()
            .expect("playing core has a timeout");
        inner.keepalive_timer = Some(Box::pin(tokio::time::sleep_until(
            tokio::time::Instant::from_std(deadline),
        )));
        Ok(Session(self.0, Playing(())))
    }
}

impl SessionInner {
    /// Does I/O until the session core's request completes.
    async fn drive(&mut self) -> Result<SessionEvent, Error> {
        let conn = self.conn.as_mut().expect("conn is present until drop");
        let core = &mut self.core;
        std::future::poll_fn(|cx| poll_request(cx, conn, core)).await
    }
}

/// Notes an unexpected RTSP interleaved data message.
///
/// This is assumed to be due to a live555 RTP/AVP/TCP session that belonged
/// to a since-closed RTSP connection, as described in case 2 of "Stale sessions"
/// at [`SessionGroup`]. If there's no known session which explains this,
/// adds an unknown session with live555's default timeout.
fn note_stale_live555_data(
    tool: Option<&Tool>,
    options: &SessionOptions,
    conn_ctx: &crate::ConnectionContext,
    channel_id: u8,
    msg_ctx: &RtspMessageContext,
    now: Instant,
) {
    let known_to_have_live555_tcp_bug = tool.map(Tool::has_live555_tcp_bug).unwrap_or(false);
    if !known_to_have_live555_tcp_bug {
        log::warn!(
            "saw unexpected RTSP packet. This is presumed to be due to a bug in old
             live555 servers' TCP handling, though tool attribute {tool:?} does not refer to a \
             known-buggy version. Consider switching to UDP.\n\n\
             conn: {conn_ctx:?}\n\
             channel: {channel_id}\n\
             msg: {msg_ctx:?}"
        );
    }

    let group = match options.session_group.as_ref() {
        Some(g) => g,
        None => {
            log::debug!("Not tracking stale session because there's no session group.");
            return;
        }
    };

    if let Some(s) = group.lock_pruned(now).sessions.iter().find(|s| s.has_tcp) {
        // This session plausibly explains the packet.
        // (We could go so far as to examine the data packet's SSRC to
        // see if it matches one associated with this session. But
        // retrying once per expiration is probably good enough.)
        log::debug!(
            "Unexpected RTSP interleaved packet (live555 stale file \
             descriptor bug) plausibly explained by known stale \
             session {:?}/{}. Not adding a session entry.",
            group.debug_id(),
            s.seqnum,
        );
        return;
    }

    // The caller *might* have a better guess than LIVE555_EXPIRATION_SEC via a SETUP response,
    // but it's also possible for note_stale_live555_data to be called prior to SETUP.
    // The group forgets the session lazily once it expires.
    let expires = now + std::time::Duration::from_secs(LIVE555_EXPIRATION_SEC);
    let seqnum = group.add(now, StaleTeardown::Impossible, true, true, expires);
    log::debug!(
        "Unexpected RTSP interleaved packet, presumed due to live555 stale \
         file descriptor bug; added stale session {:?}/{} that will \
         expire in {} seconds.",
        group.debug_id(),
        seqnum,
        LIVE555_EXPIRATION_SEC,
    );
}

/// An item returned by [`Session<Playing>::next_item`].
#[derive(Debug)]
#[non_exhaustive]
pub enum PlayingItem<'a> {
    /// An RTP packet, borrowed from the session's receive buffer.
    Rtp(RtpPacket<'a>),

    /// An RTCP compound packet.
    Rtcp(crate::rtcp::ReceivedCompoundPacket),
}

/// A received RTP packet, borrowed from the session's receive buffer.
///
/// Supply [`RtpPacket::packet`] to a depacketizer such as
/// [`crate::codec::VideoDepacketizer::push`] to turn packets into frames
/// without copying payloads out of the buffer. If the depacketizer retains
/// part of a frame, the session keeps those bytes in its buffer until the
/// depacketizer is done with them.
pub struct RtpPacket<'a> {
    stream_id: usize,
    stream: &'a Stream,
    pkt: crate::rtp::ReceivedPacketRef<'a, crate::PacketContext>,

    /// The buffer position of the start of the RTP header.
    raw_pos: u64,
    raw_len: u16,
}

impl<'a> RtpPacket<'a> {
    /// Returns the index of this packet's stream within [`Session::streams`].
    #[inline]
    pub fn stream_id(&self) -> usize {
        self.stream_id
    }

    /// Returns this packet's stream.
    ///
    /// This is `session.streams()[pkt.stream_id()]`, which is otherwise
    /// inaccessible while the packet borrows the session.
    #[inline]
    pub fn stream(&self) -> &'a Stream {
        self.stream
    }

    /// Returns the payload and metadata, ready to push to a depacketizer.
    #[inline]
    pub fn packet(&self) -> &crate::rtp::ReceivedPacketRef<'a, crate::PacketContext> {
        &self.pkt
    }

    /// Returns the fixed 12-byte RTP header, e.g. for its payload type.
    #[inline]
    pub fn header(&self) -> crate::rtp::PacketHeader {
        crate::rtp::PacketHeader(self.raw().peek_array())
    }

    /// Returns the raw packet, including the RTP header.
    #[inline]
    pub fn raw(&self) -> crate::buf::Split<'a> {
        self.pkt
            .buf()
            .split(self.raw_pos, usize::from(self.raw_len))
    }
}

impl std::fmt::Debug for RtpPacket<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let meta = &self.pkt.meta;
        f.debug_struct("RtpPacket")
            .field("stream_id", &self.stream_id)
            .field("ctx", &meta.ctx)
            .field("timestamp", &meta.timestamp)
            .field("ssrc", &format_args!("{:08x}", meta.ssrc))
            .field("sequence_number", &meta.sequence_number)
            .field("mark", &meta.mark)
            .field("loss", &meta.loss)
            .field(
                "payload",
                &crate::hex::LimitedHex::from_split(self.pkt.payload(), 64),
            )
            .finish()
    }
}

impl Session<Playing> {
    /// Polls for the next RTP or RTCP packet.
    ///
    /// Returns `Ready(None)` when the server closes the connection.
    ///
    /// The session does I/O, including sending keepalives, only while the
    /// caller polls. The item borrows the session, so it must be dropped
    /// before the next poll.
    ///
    /// This is cancel safe: if a future which calls it is dropped before
    /// completion, no packet is lost.
    pub fn poll_next_item(
        &mut self,
        cx: &mut std::task::Context<'_>,
    ) -> Poll<Option<Result<PlayingItem<'_>, Error>>> {
        let v = match ready!(self.poll_validated(cx)) {
            None => return Poll::Ready(None),
            Some(Err(e)) => return Poll::Ready(Some(Err(e))),
            Some(Ok(v)) => v,
        };
        Poll::Ready(Some(Ok(self.0.playing_core().item(v))))
    }

    /// Returns the next RTP or RTCP packet.
    ///
    /// This is an `async` wrapper around [`Session::poll_next_item`]; see
    /// there for details.
    pub async fn next_item(&mut self) -> Option<Result<PlayingItem<'_>, Error>> {
        match std::future::poll_fn(|cx| self.poll_validated(cx)).await {
            None => None,
            Some(Err(e)) => Some(Err(e)),
            Some(Ok(v)) => Some(Ok(self.0.playing_core().item(v))),
        }
    }

    /// Does I/O until the core has a validated item or the session ends.
    fn poll_validated(
        &mut self,
        cx: &mut std::task::Context<'_>,
    ) -> Poll<Option<Result<playing::ValidatedItem, Error>>> {
        let SessionInner {
            conn,
            core,
            udp,
            keepalive_timer,
            udp_next_poll_i,
        } = &mut *self.0;
        let conn = conn.as_mut().expect("conn is present until drop");
        let core = core
            .playing_mut()
            .expect("core is playing in state Playing");
        loop {
            // Use tokio's clock, to match the timer. Outside tests that pause
            // time, it's the same as `std::time::Instant::now()`.
            let now = tokio::time::Instant::now().into_std();

            // Write queued keepalives, receiver reports, and sent media as the
            // connection allows, even while reading. Otherwise a steady stream
            // of received media could hold up sending.
            if let Poll::Ready(Err(e)) = poll_write_transmit(cx, conn, core) {
                return Poll::Ready(Some(Err(e)));
            }

            // Then return anything parsed from data already received.
            if let Some(r) = core.poll_validated(now) {
                return Poll::Ready(Some(r));
            }
            if core.is_closed() {
                debug!("Server closed RTSP connection");
                return Poll::Ready(None);
            }

            // Then try receiving data on the RTSP connection.
            match conn.poll_read(cx, core.read_buf()) {
                Poll::Ready(Ok(0)) => {
                    core.handle_eof();
                    continue;
                }
                Poll::Ready(Ok(_)) => continue,
                Poll::Ready(Err(e)) => {
                    let e = core.read_error(e, now);
                    debug!("RTSP connection error: {:?}", e);
                    return Poll::Ready(Some(Err(e)));
                }
                Poll::Pending => {}
            }

            // Next try receiving data on the UDP sockets, if any.
            match Self::poll_udp(cx, core, udp, udp_next_poll_i, now) {
                Poll::Ready(Ok(())) => continue,
                Poll::Ready(Err(e)) => return Poll::Ready(Some(Err(e))),
                Poll::Pending => {}
            }

            // Then check if it's time for a new keepalive. Loop afterward to
            // poll the reset timer.
            // Note: in production keepalive_timer is always Some. Tests may disable it.
            if let Some(t) = keepalive_timer.as_mut()
                && t.as_mut().poll(cx).is_ready()
            {
                core.handle_timeout(now)?;
                t.as_mut()
                    .reset(tokio::time::Instant::from_std(core.poll_timeout()));
                Self::send_udp_reports(core, udp);
                continue;
            }

            // Nothing to do. The poll calls above have already registered cx as necessary.
            return Poll::Pending;
        }
    }

    /// Sends the core's receiver reports for UDP streams.
    ///
    /// Each is sent right away if the socket has room; otherwise it's
    /// skipped, as later reports carry cumulative statistics anyway.
    fn send_udp_reports(core: &mut PlayingCore, udp: &[Option<UdpSockets>]) {
        while let Some(t) = core.poll_transmit_udp() {
            let i = t.stream_i;
            let sockets = udp[i].as_ref().expect("stream is a UDP stream");
            if let Err(e) = sockets.socket(t.channel_type).try_send(&t.data) {
                // `ConnectionRefused` can follow an ICMP error, as with the
                // hole-punching packets sent in `setup`. Neither it nor a full
                // socket buffer is a reason to end the session.
                match e.kind() {
                    io::ErrorKind::WouldBlock | io::ErrorKind::ConnectionRefused => {
                        debug!("Unable to send RTCP receiver report for stream {i}: {e}")
                    }
                    _ => warn!("Unable to send RTCP receiver report for stream {i}: {e}"),
                }
            }
        }
    }

    /// Polls a UDP socket, reading into `read_buf`'s spare capacity via
    /// vectored I/O (`socket2::SockRef::recv_vectored`). Handles spurious
    /// readiness, `ConnectionRefused` (from firewall hole-punching), and
    /// wraps I/O errors.
    ///
    /// On success, returns the byte count. The caller must call `advance_end`
    /// or the data will be overwritten on next call.
    ///
    /// Reads at most [`u16::MAX`] bytes, above any real datagram (65,507 for
    /// IPv4, 65,527 for IPv6), so the length fits in a `u16`. Note the vectored
    /// slices scatter a *single* datagram across the ring's wrap point;
    /// `recvmsg` on a datagram socket never coalesces queued packets.
    ///
    /// TODO: drain several packets per syscall via `recvmmsg` and/or `UDP_GRO`.
    /// [`PlayingCore::udp_received`] already accepts several
    /// datagrams before they're parsed; each datagram's length is still
    /// `u16`-bounded.
    fn poll_udp_recv(
        socket: &UdpSocket,
        cx: &mut std::task::Context,
        read_buf: &mut crate::buf::MarkBuf,
        conn_ctx: &crate::ConnectionContext,
        stream_ctx: &crate::StreamContext,
    ) -> Poll<Result<u16, Error>> {
        const MAX_DATAGRAM: usize = u16::MAX as usize;
        // `spare_capacity` returns *all* the free space, which may exceed the
        // requested reserve; clamp so `recv_vectored` can't exceed a `u16`.
        let (s1, s2) = read_buf.spare_capacity(MAX_DATAGRAM);
        let s1_len = s1.len().min(MAX_DATAGRAM);
        let s2_len = s2.len().min(MAX_DATAGRAM - s1_len);
        let s1 = &mut s1[..s1_len];
        let s2 = &mut s2[..s2_len];
        loop {
            ready!(socket.poll_recv_ready(cx)).map_err(|source| {
                wrap!(ErrorInt::UdpRecvError {
                    conn_ctx: *conn_ctx,
                    stream_ctx: stream_ctx.to_owned(),
                    when: crate::WallTime::now(),
                    source,
                })
            })?;
            // SAFETY: MaybeUninit<u8> has the same layout as u8, and
            // initialized memory is valid MaybeUninit.
            let s1_mu = unsafe {
                std::slice::from_raw_parts_mut(s1.as_mut_ptr().cast::<MaybeUninit<u8>>(), s1.len())
            };
            let s2_mu = unsafe {
                std::slice::from_raw_parts_mut(s2.as_mut_ptr().cast::<MaybeUninit<u8>>(), s2.len())
            };
            let mut bufs = [
                socket2::MaybeUninitSlice::new(s1_mu),
                socket2::MaybeUninitSlice::new(s2_mu),
            ];
            // Must go through `try_io` rather than issuing the syscall
            // directly: on `WouldBlock` it clears tokio's cached readiness, so
            // the next `poll_recv_ready` actually waits. Calling
            // `SockRef::recv_vectored` here instead leaves the readiness set,
            // and this task then burns CPU re-polling indefinitely (tokio's
            // cooperative budget makes it yield after ~128 futile syscalls,
            // whereupon the stale readiness wakes it right back up).
            let r = socket.try_io(tokio::io::Interest::READABLE, || {
                socket2::SockRef::from(socket).recv_vectored(&mut bufs)
            });
            match r {
                Ok((n, _flags)) => {
                    debug_assert!(n <= MAX_DATAGRAM);
                    return Poll::Ready(Ok(n as u16));
                }
                Err(source) if source.kind() == io::ErrorKind::WouldBlock => {
                    // Spurious readiness. Loop back to poll_recv_ready
                    // to wait for actual readiness.
                    continue;
                }
                Err(source) if source.kind() == io::ErrorKind::ConnectionRefused => {
                    // The hole-punching packets sent in `setup` can elicit a
                    // 'destination unreachable' ICMP response from the server,
                    // which gets turned into a 'connection refused' error.
                    debug!("Ignoring UDP connection refused error");
                    continue;
                }
                Err(source) => {
                    return Poll::Ready(Err(wrap!(ErrorInt::UdpRecvError {
                        conn_ctx: *conn_ctx,
                        stream_ctx: stream_ctx.to_owned(),
                        when: crate::WallTime::now(),
                        source,
                    })));
                }
            }
        }
    }

    /// Polls UDP stream `i`, reading a datagram into the core's buffer.
    ///
    /// Reads from RTCP then RTP sockets. Returns `Ready(Ok(()))` after a
    /// datagram, and only returns `Poll::Pending` after both sockets have
    /// returned `Poll::Pending`.
    fn poll_udp_stream(
        cx: &mut std::task::Context,
        core: &mut PlayingCore,
        udp_sockets: &UdpSockets,
        i: usize,
        now: std::time::Instant,
    ) -> Poll<Result<(), Error>> {
        let conn_ctx = *core.conn_ctx();
        let stream_ctx = *core.streams()[i].ctx().expect("UDP stream is set up");

        // Prioritize RTCP over RTP within a stream.
        for channel_type in [ChannelType::Rtcp, ChannelType::Rtp] {
            let socket = udp_sockets.socket(channel_type);
            match Self::poll_udp_recv(socket, cx, core.udp_buf(i), &conn_ctx, &stream_ctx) {
                Poll::Ready(Ok(n)) => {
                    core.udp_received(i, channel_type, n, now);
                    return Poll::Ready(Ok(()));
                }
                Poll::Ready(Err(e)) => return Poll::Ready(Err(e)),
                Poll::Pending => {}
            }
        }
        Poll::Pending
    }

    /// Polls all UDP streams, round-robining between them to avoid starvation.
    fn poll_udp(
        cx: &mut std::task::Context,
        core: &mut PlayingCore,
        udp: &[Option<UdpSockets>],
        next_poll_i: &mut usize,
        now: std::time::Instant,
    ) -> Poll<Result<(), Error>> {
        if udp.is_empty() {
            return Poll::Pending;
        }
        let starting_i = *next_poll_i;
        loop {
            let i = *next_poll_i;
            *next_poll_i = (i + 1) % udp.len();
            if let Some(sockets) = &udp[i]
                && let Poll::Ready(r) = Self::poll_udp_stream(cx, core, sockets, i, now)
            {
                return Poll::Ready(r);
            }
            if *next_poll_i == starting_i {
                return Poll::Pending;
            }
        }
    }
}

impl Drop for SessionInner {
    fn drop(&mut self) {
        let Some(core) = self.core.take_setup() else {
            return;
        };
        // Use tokio's clock, to match the background task's timers.
        let now = tokio::time::Instant::now().into_std();
        let Some(teardown) = core.into_teardown(now) else {
            return;
        };
        tokio::spawn(teardown::background_teardown(teardown, self.conn.take()));
    }
}

#[cfg(feature = "unstable-send")]
impl Session<Playing> {
    /// Queues an RTP packet on a [`StreamDirection::Sending`] stream (ONVIF
    /// backchannel).
    ///
    /// The caller builds packets with its own [`crate::rtp::Sender`], created
    /// with the stream's [`Stream::rtp_payload_type`], and sends RTCP sender
    /// reports for it via [`Session::queue_rtcp`].
    ///
    /// Queued data goes out on the RTSP connection, interleaved with RTSP
    /// requests, as the caller polls for items via [`Session::next_item`] or
    /// [`Session::poll_next_item`]. Queueing doesn't wait or limit how much is
    /// queued. A caller sending live media should check
    /// [`Session::queued_len`] first and drop media (or, via
    /// [`crate::codec::PayloadSink::congested`], have a packetizer shed load)
    /// while the server reads slowly, so sent media stays close to real time
    /// and the session keeps reading. After dropping a packet,
    /// [`crate::rtp::Sender::skip`] makes the gap visible to the server.
    ///
    /// A caller typically waits for both items and its media source via e.g.
    /// `tokio::select!`, queueing media once the `next_item` future is dropped;
    /// `next_item` is cancel safe.
    ///
    /// Fails without queueing anything if the stream isn't set up for sending;
    /// the session is still usable.
    pub fn queue_rtp(
        &mut self,
        stream_i: usize,
        pkt: &crate::rtp::OutgoingPacketRef<'_>,
    ) -> Result<(), Error> {
        self.0.playing_core().queue_rtp(stream_i, pkt)
    }

    /// Queues an RTCP packet, such as a sender report from
    /// [`crate::rtp::Sender::sender_report`], on a
    /// [`StreamDirection::Sending`] stream.
    ///
    /// See [`Session::queue_rtp`]. Fails as it does, or if `pkt` is longer
    /// than 65,535 bytes.
    pub fn queue_rtcp(&mut self, stream_i: usize, pkt: &[u8]) -> Result<(), Error> {
        self.0.playing_core().queue_rtcp(stream_i, pkt)
    }

    /// Returns the number of bytes queued to write to the RTSP connection,
    /// including RTSP requests and receiver reports as well as data from
    /// [`Session::queue_rtp`] and [`Session::queue_rtcp`].
    pub fn queued_len(&self) -> usize {
        let SessionInner { core, .. } = &*self.0;
        let (a, b) = core.transmit_buf();
        a.len() + b.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rtsp::msg::StatusCode;
    use crate::testutil::{init_logging, response};
    use futures::{SinkExt as _, StreamExt as _};
    use session_core::HOLE_PUNCH_RTCP;
    use std::net::{IpAddr, Ipv4Addr};

    /// Returns tokio's notion of now, which is paused in some tests.
    fn tokio_now() -> Instant {
        tokio::time::Instant::now().into_std()
    }

    /// Cross-platform, tokio equivalent of `socketpair(2)`.
    async fn socketpair() -> (tokio::net::TcpStream, tokio::net::TcpStream) {
        // Another process on the machine could connect to the server and mess
        // this up, but that's unlikely enough to ignore in test code.
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let client = tokio::net::TcpStream::connect(addr);
        let server = listener.accept();
        let (client, server) = (client.await.unwrap(), server.await.unwrap().0);

        // Without this, Nagle's algorithm holds back a small write until the
        // peer ACKs the last one, which on Linux it may delay ~40 ms. Tests
        // that pause time would auto-advance far past their deadlines meanwhile.
        client.set_nodelay(true).unwrap();
        server.set_nodelay(true).unwrap();
        (client, server)
    }

    /// UDP equivalent of [`socketpair`]: two mutually connected localhost
    /// sockets, as `setup` establishes for a UDP stream.
    async fn udp_socketpair() -> (UdpSocket, UdpSocket) {
        let a = UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let b = UdpSocket::bind("127.0.0.1:0").await.unwrap();
        a.connect(b.local_addr().unwrap()).await.unwrap();
        b.connect(a.local_addr().unwrap()).await.unwrap();
        (a, b)
    }

    /// Polls [`Session::poll_udp_recv`] once, returning its `Poll`.
    async fn poll_udp_recv_once(
        socket: &UdpSocket,
        read_buf: &mut crate::buf::MarkBuf,
    ) -> Poll<Result<u16, Error>> {
        let conn_ctx = crate::ConnectionContext::dummy();
        let stream_ctx = crate::StreamContext::dummy();
        std::future::poll_fn(|cx| {
            Poll::Ready(Session::<Playing>::poll_udp_recv(
                socket,
                cx,
                read_buf,
                &conn_ctx,
                &stream_ctx,
            ))
        })
        .await
    }

    #[tokio::test]
    async fn udp_recv_pending_when_idle() {
        let (a, _b) = udp_socketpair().await;
        let mut read_buf = crate::buf::MarkBuf::new(128 * 1024);
        assert!(poll_udp_recv_once(&a, &mut read_buf).await.is_pending());
    }

    #[tokio::test]
    async fn udp_recv_datagram() {
        let (a, b) = udp_socketpair().await;
        let mut read_buf = crate::buf::MarkBuf::new(128 * 1024);
        b.send(b"hello world").await.unwrap();
        a.readable().await.unwrap();

        let pos = read_buf.end();
        let Poll::Ready(Ok(n)) = poll_udp_recv_once(&a, &mut read_buf).await else {
            panic!("expected a datagram");
        };
        assert_eq!(n, 11);
        read_buf.advance_end(usize::from(n));
        assert_eq!(read_buf.split(pos, 11).to_owned(), b"hello world");
    }

    /// A datagram landing on the ring's wrap point must be scattered correctly
    /// across both halves of the vectored read.
    #[tokio::test]
    async fn udp_recv_scatters_across_ring_wrap() {
        let (a, b) = udp_socketpair().await;

        // Position `end` 10 bytes short of the ring's end, and consume
        // everything, so the free space wraps and its first half is 10 bytes.
        let mut read_buf = crate::buf::MarkBuf::new(128 * 1024);
        let head = read_buf.capacity() - 10;
        read_buf.extend(&vec![0u8; head]);
        read_buf.advance_unparsed(read_buf.end());

        let datagram: Vec<u8> = (0..100u8).collect();
        b.send(&datagram).await.unwrap();
        a.readable().await.unwrap();

        let pos = read_buf.end();
        let Poll::Ready(Ok(n)) = poll_udp_recv_once(&a, &mut read_buf).await else {
            panic!("expected a datagram");
        };
        assert_eq!(n, 100);
        read_buf.advance_end(usize::from(n));

        let split = read_buf.split(pos, 100);
        let (s1, s2) = split.slices();
        assert_eq!((s1.len(), s2.len()), (10, 90), "should have wrapped");
        assert_eq!(split.to_owned(), datagram);
    }

    /// Regression test: tokio caches readiness, and only its own `try_*` /
    /// `try_io` helpers clear it. Issuing the `recvmsg` directly after
    /// `poll_recv_ready` leaves stale readiness set, so the task is woken again
    /// as soon as it yields and re-polls forever, burning CPU without making
    /// progress. (It doesn't hang outright: tokio's cooperative budget forces a
    /// yield after ~128 futile syscalls, then the stale readiness wakes it
    /// straight back up.)
    ///
    /// Asserts the socket is polled once and then stays asleep.
    #[tokio::test]
    async fn udp_recv_stale_readiness_does_not_spin() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let (a, b) = udp_socketpair().await;
        b.send(b"hello").await.unwrap();
        a.readable().await.unwrap(); // tokio caches READABLE

        // Consume the datagram behind tokio's back, so the socket is no longer
        // readable but tokio still believes it is.
        let mut scratch = [MaybeUninit::<u8>::uninit(); 64];
        let n = socket2::SockRef::from(&a).recv(&mut scratch[..]).unwrap();
        assert_eq!(n, 5);

        let mut read_buf = crate::buf::MarkBuf::new(128 * 1024);
        let conn_ctx = crate::ConnectionContext::dummy();
        let stream_ctx = crate::StreamContext::dummy();
        let polls = AtomicUsize::new(0);
        let fut = std::future::poll_fn(|cx| {
            polls.fetch_add(1, Ordering::Relaxed);
            Session::<Playing>::poll_udp_recv(&a, cx, &mut read_buf, &conn_ctx, &stream_ctx)
        });
        let r = tokio::time::timeout(std::time::Duration::from_millis(200), fut).await;
        assert!(r.is_err(), "expected no datagram; got {:?}", r.map(drop));
        let polls = polls.load(Ordering::Relaxed);
        assert!(
            polls < 10,
            "polled {polls} times in 200ms: spinning on stale readiness",
        );
    }

    async fn connect_to_mock() -> (crate::tokio::Connection, crate::tokio::Connection) {
        let (client, server) = socketpair().await;
        let client = crate::tokio::Connection::from_stream(client).unwrap();
        let server = crate::tokio::Connection::from_stream(server)
            .unwrap()
            .with_reader(usize::MAX);
        (client, server)
    }

    /// Receives a request and sends a response, filling in the matching `CSeq`.
    async fn req_response(
        server: &mut crate::tokio::Connection,
        expected_method: msg::Method,
        response: (msg::Response, Bytes),
    ) {
        req_response_returning_req(server, expected_method, response).await;
    }

    /// As [`req_response`], also returning the request for inspection.
    async fn req_response_returning_req(
        server: &mut crate::tokio::Connection,
        expected_method: msg::Method,
        (mut response, resp_body): (msg::Response, Bytes),
    ) -> msg::Request {
        let msg = server.next().await.unwrap().unwrap();
        let req = match msg.msg {
            msg::Message::Request(r) => r,
            o => panic!("expected {expected_method:?} request, got {o:#?}"),
        };
        assert_eq!(req.method, expected_method);
        let cseq = req.headers.get("CSeq").unwrap().to_string();
        response.headers.insert(
            msg::HeaderName::CSEQ,
            msg::HeaderValue::try_from(cseq).unwrap(),
        );
        server
            .send(OwnedMessage::Response {
                head: response,
                body: resp_body,
            })
            .await
            .unwrap();
        req
    }

    /// Regression test: the tokio driver must write the authenticated retry
    /// that `ConnCore` queues upon `401 Unauthorized`, rather than waiting
    /// for the server to send more (which it won't until it gets the retry).
    #[tokio::test]
    async fn describe_retries_with_auth() {
        init_logging();
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();
        let options = SessionOptions::default().creds(Some(Credentials {
            username: "admin".to_owned(),
            password: "secret".to_owned(),
        }));
        let (session, ()) = tokio::time::timeout(std::time::Duration::from_secs(5), async {
            tokio::join!(Session::describe_with_conn(conn, options, url), async {
                let req = req_response_returning_req(
                    &mut server,
                    msg::Method::DESCRIBE,
                    response(include_bytes!("testdata/longse_unauthorized.txt")),
                )
                .await;
                assert!(req.headers.get("Authorization").is_none());
                let req = req_response_returning_req(
                    &mut server,
                    msg::Method::DESCRIBE,
                    response(include_bytes!("testdata/reolink_describe.txt")),
                )
                .await;
                let authorization = req.headers.get("Authorization").unwrap().to_string();
                assert!(authorization.starts_with("Digest "), "{authorization}");
            },)
        })
        .await
        .expect("authenticated DESCRIBE retry should be sent");
        assert_eq!(session.unwrap().streams().len(), 2);
    }

    /// Tests the happy path from initialization to teardown (first attempt succeeds).
    #[tokio::test(start_paused = true)]
    async fn simple() {
        init_logging();
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();
        let group = Arc::new(SessionGroup::default());

        // DESCRIBE.
        let (session, _) = tokio::join!(
            Session::describe_with_conn(
                conn,
                SessionOptions::default()
                    .session_group(group.clone())
                    .unassigned_channel_data(UnassignedChannelDataPolicy::Ignore),
                url
            ),
            req_response(
                &mut server,
                msg::Method::DESCRIBE,
                response(include_bytes!("testdata/reolink_describe.txt"))
            ),
        );
        let mut session = session.unwrap();
        assert_eq!(session.streams().len(), 2);

        // SETUP.
        tokio::join!(
            async {
                session.setup(0, SetupOptions::default()).await.unwrap();
            },
            req_response(
                &mut server,
                msg::Method::SETUP,
                response(include_bytes!("testdata/reolink_setup.txt"))
            ),
        );

        // PLAY.
        let (session, _) = tokio::join!(
            session.play(PlayOptions::default()),
            req_response(
                &mut server,
                msg::Method::PLAY,
                response(include_bytes!("testdata/reolink_play.txt"))
            ),
        );
        {
            let mut session = session.unwrap();

            // XXX: tokio will "auto-advance" paused time when timers are polled.
            // This is not great for this test. Disable keepalives to prevent it.
            // <https://github.com/tokio-rs/tokio/issues/4522>
            session.0.keepalive_timer = None;

            // Packets: first ignored one (unassigned channel), then one passed through.
            tokio::join!(
                async {
                    match session.next_item().await {
                        Some(Ok(PlayingItem::Rtp(p))) => {
                            assert_eq!(p.packet().meta.ssrc, 0xdcc4a0d8);
                            assert_eq!(p.packet().meta.sequence_number, 0x41d4);
                            assert_eq!(p.packet().payload().to_vec(), b"hello world");
                        }
                        o => panic!("unexpected item: {o:#?}"),
                    }
                },
                async {
                    let bad_pkt = b"data on unassigned channel";
                    server
                        .send(OwnedMessage::Data {
                            channel_id: 2,
                            body: Bytes::from_static(bad_pkt),
                        })
                        .await
                        .unwrap();
                    let good_pkt = b"\x80\x60\x41\xd4\x00\x00\x00\x00\xdc\xc4\xa0\xd8hello world";
                    server
                        .send(OwnedMessage::Data {
                            channel_id: 0,
                            body: Bytes::from_static(good_pkt),
                        })
                        .await
                        .unwrap();
                },
            );
        };

        // Drop (initiated by exiting the scope above).
        // This server advertises an ancient version of live555, so Retina
        // sends a TEARDOWN even with TCP.

        let stale_sessions = group.stale_sessions(tokio_now());
        assert_eq!(stale_sessions.num_sessions, 1);

        // Resume real time for the TEARDOWN exchange. With paused time,
        // the runtime may auto-advance through the teardown's I/O timeout
        // before the I/O exchange with the mock server completes, because
        // the auto-advance's non-blocking I/O poll can race with kernel
        // TCP event delivery on localhost.
        tokio::time::resume();
        tokio::join!(
            group.await_stale_sessions(&stale_sessions),
            req_response(
                &mut server,
                msg::Method::TEARDOWN,
                response(include_bytes!("testdata/reolink_teardown.txt"))
            ),
        );
        tokio::time::pause();
        assert_eq!(group.stale_sessions(tokio_now()).num_sessions, 0);
    }

    /// Borrowed packets via `Session::next_item`, pushed to a caller-owned
    /// depacketizer.
    #[tokio::test(start_paused = true)]
    #[cfg(feature = "h264")]
    async fn next_item() {
        use crate::codec::Accumulate;
        use crate::codec::events::testutil::{Event, Recorder, hex};
        init_logging();
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();
        let (session, _) = tokio::join!(
            Session::describe_with_conn(
                conn,
                SessionOptions::default().teardown(TeardownPolicy::Never),
                url
            ),
            req_response(
                &mut server,
                msg::Method::DESCRIBE,
                response(include_bytes!("testdata/reolink_describe.txt"))
            ),
        );
        let mut session = session.unwrap();
        tokio::join!(
            async {
                session.setup(0, SetupOptions::default()).await.unwrap();
            },
            req_response(
                &mut server,
                msg::Method::SETUP,
                response(include_bytes!("testdata/reolink_setup.txt"))
            ),
        );
        let (session, _) = tokio::join!(
            session.play(PlayOptions::default()),
            req_response(
                &mut server,
                msg::Method::PLAY,
                response(include_bytes!("testdata/reolink_play.txt"))
            ),
        );
        let mut session = session.unwrap();
        session.0.keepalive_timer = None; // see `simple`.

        assert!(session.streams()[0].is_setup());
        assert!(!session.streams()[1].is_setup());
        let mut d = session.streams()[0].new_depacketizer().unwrap();
        let mut h = Recorder::new(Accumulate::Yes);
        const PKT: &[u8] = b"\x80\xe0\x41\xd4\x00\x00\x00\x00\xdc\xc4\xa0\xd8\x65slice";
        tokio::join!(
            async {
                match session.next_item().await {
                    Some(Ok(PlayingItem::Rtp(p))) => {
                        assert_eq!(p.stream_id(), 0);
                        assert_eq!(p.stream().encoding_name(), "h264");
                        assert_eq!(p.header().sequence_number(), 0x41d4);
                        assert_eq!(p.header().payload_type(), 96);
                        assert_eq!(p.raw().to_vec(), PKT);
                        let meta = &p.packet().meta;
                        assert_eq!(meta.ssrc, 0xdcc4a0d8);
                        assert!(meta.mark);
                        assert_eq!(p.packet().payload().to_vec(), b"\x65slice");
                        d.push(p.packet(), &mut h);
                    }
                    o => panic!("unexpected item: {o:#?}"),
                }
            },
            async {
                server
                    .send(OwnedMessage::Data {
                        channel_id: 0,
                        body: Bytes::from_static(PKT),
                    })
                    .await
                    .unwrap();
            },
        );
        assert_eq!(
            h.take(),
            vec![
                Event::FrameStart {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                },
                Event::Data(crate::codec::Position::Complete, hex(b"\x65slice")),
                Event::FrameEnd {
                    is_random_access_point: true,
                    is_disposable: false,
                    has_new_parameters: false,
                    data: Some(hex(b"\x00\x00\x00\x06\x65slice")),
                },
            ]
        );
    }

    /// As above, but TEARDOWN fails until session expiration.
    #[tokio::test(start_paused = true)]
    async fn session_expiration() {
        init_logging();
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();
        let group = Arc::new(SessionGroup::default());

        // DESCRIBE.
        let (session, _) = tokio::join!(
            Session::describe_with_conn(
                conn,
                SessionOptions::default().session_group(group.clone()),
                url
            ),
            req_response(
                &mut server,
                msg::Method::DESCRIBE,
                response(include_bytes!("testdata/reolink_describe.txt"))
            ),
        );
        let mut session = session.unwrap();
        assert_eq!(session.streams().len(), 2);

        // SETUP.
        tokio::join!(
            async {
                session.setup(0, SetupOptions::default()).await.unwrap();
            },
            req_response(
                &mut server,
                msg::Method::SETUP,
                response(include_bytes!("testdata/reolink_setup.txt"))
            ),
        );

        // PLAY.
        let (session, _) = tokio::join!(
            session.play(PlayOptions::default()),
            req_response(
                &mut server,
                msg::Method::PLAY,
                response(include_bytes!("testdata/reolink_play.txt"))
            ),
        );
        let drop_time;
        {
            let mut session = session.unwrap();
            session.0.keepalive_timer = None; // see `simple`.

            // Packet.
            tokio::join!(
                async {
                    match session.next_item().await {
                        Some(Ok(PlayingItem::Rtp(p))) => {
                            assert_eq!(p.packet().meta.ssrc, 0xdcc4a0d8);
                            assert_eq!(p.packet().meta.sequence_number, 0x41d4);
                            assert_eq!(p.packet().payload().to_vec(), b"hello world");
                        }
                        o => panic!("unexpected item: {o:#?}"),
                    }
                },
                async {
                    let pkt = b"\x80\x60\x41\xd4\x00\x00\x00\x00\xdc\xc4\xa0\xd8hello world";
                    server
                        .send(OwnedMessage::Data {
                            channel_id: 0,
                            body: Bytes::from_static(pkt),
                        })
                        .await
                        .unwrap();
                },
            );
            drop_time = tokio::time::Instant::now();
        }

        // Drop (initiated by exiting the scope above).
        // This server advertises an ancient version of live555, so Retina
        // sends a TEARDOWN even with TCP.
        server.close().await.unwrap();
        let stale_sessions = group.stale_sessions(tokio_now());
        assert_eq!(stale_sessions.num_sessions, 1);

        // Even if repeated attempts fail, the stale session will go away on timeout.
        // The "60" in the assert below is the RFC-defined default timeout when
        // none is specified in the SETUP response.
        group.await_stale_sessions(&stale_sessions).await;
        assert_eq!(group.stale_sessions(tokio_now()).num_sessions, 0);

        // elapsed is not zero because tokio advances the time unnecessarily, grr.
        // https://github.com/tokio-rs/tokio/issues/3108
        let elapsed = tokio::time::Instant::now() - drop_time;
        assert!(
            elapsed >= std::time::Duration::from_secs(60),
            "elapsed={elapsed:?}"
        );
    }

    /// Stale sessions detected via unexpected RTSP interleaved packets should be tracked
    /// until expiration.
    #[tokio::test(start_paused = true)]
    async fn stale_file_descriptor_session() {
        init_logging();
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();
        let group = Arc::new(SessionGroup::default());
        let bogus_rtp = OwnedMessage::Data {
            channel_id: 0,
            body: Bytes::from_static(b"bogus pkt"),
        };

        let start = tokio::time::Instant::now();

        // DESCRIBE.
        tokio::join!(
            async {
                let e = Session::describe_with_conn(
                    conn,
                    SessionOptions::default()
                        .session_group(group.clone())
                        .unassigned_channel_data(UnassignedChannelDataPolicy::AssumeStaleSession),
                    url,
                )
                .await
                .map(|_s| ())
                .unwrap_err();
                assert!(matches!(*e.0, ErrorInt::RtspUnassignedChannelError { .. }));
            },
            async { server.send(bogus_rtp).await.unwrap() },
        );

        let stale_sessions = group.stale_sessions(tokio_now());
        assert_eq!(stale_sessions.num_sessions, 1);

        group.await_stale_sessions(&stale_sessions).await;
        let elapsed = tokio::time::Instant::now() - start;
        assert_eq!(group.stale_sessions(tokio_now()).num_sessions, 0);

        assert!(
            elapsed >= std::time::Duration::from_secs(LIVE555_EXPIRATION_SEC),
            "elapsed={elapsed:?}"
        );
    }

    /// Tests that a keepalive response with an unexpected `CSeq` is a fatal error.
    ///
    /// Tapo cameras reply to `SET_PARAMETER` with the previous request's
    /// `CSeq`. Retina avoids this by preferring `GET_PARAMETER`, but a mismatched
    /// response is still an error rather than being guessed to belong to the
    /// outstanding keepalive.
    #[tokio::test]
    async fn keepalive_unexpected_cseq() {
        init_logging();
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();

        // DESCRIBE.
        let (session, _) = tokio::join!(
            Session::describe_with_conn(conn, SessionOptions::default(), url),
            req_response(
                &mut server,
                msg::Method::DESCRIBE,
                response(include_bytes!("testdata/reolink_describe.txt"))
            ),
        );
        let mut session = session.unwrap();

        // SETUP.
        tokio::join!(
            async {
                session.setup(0, SetupOptions::default()).await.unwrap();
            },
            req_response(
                &mut server,
                msg::Method::SETUP,
                response(include_bytes!("testdata/reolink_setup.txt"))
            ),
        );

        // PLAY.
        let (session, _) = tokio::join!(
            session.play(PlayOptions::default()),
            req_response(
                &mut server,
                msg::Method::PLAY,
                response(include_bytes!("testdata/reolink_play.txt"))
            ),
        );
        let session = session.unwrap();
        tokio::pin!(session);

        // Pretend a previous `OPTIONS` advertised both parameter methods, and
        // make the keepalive fire almost immediately.
        let core = playing_core(&mut session);
        core.set_parameter_methods_supported();
        core.set_keepalive_deadline(
            (tokio::time::Instant::now() + std::time::Duration::from_millis(1)).into_std(),
        );
        rearm(&mut session);

        tokio::join!(
            async {
                match session.next_item().await {
                    Some(Err(e)) => {
                        assert!(
                            matches!(*e.0, ErrorInt::RtspFramingError { .. }),
                            "unexpected error: {e}"
                        );
                    }
                    o => panic!("unexpected item: {o:#?}"),
                }
            },
            async {
                let msg = server.next().await.unwrap().unwrap();
                let req = match msg.msg {
                    msg::Message::Request(r) => r,
                    o => panic!("expected keepalive request, got {o:#?}"),
                };
                assert_eq!(req.method, msg::Method::GET_PARAMETER);
                let cseq: u32 = req.headers.get("CSeq").unwrap().parse().unwrap();
                let mut headers = msg::Headers::default();
                headers.insert(
                    msg::HeaderName::CSEQ,
                    msg::HeaderValue::try_from((cseq - 1).to_string()).unwrap(),
                );
                server
                    .send(OwnedMessage::Response {
                        head: msg::Response {
                            status_code: StatusCode::try_from(400u16).unwrap(),
                            reason_phrase: "Bad Request".to_owned(),
                            headers,
                        },
                        body: Bytes::new(),
                    })
                    .await
                    .unwrap();
            },
        );
    }

    /// Tests ignoring bogus RTP and RTCP messages while waiting for PLAY response.
    #[tokio::test]
    async fn ignore_early_rtp_rtcp() {
        init_logging();
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();
        let bogus_rtp = OwnedMessage::Data {
            channel_id: 0,
            body: Bytes::from_static(b"bogus pkt"),
        };
        let bogus_rtcp = OwnedMessage::Data {
            channel_id: 1,
            body: Bytes::from_static(b"bogus pkt"),
        };

        // DESCRIBE.
        let (session, _) = tokio::join!(
            Session::describe_with_conn(conn, SessionOptions::default(), url),
            async {
                req_response(
                    &mut server,
                    msg::Method::DESCRIBE,
                    response(include_bytes!("testdata/reolink_describe.txt")),
                )
                .await;
            },
        );
        let mut session = session.unwrap();
        assert_eq!(session.streams().len(), 2);

        // SETUP.
        tokio::join!(
            async {
                session.setup(0, SetupOptions::default()).await.unwrap();
            },
            req_response(
                &mut server,
                msg::Method::SETUP,
                response(include_bytes!("testdata/reolink_setup.txt"))
            ),
        );

        // PLAY.
        let (session, _) = tokio::join!(session.play(PlayOptions::default()), async move {
            server.send(bogus_rtp).await.unwrap();
            server.send(bogus_rtcp).await.unwrap();
            req_response(
                &mut server,
                msg::Method::PLAY,
                response(include_bytes!("testdata/reolink_play.txt")),
            )
            .await
        },);
        let _session = session.unwrap();
    }

    /// A camera that sends `Session: 1 ;timeout=60`. The id is trimmed and
    /// sent back in `PLAY`, which used to panic on the invalid header value.
    #[tokio::test]
    async fn session_id_trailing_space() {
        init_logging();
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();

        // DESCRIBE.
        let (session, _) = tokio::join!(
            Session::describe_with_conn(conn, SessionOptions::default(), url),
            req_response(
                &mut server,
                msg::Method::DESCRIBE,
                response(include_bytes!("testdata/reolink_describe.txt"))
            ),
        );
        let mut session = session.unwrap();

        // SETUP.
        tokio::join!(
            async {
                session.setup(0, SetupOptions::default()).await.unwrap();
            },
            req_response(
                &mut server,
                msg::Method::SETUP,
                response(
                    b"RTSP/1.0 200 OK\r\n\
                      CSeq: 2\r\n\
                      Transport: RTP/AVP/TCP;unicast;interleaved=0-1\r\n\
                      Session: 1 ;timeout=60\r\n\r\n"
                )
            ),
        );

        // PLAY.
        let (session, _) = tokio::join!(session.play(PlayOptions::default()), async {
            let msg = server.next().await.unwrap().unwrap();
            let msg::Message::Request(r) = msg.msg else {
                panic!()
            };
            assert_eq!(r.method, msg::Method::PLAY);
            assert_eq!(r.headers.get("Session").map(|v| &**v), Some("1"));
            let (mut resp, body) = response(b"RTSP/1.0 200 OK\r\nSession: 1\r\n\r\n");
            resp.headers.insert(
                msg::HeaderName::CSEQ,
                r.headers.get("CSeq").unwrap().clone(),
            );
            server
                .send(OwnedMessage::Response { head: resp, body })
                .await
                .unwrap();
        });
        session.unwrap();
    }

    #[tokio::test]
    async fn reject_session_id_change() {
        session_id_change(SessionIdPolicy::RequireMatch, true).await
    }

    #[tokio::test]
    async fn ignore_session_id_change() {
        session_id_change(SessionIdPolicy::UseFirst, false).await
    }

    async fn session_id_change(policy: SessionIdPolicy, expect_error: bool) {
        init_logging();
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://127.0.0.1:554/camera").unwrap();
        let group = Arc::new(SessionGroup::default());

        // DESCRIBE.
        let (session, _) = tokio::join!(
            Session::describe_with_conn(
                conn,
                SessionOptions::default()
                    .session_group(group.clone())
                    .session_id(policy),
                url
            ),
            req_response(
                &mut server,
                msg::Method::DESCRIBE,
                response(include_bytes!("testdata/h264dvr_describe.txt"))
            ),
        );
        let mut session = session.unwrap();
        assert_eq!(session.streams().len(), 2);

        // SETUP.
        tokio::join!(
            async {
                session
                    .setup(
                        0,
                        SetupOptions::default()
                            .transport(Transport::Udp(UdpTransportOptions::default())),
                    )
                    .await
                    .unwrap();
            },
            req_response(
                &mut server,
                msg::Method::SETUP,
                response(include_bytes!("testdata/h264dvr_setup_video.txt"))
            ),
        );

        tokio::join!(
            async {
                let r = session
                    .setup(
                        1,
                        SetupOptions::default()
                            .transport(Transport::Udp(UdpTransportOptions::default())),
                    )
                    .await;
                if expect_error {
                    let e = r.unwrap_err();
                    assert!(matches!(*e.0, ErrorInt::RtspResponseError { .. }));
                } else {
                    r.unwrap();
                }
            },
            req_response(
                &mut server,
                msg::Method::SETUP,
                response(include_bytes!("testdata/h264dvr_setup_audio.txt"))
            ),
        );
    }

    /// Sends `DESCRIBE` to a server which answers with the raw bytes `resp`,
    /// then holds the connection open.
    async fn describe_raw(
        options: SessionOptions,
        resp: Vec<u8>,
    ) -> Result<Session<Described>, Error> {
        use tokio::io::{AsyncReadExt as _, AsyncWriteExt as _};
        let (client, mut server) = socketpair().await;
        let conn = crate::tokio::Connection::from_stream(client).unwrap();
        let url = Url::parse("rtsp://127.0.0.1:554/camera").unwrap();
        let serve = async move {
            let mut req = Vec::new();
            while !req.ends_with(b"\r\n\r\n") {
                let mut buf = [0u8; 1024];
                let n = server.read(&mut buf).await.unwrap();
                assert_ne!(n, 0, "client hung up before sending its request");
                req.extend_from_slice(&buf[..n]);
            }
            // The client may hang up partway through; that's fine.
            let _ = server.write_all(&resp).await;
            server
        };
        let (session, _server) = tokio::join!(
            tokio::time::timeout(
                std::time::Duration::from_secs(10),
                Session::describe_with_conn(conn, options, url),
            ),
            serve,
        );
        session.expect("DESCRIBE should finish rather than buffer forever")
    }

    fn assert_too_large(r: Result<Session<Described>, Error>) {
        let e = r.map(|_| ()).unwrap_err();
        assert!(
            matches!(*e.0, ErrorInt::RtspFramingError { .. }),
            "expected framing error, got {e}"
        );
        assert!(e.to_string().contains("exceeds max_message_size"), "{e}");
    }

    /// Appends header lines to `resp` until it's at least 2 MiB.
    fn push_junk_headers(resp: &mut Vec<u8>) {
        let mut i = 0;
        while resp.len() < 2 << 20 {
            resp.extend_from_slice(format!("X-Junk-{i}: {:0>64}\r\n", 0).as_bytes());
            i += 1;
        }
    }

    /// The limit rejects a declared body length up front, without waiting for
    /// the body.
    #[tokio::test]
    async fn describe_rejects_huge_content_length() {
        init_logging();
        let resp = b"RTSP/1.0 200 OK\r\nCSeq: 1\r\nContent-Length: 1000000000\r\n\r\n";
        let options = SessionOptions::default().max_message_size(64 << 10);
        assert_too_large(describe_raw(options, resp.to_vec()).await);
    }

    /// The limit rejects a header block that never ends.
    #[tokio::test]
    async fn describe_rejects_endless_headers() {
        init_logging();
        let mut resp = b"RTSP/1.0 200 OK\r\nCSeq: 1\r\n".to_vec();
        push_junk_headers(&mut resp);
        let options = SessionOptions::default().max_message_size(64 << 10);
        assert_too_large(describe_raw(options, resp).await);
    }

    /// A response exactly at the limit passes; one byte over fails.
    #[tokio::test]
    async fn describe_max_message_size() {
        init_logging();
        let (mut head, body) = response(include_bytes!("testdata/reolink_describe.txt"));
        head.headers.insert(
            msg::HeaderName::CSEQ,
            msg::HeaderValue::try_from("1").unwrap(),
        );
        let mut resp = Vec::new();
        OwnedMessage::Response { head, body }
            .write(&mut resp)
            .unwrap();
        let len = resp.len();
        let session = describe_raw(
            SessionOptions::default().max_message_size(len),
            resp.clone(),
        )
        .await
        .unwrap();
        assert_eq!(session.streams().len(), 2);
        assert_too_large(
            describe_raw(SessionOptions::default().max_message_size(len - 1), resp).await,
        );
    }

    /// By default there's no limit: a 2 MiB response is accepted.
    #[tokio::test]
    async fn describe_no_max_message_size_by_default() {
        init_logging();
        let (mut head, body) = response(include_bytes!("testdata/reolink_describe.txt"));
        head.headers.insert(
            msg::HeaderName::CSEQ,
            msg::HeaderValue::try_from("1").unwrap(),
        );
        let mut wire = Vec::new();
        OwnedMessage::Response { head, body }
            .write(&mut wire)
            .unwrap();
        let status_line_len = wire.windows(2).position(|w| w == b"\r\n").unwrap() + 2;
        let (status_line, rest) = wire.split_at(status_line_len);
        let mut resp = status_line.to_vec();
        push_junk_headers(&mut resp);
        resp.extend_from_slice(rest);
        let session = describe_raw(SessionOptions::default(), resp).await.unwrap();
        assert_eq!(session.streams().len(), 2);
    }

    /// Returns `session`'s core. After moving its deadlines, call [`rearm`].
    fn playing_core(session: &mut Session<Playing>) -> &mut PlayingCore {
        session.0.playing_core()
    }

    /// Resets `session`'s timer to its core's next deadline.
    fn rearm(session: &mut Session<Playing>) {
        let deadline = tokio::time::Instant::from_std(playing_core(session).poll_timeout());
        session.0.keepalive_timer = Some(Box::pin(tokio::time::sleep_until(deadline)));
    }

    /// Effectively disables keepalives, so paused time auto-advances only to
    /// receiver reports. Returns the report writer's SSRC and CNAME and when
    /// the first reports are due.
    fn keepalive_off(session: &mut Session<Playing>) -> (u32, String, tokio::time::Instant) {
        let core = playing_core(session);
        core.set_keepalive_deadline(
            (tokio::time::Instant::now() + std::time::Duration::from_secs(86_400)).into_std(),
        );
        let reports = core.reports_mut().unwrap();
        let r = (
            reports.writer.ssrc,
            reports.writer.cname.clone(),
            tokio::time::Instant::from_std(reports.due),
        );
        rearm(session);
        r
    }

    /// Moves `session`'s next receiver reports to `due`.
    fn set_report_due(session: &mut Session<Playing>, due: tokio::time::Instant) {
        playing_core(session).reports_mut().unwrap().due = due.into_std();
        rearm(session);
    }

    /// Describes, sets up stream 0 via TCP, and plays a session against the
    /// mock server, using the Reolink test data.
    async fn play_tcp(options: SessionOptions) -> (Session<Playing>, crate::tokio::Connection) {
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();
        let (session, _) = tokio::join!(
            Session::describe_with_conn(conn, options, url),
            req_response(
                &mut server,
                msg::Method::DESCRIBE,
                response(include_bytes!("testdata/reolink_describe.txt"))
            ),
        );
        let mut session = session.unwrap();
        tokio::join!(
            async {
                session.setup(0, SetupOptions::default()).await.unwrap();
            },
            req_response(
                &mut server,
                msg::Method::SETUP,
                response(include_bytes!("testdata/reolink_setup.txt"))
            ),
        );
        let (session, _) = tokio::join!(
            session.play(PlayOptions::default()),
            req_response(
                &mut server,
                msg::Method::PLAY,
                response(include_bytes!("testdata/reolink_play.txt"))
            ),
        );
        (session.unwrap(), server)
    }

    /// The SSRC in the Reolink test data's RTP packets.
    const REOLINK_SSRC: u32 = 0xdcc4a0d8;

    fn rtp_pkt(seq: u16, timestamp: u32) -> Bytes {
        let mut pkt = vec![0x80, 0x60];
        pkt.extend_from_slice(&seq.to_be_bytes());
        pkt.extend_from_slice(&timestamp.to_be_bytes());
        pkt.extend_from_slice(&REOLINK_SSRC.to_be_bytes());
        pkt.extend_from_slice(b"hello world");
        Bytes::from(pkt)
    }

    fn sender_report_pkt(ntp: u64, timestamp: u32) -> Bytes {
        let mut pkt = vec![0x80, 200, 0, 6];
        pkt.extend_from_slice(&REOLINK_SSRC.to_be_bytes());
        pkt.extend_from_slice(&ntp.to_be_bytes());
        pkt.extend_from_slice(&timestamp.to_be_bytes());
        pkt.extend_from_slice(&[0; 8]); // packet and octet counts.
        Bytes::from(pkt)
    }

    /// Polls `session` (which must yield nothing) until `server` receives a
    /// message, and returns it with its body.
    async fn recv_while_polling(
        session: &mut Pin<&mut Session<Playing>>,
        server: &mut crate::tokio::Connection,
    ) -> (msg::Message, Bytes) {
        tokio::select! {
            item = session.next_item() => panic!("unexpected item: {item:#?}"),
            msg = server.next() => {
                let msg = msg.unwrap().unwrap();
                let body = server.body_bytes(msg.body_pos, msg.body_len);
                (msg.msg, body)
            }
        }
    }

    /// Like [`recv_while_polling`], expecting interleaved data on `channel_id`.
    async fn recv_data_while_polling(
        session: &mut Pin<&mut Session<Playing>>,
        server: &mut crate::tokio::Connection,
        channel_id: u8,
    ) -> Bytes {
        match recv_while_polling(session, server).await {
            (msg::Message::Data(d), body) => {
                assert_eq!(d.channel_id, channel_id);
                body
            }
            (o, _) => panic!("expected data, got {o:#?}"),
        }
    }

    /// Reports are sent on the stream's RTCP channel when due: an empty RR
    /// before any RTP has arrived, then one describing what has.
    #[tokio::test(start_paused = true)]
    async fn receiver_reports_tcp() {
        init_logging();
        let (session, mut server) = play_tcp(
            SessionOptions::default()
                .unassigned_channel_data(UnassignedChannelDataPolicy::Ignore)
                .receiver_reports(ReceiverReportPolicy::Always),
        )
        .await;
        tokio::pin!(session);

        // Keep only the report deadline, so paused time auto-advances to it.
        // See the comment in `simple`.
        let (ssrc, cname, due) = keepalive_off(&mut session);

        // RFC 3550 section 6.2: the first report may come after half the 5 s
        // minimum, randomized and compensated as in section 6.3.1.
        let played = tokio::time::Instant::now();
        assert!(due - played >= std::time::Duration::from_millis(1026));
        assert!(due - played < std::time::Duration::from_millis(3079));

        // Nothing has arrived yet, so the first report is an empty RR.
        let report = recv_data_while_polling(&mut session, &mut server, 1).await;
        assert!(tokio::time::Instant::now() >= due);
        receiver_report::tests::parse_report(&report, ssrc, 0, &cname);

        // Disarm the timer while packets arrive. Otherwise, while the session
        // waits on the socket, paused time can auto-advance to the timer, so
        // packets arrive at different instants and a report can slip out
        // between them. `set_report_due` below rearms it.
        session.0.keepalive_timer = None;
        let ntp = 0xe436_2f99_cccc_cccc;
        tokio::join!(
            async {
                for _ in 0..4 {
                    match session.next_item().await {
                        Some(Ok(_)) => {}
                        o => panic!("unexpected item: {o:#?}"),
                    }
                }
            },
            async {
                // seq 0x41d6 is lost; 0x41d7 is 6000 ticks late relative to
                // 0x41d5 (all arrive at the same paused instant).
                for (channel_id, body) in [
                    (0, rtp_pkt(0x41d4, 1_000)),
                    (0, rtp_pkt(0x41d5, 4_000)),
                    (0, rtp_pkt(0x41d7, 10_000)),
                    (1, sender_report_pkt(ntp, 10_000)),
                ] {
                    server
                        .send(OwnedMessage::Data { channel_id, body })
                        .await
                        .unwrap();
                }
            },
        );
        tokio::time::advance(std::time::Duration::from_millis(1500)).await;
        set_report_due(&mut session, tokio::time::Instant::now());

        // A report may have slipped out before the packets arrived; skip any
        // empty one.
        let block = loop {
            let report = recv_data_while_polling(&mut session, &mut server, 1).await;
            if report[0] & 0x1f == 0 {
                continue;
            }
            let rr = receiver_report::tests::parse_report(&report, ssrc, 1, &cname);
            break receiver_report::tests::parse_block(rr);
        };
        assert_eq!(
            block,
            receiver_report::ReportBlock {
                ssrc: REOLINK_SSRC,
                fraction_lost: 85, // 1 of 3 expected since 0x41d5, the first valid packet.
                cumulative_lost: 1,
                extended_highest_seq: 0x41d7,
                jitter: 375, // 6000 / 16
                lsr: 0x2f99_cccc,
                dlsr: 98_304, // 1.5 s in units of 1/65536 s
            }
        );
    }

    /// Reports keep coming on schedule while nothing else wakes the session.
    #[tokio::test(start_paused = true)]
    async fn receiver_reports_tcp_quiet() {
        init_logging();
        let (mut session, mut server) =
            play_tcp(SessionOptions::default().receiver_reports(ReceiverReportPolicy::Always))
                .await;
        let (ssrc, cname, due) = keepalive_off(&mut session);

        // Poll the session from its own task, so only its own wakers wake it.
        let session = tokio::spawn(async move {
            let item = session.next_item().await;
            panic!("unexpected item: {item:#?}");
        });
        tokio::time::timeout(std::time::Duration::from_secs(60), async {
            for i in 0..3 {
                let msg = server.next().await.unwrap().unwrap();
                let msg::Message::Data(d) = msg.msg else {
                    panic!("expected data, got {:#?}", msg.msg);
                };
                assert_eq!(d.channel_id, 1);
                let report = server.body_bytes(msg.body_pos, msg.body_len);
                receiver_report::tests::parse_report(&report, ssrc, 0, &cname);

                // Each report is at least 5 s × 0.5 / (e - 3/2) after the last.
                assert!(
                    tokio::time::Instant::now() >= due + i * std::time::Duration::from_millis(2052)
                );
            }
        })
        .await
        .unwrap();
        session.abort();
    }

    /// A keepalive and a report due at once both reach the server intact, in
    /// that order.
    #[tokio::test]
    async fn receiver_report_and_keepalive_back_to_back() {
        init_logging();
        let (session, mut server) =
            play_tcp(SessionOptions::default().receiver_reports(ReceiverReportPolicy::Always))
                .await;
        tokio::pin!(session);
        let deadline = tokio::time::Instant::now() + std::time::Duration::from_millis(1);
        let core = playing_core(&mut session);
        core.set_keepalive_deadline(deadline.into_std());
        let reports = core.reports_mut().unwrap();
        reports.due = deadline.into_std();
        let (ssrc, cname) = (reports.writer.ssrc, reports.writer.cname.clone());
        rearm(&mut session);

        match recv_while_polling(&mut session, &mut server).await {
            (msg::Message::Request(r), body) => {
                assert_eq!(r.method, msg::Method::OPTIONS);
                assert!(r.headers.get("CSeq").is_some());
                assert!(body.is_empty());
            }
            (o, _) => panic!("expected keepalive request, got {o:#?}"),
        }
        let report = recv_data_while_polling(&mut session, &mut server, 1).await;
        receiver_report::tests::parse_report(&report, ssrc, 0, &cname);
    }

    /// Without `SessionOptions::receiver_reports`, no RTCP is written.
    #[tokio::test(start_paused = true)]
    async fn receiver_reports_off_by_default() {
        init_logging();
        let (session, mut server) = play_tcp(SessionOptions::default()).await;
        tokio::pin!(session);
        session.0.keepalive_timer = None;
        let core = playing_core(&mut session);
        assert!(core.reports_mut().is_none());
        assert!(!core.has_reception_stats());
        tokio::join!(
            async {
                match session.next_item().await {
                    Some(Ok(PlayingItem::Rtp(_))) => {}
                    o => panic!("unexpected item: {o:#?}"),
                }
            },
            async {
                server
                    .send(OwnedMessage::Data {
                        channel_id: 0,
                        body: rtp_pkt(0x41d4, 0),
                    })
                    .await
                    .unwrap();
            },
        );
        let r = tokio::time::timeout(
            std::time::Duration::from_secs(60),
            recv_while_polling(&mut session, &mut server),
        )
        .await;
        assert!(r.is_err(), "unexpected message: {:#?}", r.map(|(m, _)| m));
    }

    /// Over UDP, reports go from the stream's RTCP socket to the server's RTCP
    /// port.
    #[tokio::test]
    async fn receiver_reports_udp() {
        init_logging();
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();

        // DESCRIBE.
        let (session, _) = tokio::join!(
            Session::describe_with_conn(
                conn,
                SessionOptions::default().receiver_reports(ReceiverReportPolicy::Always),
                url
            ),
            req_response(
                &mut server,
                msg::Method::DESCRIBE,
                response(include_bytes!("testdata/reolink_describe.txt"))
            ),
        );
        let mut session = session.unwrap();

        // SETUP, with server sockets for the stream.
        let server_udp = crate::tokio::UdpPair::for_ip(IpAddr::V4(Ipv4Addr::LOCALHOST)).unwrap();
        let ((), client_rtp_port) = tokio::join!(
            async {
                session
                    .setup(
                        0,
                        SetupOptions::default().transport(Transport::Udp(Default::default())),
                    )
                    .await
                    .unwrap();
            },
            async {
                let msg = server.next().await.unwrap().unwrap();
                let msg::Message::Request(req) = msg.msg else {
                    panic!("expected SETUP request");
                };
                assert_eq!(req.method, msg::Method::SETUP);
                let transport: &str = req.headers.get("Transport").unwrap();
                let client_port = transport
                    .split(';')
                    .find_map(|p| p.strip_prefix("client_port="))
                    .unwrap()
                    .to_owned();
                let client_rtp_port: u16 = client_port.split('-').next().unwrap().parse().unwrap();
                let mut headers = msg::Headers::default();
                for (name, value) in [
                    ("CSeq", req.headers.get("CSeq").unwrap().to_string()),
                    ("Session", "F8F8E425".to_owned()),
                    (
                        "Transport",
                        format!(
                            "RTP/AVP/UDP;unicast;client_port={client_port};server_port={}-{}",
                            server_udp.rtp_port,
                            server_udp.rtp_port + 1
                        ),
                    ),
                ] {
                    headers.insert(
                        msg::HeaderName::try_from(name).unwrap(),
                        msg::HeaderValue::try_from(value).unwrap(),
                    );
                }
                server
                    .send(OwnedMessage::Response {
                        head: msg::Response {
                            status_code: StatusCode::OK,
                            reason_phrase: "OK".to_owned(),
                            headers,
                        },
                        body: Bytes::new(),
                    })
                    .await
                    .unwrap();
                client_rtp_port
            },
        );
        let client_rtcp_addr = SocketAddr::new(Ipv4Addr::LOCALHOST.into(), client_rtp_port + 1);

        // The firewall hole-punching packet arrives first.
        let mut buf = [0u8; 1500];
        let (n, from) = server_udp.rtcp_socket.recv_from(&mut buf).await.unwrap();
        assert_eq!((&buf[..n], from), (&HOLE_PUNCH_RTCP[..], client_rtcp_addr));

        // PLAY.
        let (session, _) = tokio::join!(
            session.play(PlayOptions::default()),
            req_response(
                &mut server,
                msg::Method::PLAY,
                response(include_bytes!("testdata/reolink_play.txt"))
            ),
        );
        let session = session.unwrap();
        tokio::pin!(session);
        let (ssrc, cname, _) = keepalive_off(&mut session);
        set_report_due(
            &mut session,
            tokio::time::Instant::now() + std::time::Duration::from_secs(3600),
        );

        // RTP.
        let client_rtp_addr = SocketAddr::new(Ipv4Addr::LOCALHOST.into(), client_rtp_port);
        for seq in [0x41d4, 0x41d5] {
            server_udp
                .rtp_socket
                .send_to(&rtp_pkt(seq, 0), client_rtp_addr)
                .await
                .unwrap();
            match session.next_item().await {
                Some(Ok(PlayingItem::Rtp(p))) => assert_eq!(p.header().sequence_number(), seq),
                o => panic!("unexpected item: {o:#?}"),
            }
        }

        // The report.
        set_report_due(&mut session, tokio::time::Instant::now());
        let (n, from) = tokio::select! {
            item = session.next_item() => panic!("unexpected item: {item:#?}"),
            r = server_udp.rtcp_socket.recv_from(&mut buf) => r.unwrap(),
        };
        assert_eq!(from, client_rtcp_addr);
        let rr = receiver_report::tests::parse_report(&buf[..n], ssrc, 1, &cname);
        let block = receiver_report::tests::parse_block(rr);
        assert_eq!(
            (
                block.ssrc,
                block.extended_highest_seq,
                block.cumulative_lost
            ),
            (REOLINK_SSRC, 0x41d5, 0)
        );
    }

    #[test]
    fn receiver_report_policy_from_str() {
        for policy in [
            ReceiverReportPolicy::Default,
            ReceiverReportPolicy::Never,
            ReceiverReportPolicy::Always,
        ] {
            let parsed: ReceiverReportPolicy = policy.to_string().parse().unwrap();
            assert_eq!(parsed.enabled(), policy.enabled());
        }
        assert!(!ReceiverReportPolicy::default().enabled());
        assert!("sometimes".parse::<ReceiverReportPolicy>().is_err());
    }

    /// ONVIF backchannel tests.
    #[cfg(feature = "unstable-send")]
    mod backchannel {
        use super::*;

        const BACKCHANNEL_URL: &str = "rtsp://192.168.0.1/";
        const BACKCHANNEL_DESCRIBE: &[u8] =
            include_bytes!("testdata/onvif_backchannel_describe.txt");
        const BACKCHANNEL_SETUP_VIDEO: &[u8] = b"RTSP/1.0 200 OK\r\n\
            CSeq: 0\r\n\
            Session: 12345678;timeout=60\r\n\
            Transport: RTP/AVP/TCP;unicast;interleaved=0-1\r\n\r\n";
        const BACKCHANNEL_SETUP_BACK: &[u8] = b"RTSP/1.0 200 OK\r\n\
            CSeq: 0\r\n\
            Session: 12345678;timeout=60\r\n\
            Transport: RTP/AVP/TCP;unicast;interleaved=2-3;ssrc=0BADF00D\r\n\r\n";
        const BACKCHANNEL_PLAY: &[u8] = b"RTSP/1.0 200 OK\r\n\
            CSeq: 0\r\n\
            Session: 12345678\r\n\
            RTP-Info: url=rtsp://192.168.0.1/video;seq=1;rtptime=0\r\n\r\n";
        const BACKCHANNEL_TEARDOWN: &[u8] = b"RTSP/1.0 200 OK\r\n\
            CSeq: 0\r\n\
            Session: 12345678\r\n\r\n";

        /// Returns a timestamp at the 8 kHz clock rate of the backchannel in
        /// [`BACKCHANNEL_DESCRIBE`].
        fn ts(timestamp: i64) -> crate::Timestamp {
            crate::Timestamp::new(timestamp, NonZeroU32::new(8_000).unwrap(), 0).unwrap()
        }

        /// Like [`next_data`], but polls `session` meanwhile, so it writes what's
        /// been queued. Fails if the session yields an item.
        async fn next_data_while_polling(
            session: &mut Session<Playing>,
            server: &mut crate::tokio::Connection,
        ) -> (u8, Bytes) {
            tokio::select! {
                d = next_data(server) => d,
                o = session.next_item() => panic!("unexpected item: {o:#?}"),
            }
        }

        /// Receives an interleaved data message, returning its channel id and body.
        ///
        /// Fails rather than hanging if none arrives.
        async fn next_data(server: &mut crate::tokio::Connection) -> (u8, Bytes) {
            let msg = tokio::time::timeout(std::time::Duration::from_secs(10), server.next())
                .await
                .expect("expected interleaved data")
                .unwrap()
                .unwrap();
            match msg.msg {
                msg::Message::Data(d) => (
                    d.channel_id,
                    server.body_bytes(msg.body_pos, u32::from(d.body_len)),
                ),
                o => panic!("expected interleaved data, got {o:#?}"),
            }
        }

        /// Returns the `Require` header of `req`, if any.
        fn require(req: &msg::Request) -> Option<&str> {
            req.headers.get("Require").map(|v| &**v)
        }

        /// The `Require` header is sent on `DESCRIBE` only when the caller asks
        /// for a backchannel, and `a=sendonly` media are only then sending streams.
        #[tokio::test]
        async fn backchannel_require_only_when_requested() {
            init_logging();
            for backchannel in [false, true] {
                let (conn, mut server) = connect_to_mock().await;
                let (session, req) = tokio::join!(
                    Session::describe_with_conn(
                        conn,
                        SessionOptions::default().backchannel(backchannel),
                        Url::parse(BACKCHANNEL_URL).unwrap(),
                    ),
                    req_response_returning_req(
                        &mut server,
                        msg::Method::DESCRIBE,
                        response(BACKCHANNEL_DESCRIBE)
                    ),
                );
                let session = session.unwrap();
                let directions: Vec<_> = session.streams().iter().map(Stream::direction).collect();
                if backchannel {
                    assert_eq!(require(&req), Some("www.onvif.org/ver20/backchannel"));
                    assert_eq!(
                        directions,
                        [
                            StreamDirection::Receiving,
                            StreamDirection::Receiving,
                            StreamDirection::Sending
                        ]
                    );
                } else {
                    assert_eq!(require(&req), None);
                    assert_eq!(directions, [StreamDirection::Receiving; 3]);
                }
            }
        }

        /// A server without backchannel support answers `551 Option not supported`
        /// (ONVIF Streaming Specification section 5.3.2). The error carries the
        /// status and a hint. Other errors, or a 551 without the backchannel
        /// option, have no hint.
        #[tokio::test]
        async fn backchannel_describe_unsupported() {
            init_logging();
            for (backchannel, raw, status, hint) in [
                (
                    true,
                    &b"RTSP/1.0 551 Option not supported\r\n\
                       CSeq: 0\r\n\
                       Unsupported: www.onvif.org/ver20/backchannel\r\n\r\n"[..],
                    551,
                    true,
                ),
                (
                    true,
                    b"RTSP/1.0 404 Not Found\r\nCSeq: 0\r\n\r\n",
                    404,
                    false,
                ),
                (
                    false,
                    b"RTSP/1.0 551 Option not supported\r\nCSeq: 0\r\n\r\n",
                    551,
                    false,
                ),
            ] {
                let (conn, mut server) = connect_to_mock().await;
                let (session, _) = tokio::join!(
                    Session::describe_with_conn(
                        conn,
                        SessionOptions::default().backchannel(backchannel),
                        Url::parse(BACKCHANNEL_URL).unwrap(),
                    ),
                    req_response(&mut server, msg::Method::DESCRIBE, response(raw)),
                );
                let e = session.map(|_| ()).unwrap_err();
                assert_eq!(e.status_code(), Some(status));
                let msg = e.to_string();
                assert_eq!(msg.contains("ONVIF backchannel"), hint, "{msg}");
            }
        }

        /// `SETUP` of a sending stream over UDP fails without a request, and with
        /// TCP carries the `Require` header.
        #[tokio::test]
        async fn backchannel_setup() {
            init_logging();
            let (conn, mut server) = connect_to_mock().await;
            let (session, _) = tokio::join!(
                Session::describe_with_conn(
                    conn,
                    SessionOptions::default().backchannel(true),
                    Url::parse(BACKCHANNEL_URL).unwrap(),
                ),
                req_response(
                    &mut server,
                    msg::Method::DESCRIBE,
                    response(BACKCHANNEL_DESCRIBE)
                ),
            );
            let mut session = session.unwrap();
            let e = session
                .setup(
                    2,
                    SetupOptions::default()
                        .transport(Transport::Udp(UdpTransportOptions::default())),
                )
                .await
                .unwrap_err();
            assert!(matches!(*e.0, ErrorInt::Unsupported(_)), "{e}");

            // The next request the server sees is the TCP `SETUP`.
            let (r, req) = tokio::join!(
                session.setup(2, SetupOptions::default()),
                req_response_returning_req(
                    &mut server,
                    msg::Method::SETUP,
                    response(BACKCHANNEL_SETUP_BACK)
                ),
            );
            r.unwrap();
            assert_eq!(
                req.request_uri.as_ref().unwrap().as_str(),
                "rtsp://192.168.0.1/audioback"
            );
            assert_eq!(require(&req), Some("www.onvif.org/ver20/backchannel"));
            assert_eq!(
                req.headers.get("Transport").map(|v| &**v),
                Some("RTP/AVP/TCP;unicast;interleaved=0-1")
            );
        }

        /// A refused `SETUP` of the backchannel leaves the session usable: it
        /// plays the other streams, and as no sending stream was set up, `PLAY`
        /// and `TEARDOWN` go without the `Require` header and sending fails.
        #[tokio::test]
        async fn backchannel_setup_refused() {
            init_logging();
            let (conn, mut server) = connect_to_mock().await;
            let (session, _) = tokio::join!(
                Session::describe_with_conn(
                    conn,
                    SessionOptions::default().backchannel(true),
                    Url::parse(BACKCHANNEL_URL).unwrap(),
                ),
                req_response(
                    &mut server,
                    msg::Method::DESCRIBE,
                    response(BACKCHANNEL_DESCRIBE)
                ),
            );
            let mut session = session.unwrap();
            let (r, _) = tokio::join!(
                session.setup(0, SetupOptions::default()),
                req_response(
                    &mut server,
                    msg::Method::SETUP,
                    response(BACKCHANNEL_SETUP_VIDEO)
                ),
            );
            r.unwrap();
            let (r, _) = tokio::join!(
                session.setup(2, SetupOptions::default()),
                req_response(
                    &mut server,
                    msg::Method::SETUP,
                    response(b"RTSP/1.0 453 Not Enough Bandwidth\r\nCSeq: 0\r\n\r\n")
                ),
            );
            assert_eq!(r.unwrap_err().status_code(), Some(453));
            let (session, req) = tokio::join!(
                session.play(PlayOptions::default()),
                req_response_returning_req(
                    &mut server,
                    msg::Method::PLAY,
                    response(BACKCHANNEL_PLAY)
                ),
            );
            assert_eq!(require(&req), None);
            let mut session = session.unwrap();
            let mut sender = crate::rtp::Sender::new(0, crate::rtp::SenderOptions::default());
            let e = session
                .queue_rtp(2, &sender.packet(ts(0), false, &[&[0xff; 160]]))
                .unwrap_err();
            assert!(matches!(*e.0, ErrorInt::FailedPrecondition(_)), "{e}");
            drop(session);
            let req = req_response_returning_req(
                &mut server,
                msg::Method::TEARDOWN,
                response(BACKCHANNEL_TEARDOWN),
            )
            .await;
            assert_eq!(require(&req), None);
        }

        /// Plays a video stream and a backchannel on one connection: checks the
        /// `Require` headers and the exact interleaved RTP and RTCP bytes sent,
        /// receives on both streams, and checks errors for bad packets.
        #[tokio::test]
        async fn backchannel_send() {
            init_logging();
            let (conn, mut server) = connect_to_mock().await;

            // DESCRIBE.
            let (session, req) = tokio::join!(
                Session::describe_with_conn(
                    conn,
                    SessionOptions::default().backchannel(true),
                    Url::parse(BACKCHANNEL_URL).unwrap(),
                ),
                req_response_returning_req(
                    &mut server,
                    msg::Method::DESCRIBE,
                    response(BACKCHANNEL_DESCRIBE)
                ),
            );
            assert_eq!(require(&req), Some("www.onvif.org/ver20/backchannel"));
            let mut session = session.unwrap();

            // SETUP video, without `Require`, then the backchannel, with it.
            let (r, req) = tokio::join!(
                session.setup(0, SetupOptions::default()),
                req_response_returning_req(
                    &mut server,
                    msg::Method::SETUP,
                    response(BACKCHANNEL_SETUP_VIDEO)
                ),
            );
            r.unwrap();
            assert_eq!(require(&req), None);
            let (r, req) = tokio::join!(
                session.setup(2, SetupOptions::default()),
                req_response_returning_req(
                    &mut server,
                    msg::Method::SETUP,
                    response(BACKCHANNEL_SETUP_BACK)
                ),
            );
            r.unwrap();
            assert_eq!(require(&req), Some("www.onvif.org/ver20/backchannel"));

            // PLAY, with `Require`. `RTP-Info` describes only the video stream.
            let (session, req) = tokio::join!(
                session.play(PlayOptions::default()),
                req_response_returning_req(
                    &mut server,
                    msg::Method::PLAY,
                    response(BACKCHANNEL_PLAY)
                ),
            );
            assert_eq!(require(&req), Some("www.onvif.org/ver20/backchannel"));
            let mut session = session.unwrap();

            // The caller's sender, with a fixed SSRC, sequence number, and
            // timestamp offset so the bytes are predictable. Start near wraparound.
            let mut sender = crate::rtp::Sender::new(
                session.streams()[2].rtp_payload_type(),
                crate::rtp::SenderOptions::default()
                    .ssrc(0x0102_0304)
                    .initial_sequence_number(0xfffe)
                    .timestamp_offset(0xffff_ff00),
            );

            // Packet 1 and a sender report go out on the backchannel's RTP and
            // RTCP channels, in order, as the session is polled.
            session
                .queue_rtp(2, &sender.packet(ts(0), true, &[&[0xff; 100], &[0xff; 60]]))
                .unwrap();
            let sr = sender.sender_report(crate::NtpTimestamp(0x1234), ts(0), "abcdefghijklmnop");
            session.queue_rtcp(2, &sr).unwrap();
            assert_eq!(session.queued_len(), 4 + 12 + 160 + 4 + sr.len());
            let (channel, rtp) = next_data_while_polling(&mut session, &mut server).await;
            assert_eq!(channel, 2);
            let mut expected = b"\x80\x80\xff\xfe\xff\xff\xff\x00\x01\x02\x03\x04".to_vec();
            expected.extend_from_slice(&[0xff; 160]);
            crate::testutil::assert_eq_hex!(rtp, expected);
            let (channel, rtcp) = next_data_while_polling(&mut session, &mut server).await;
            assert_eq!(channel, 3);
            crate::testutil::assert_eq_hex!(rtcp, sr);
            assert_eq!(session.queued_len(), 0);

            // Packets for the wrong stream fail without queueing anything.
            let pkt = sender.packet(ts(160), false, &[&[0xff; 160]]);
            for (stream_i, want) in [
                (0, "isn't an ONVIF backchannel"),
                (1, "isn't an ONVIF backchannel"),
                (3, "has only 3 streams"),
            ] {
                let e = session.queue_rtp(stream_i, &pkt).unwrap_err();
                assert!(matches!(*e.0, ErrorInt::InvalidArgument(_)), "{e}");
                assert!(e.to_string().contains(want), "{e} should contain {want:?}");
                let e = session.queue_rtcp(stream_i, &sr).unwrap_err();
                assert!(e.to_string().contains(want), "{e} should contain {want:?}");
            }
            assert_eq!(session.queued_len(), 0);

            // Receive while sending: RTP on the backchannel's channel is ignored;
            // video RTP and the server's RTCP receiver report come through.
            for (channel_id, body) in [
                (2, &b"\x80\x00\x00\x01\x00\x00\x00\x00\xaa\xbb\xcc\xdd?"[..]),
                (
                    0,
                    &b"\x80\x1a\x00\x01\x00\x00\x00\x00\x11\x22\x33\x44hello"[..],
                ),
                (3, &b"\x80\xc9\x00\x01\xaa\xbb\xcc\xdd"[..]),
            ] {
                server
                    .send(OwnedMessage::Data {
                        channel_id,
                        body: Bytes::from_static(body),
                    })
                    .await
                    .unwrap();
            }
            match session.next_item().await {
                Some(Ok(PlayingItem::Rtp(p))) => {
                    assert_eq!(p.stream_id(), 0);
                    assert_eq!(p.packet().payload().to_vec(), b"hello");
                }
                o => panic!("unexpected item: {o:#?}"),
            }
            match session.next_item().await {
                Some(Ok(PlayingItem::Rtcp(p))) => {
                    assert_eq!(p.stream_id(), 2);
                    assert_eq!(p.raw(), b"\x80\xc9\x00\x01\xaa\xbb\xcc\xdd");
                }
                o => panic!("unexpected item: {o:#?}"),
            }

            // TEARDOWN carries `Require`, as in the ONVIF spec's example.
            drop(session);
            let req = req_response_returning_req(
                &mut server,
                msg::Method::TEARDOWN,
                response(BACKCHANNEL_TEARDOWN),
            )
            .await;
            assert_eq!(require(&req), Some("www.onvif.org/ver20/backchannel"));
        }

        /// Describes [`BACKCHANNEL_DESCRIBE`] with the backchannel option, sets up
        /// only the backchannel (stream 2), and plays, with keepalives disabled.
        async fn play_backchannel(
            conn: crate::tokio::Connection,
            server: &mut crate::tokio::Connection,
        ) -> Session<Playing> {
            let (session, _) = tokio::join!(
                Session::describe_with_conn(
                    conn,
                    SessionOptions::default().backchannel(true),
                    Url::parse(BACKCHANNEL_URL).unwrap(),
                ),
                req_response(
                    server,
                    msg::Method::DESCRIBE,
                    response(BACKCHANNEL_DESCRIBE)
                ),
            );
            let mut session = session.unwrap();
            let (r, _) = tokio::join!(
                session.setup(2, SetupOptions::default()),
                req_response(server, msg::Method::SETUP, response(BACKCHANNEL_SETUP_BACK)),
            );
            r.unwrap();
            let (session, _) = tokio::join!(
                session.play(PlayOptions::default()),
                req_response(server, msg::Method::PLAY, response(BACKCHANNEL_PLAY)),
            );
            let mut session = session.unwrap();
            session.0.keepalive_timer = None;
            session
        }

        /// Sends `server` a response to a keepalive request with the given `CSeq`.
        async fn send_keepalive_response(server: &mut crate::tokio::Connection, cseq: u32) {
            let mut response = response(BACKCHANNEL_TEARDOWN).0;
            response.headers.insert(
                msg::HeaderName::CSEQ,
                msg::HeaderValue::try_from(cseq.to_string()).unwrap(),
            );
            server
                .send(OwnedMessage::Response {
                    head: response,
                    body: Bytes::new(),
                })
                .await
                .unwrap();
        }

        /// With receiver reports enabled, a video stream gets receiver reports on
        /// its RTCP channel while the backchannel gets none: Retina sends rather
        /// than receives its media, and describes it in sender reports instead.
        #[tokio::test]
        async fn backchannel_with_receiver_reports() {
            init_logging();
            let (conn, mut server) = connect_to_mock().await;
            let (session, _) = tokio::join!(
                Session::describe_with_conn(
                    conn,
                    SessionOptions::default()
                        .backchannel(true)
                        .receiver_reports(ReceiverReportPolicy::Always),
                    Url::parse(BACKCHANNEL_URL).unwrap(),
                ),
                req_response(
                    &mut server,
                    msg::Method::DESCRIBE,
                    response(BACKCHANNEL_DESCRIBE)
                ),
            );
            let mut session = session.unwrap();
            let (r, _) = tokio::join!(
                session.setup(0, SetupOptions::default()),
                req_response(
                    &mut server,
                    msg::Method::SETUP,
                    response(BACKCHANNEL_SETUP_VIDEO)
                ),
            );
            r.unwrap();
            let (r, _) = tokio::join!(
                session.setup(2, SetupOptions::default()),
                req_response(
                    &mut server,
                    msg::Method::SETUP,
                    response(BACKCHANNEL_SETUP_BACK)
                ),
            );
            r.unwrap();
            let (session, _) = tokio::join!(
                session.play(PlayOptions::default()),
                req_response(&mut server, msg::Method::PLAY, response(BACKCHANNEL_PLAY)),
            );
            let session = session.unwrap();
            tokio::pin!(session);
            // Make a report due now. Only the video stream's goes out.
            let (ssrc, cname, _) = keepalive_off(&mut session);
            set_report_due(&mut session, tokio::time::Instant::now());
            let report = recv_data_while_polling(&mut session, &mut server, 1).await;
            receiver_report::tests::parse_report(&report, ssrc, 0, &cname);

            // Backchannel media follows on the backchannel's channel.
            let mut sender = crate::rtp::Sender::new(0, crate::rtp::SenderOptions::default());
            session
                .queue_rtp(2, &sender.packet(ts(0), true, &[&[0xff; 160]]))
                .unwrap();
            let (channel, rtp) = next_data_while_polling(&mut session, &mut server).await;
            assert_eq!(channel, 2);
            assert_eq!(rtp.len(), 12 + 160);
        }

        /// Backchannel media queued after a keepalive request can keep the write
        /// buffer from emptying past the keepalive interval. The keepalive counts
        /// as written once its own bytes are out, so the session waits for the
        /// response rather than timing out writing it. A keepalive that really
        /// can't be written still times out.
        #[tokio::test]
        async fn keepalive_written_while_media_queued() {
            init_logging();
            let (conn, mut server) = connect_to_mock().await;
            let mut session = play_backchannel(conn, &mut server).await;
            playing_core(&mut session).set_parameter_methods_supported();

            /// Queues 16 MiB of media on the backchannel: more than the socket
            /// buffers hold.
            fn queue_media(session: &mut Session<Playing>) {
                let mut sender = crate::rtp::Sender::new(0, crate::rtp::SenderOptions::default());
                let payload = vec![0xd5; 16_384];
                for _ in 0..1024 {
                    session
                        .queue_rtp(2, &sender.packet(ts(0), false, &[&payload]))
                        .unwrap();
                }
            }

            /// Makes a keepalive due on the next poll.
            fn fire_keepalive_timer(session: &mut Session<Playing>) {
                playing_core(session).set_keepalive_deadline(std::time::Instant::now());
                session.0.keepalive_timer =
                    Some(Box::pin(tokio::time::sleep(std::time::Duration::ZERO)));
            }

            /// Polls `session` until `done`, failing if it yields an item.
            async fn poll_until(
                session: &mut Session<Playing>,
                done: impl Fn(&playing::KeepaliveState) -> bool,
            ) {
                tokio::time::timeout(std::time::Duration::from_secs(10), async {
                    while !done(&playing_core(session).keepalive_state()) {
                        match futures::poll!(std::pin::pin!(session.next_item())) {
                            Poll::Pending => tokio::task::yield_now().await,
                            Poll::Ready(o) => panic!("unexpected item: {o:#?}"),
                        }
                    }
                })
                .await
                .unwrap();
            }

            // The keepalive is queued behind media and can't be written yet. More
            // media is queued behind it.
            queue_media(&mut session);
            fire_keepalive_timer(&mut session);
            poll_until(&mut session, |s| {
                matches!(s, playing::KeepaliveState::Flushing { .. })
            })
            .await;
            queue_media(&mut session);

            // The server reads up to the keepalive request, which is then written,
            // while media remains queued behind it.
            let (cseq, ()) = tokio::join!(
                async {
                    loop {
                        let msg = server.next().await.unwrap().unwrap();
                        if let msg::Message::Request(r) = msg.msg {
                            assert_eq!(r.method, msg::Method::GET_PARAMETER);
                            break r.headers.get("CSeq").unwrap().parse::<u32>().unwrap();
                        }
                    }
                },
                poll_until(&mut session, |s| matches!(
                    s,
                    playing::KeepaliveState::Waiting { .. }
                )),
            );
            assert!(!playing_core(&mut session).transmit_buf().0.is_empty());

            // The response arrives, and the next keepalive is sent without error.
            send_keepalive_response(&mut server, cseq).await;
            poll_until(&mut session, |s| matches!(s, playing::KeepaliveState::Idle)).await;
            fire_keepalive_timer(&mut session);
            poll_until(&mut session, |s| {
                matches!(s, playing::KeepaliveState::Flushing { .. })
            })
            .await;

            // The server isn't reading, so that keepalive is never written.
            fire_keepalive_timer(&mut session);
            let e = loop {
                match futures::poll!(std::pin::pin!(session.next_item())) {
                    Poll::Pending => tokio::task::yield_now().await,
                    Poll::Ready(Some(Err(e))) => break e,
                    Poll::Ready(o) => panic!("unexpected item: {o:#?}"),
                }
            };
            match &*e.0 {
                ErrorInt::WriteError { source, .. } => {
                    assert_eq!(source.kind(), std::io::ErrorKind::TimedOut);
                    assert!(
                        source.to_string().contains("Unable to write keepalive"),
                        "{e}"
                    );
                }
                _ => panic!("unexpected error: {e}"),
            }
        }
    }

    // See with: cargo test -- --nocapture client::tests::print_sizes
    #[test]
    fn print_sizes() {
        init_logging();
        for (name, size) in &[
            ("PlayingItem", std::mem::size_of::<PlayingItem>()),
            ("Presentation", std::mem::size_of::<Presentation>()),
            ("PlayingCore", std::mem::size_of::<PlayingCore>()),
            (
                "Session",
                std::mem::size_of::<Session<Described>>(), // <Playing> is the same size.
            ),
            ("SessionCore", std::mem::size_of::<SessionCore>()),
            ("SessionInner", std::mem::size_of::<SessionInner>()),
            ("SessionOptions", std::mem::size_of::<SessionOptions>()),
            ("Stream", std::mem::size_of::<Stream>()),
        ] {
            log::info!("{name:-40} {size:4}");
        }
    }

    #[test]
    fn check_live555_tcp_bug() {
        init_logging();
        assert!(!Tool::new("not live555").has_live555_tcp_bug());
        assert!(!Tool::new("LIVE555 Streaming Media v").has_live555_tcp_bug());
        assert!(Tool::new("LIVE555 Streaming Media v2013.04.08").has_live555_tcp_bug());
        assert!(!Tool::new("LIVE555 Streaming Media v2017.06.04").has_live555_tcp_bug());
        assert!(!Tool::new("LIVE555 Streaming Media v2020.01.01").has_live555_tcp_bug());
    }

    #[test]
    fn await_stale_sessions_is_send() {
        // There's probably a more elegant way to test this, but here goes.
        fn assert_send<T: Send>(_: T) {}
        let group = SessionGroup::default();
        let stale_sessions = group.stale_sessions(tokio_now());
        assert_send(group.await_stale_sessions(&stale_sessions));
    }
}
