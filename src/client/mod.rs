// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTSP client: connect to a server via [`Session`].

use std::convert::TryFrom;
use std::mem::MaybeUninit;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::num::NonZeroU32;
use std::sync::{Arc, Mutex};
use std::task::Poll;
use std::{fmt::Debug, num::NonZeroU16, pin::Pin};

use self::channel_mapping::*;
pub use self::timeline::Timeline;
use bytes::Bytes;
use futures::{ready, Future, SinkExt, StreamExt};
use log::{debug, trace, warn};
use pin_project::pin_project;
use rtsp_types::{Data, Method};
use tokio::net::UdpSocket;
use tokio::sync::Notify;
use url::Url;

use crate::client::parse::SessionHeader;
use crate::codec::CodecItem;
use crate::{Error, ErrorInt, RtspMessageContext};

mod channel_mapping;
mod parse;
pub mod rtp;
mod teardown;
mod timeline;

// TODO: this is pub but can't be fed back into the crate in any way; strange.
#[doc(hidden)]
/// Duration between keepalive RTSP requests during [Playing] state.
pub const KEEPALIVE_DURATION: std::time::Duration = std::time::Duration::from_secs(30);

/// Assumed expiration time for stale live555 TCP sessions (case #2 of "Stale
/// sessions" in [`SessionGroup`]).
///
/// This constant is taken from
/// [here](https://github.com/rgaufman/live555/blob/41a5ec5f65bd626918a43951f743b4c9ffc52289/liveMedia/include/RTSPServer.hh#L35).
const LIVE555_EXPIRATION_SEC: u64 = 65;

/// A stale RTP session. See explanation at [`SessionGroup`].
struct StaleSession {
    seqnum: u64,

    /// If this stale session was created from a dropped [`Session`],
    /// a watch showing the results of the latest `TEARDOWN` attempt, or `None`
    /// if one hasn't yet concluded.
    teardown_rx: Option<tokio::sync::watch::Receiver<Option<Result<(), Error>>>>,

    maybe_playing: bool,
    is_tcp: bool,

    /// Upper bound of advertised expiration time.
    expires: tokio::time::Instant,
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
/// 1.  Dropped [`Session`]s if the [`TeardownPolicy`] says to do so
///     and a valid `SETUP` response has been received.
///
///     A tokio background task is responsible for attempting a `TEARDOWN` and
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
/// ## Granularity
///
/// A `SessionGroup` can be of any granularity, but a typical use is to ensure
/// there are no stale sessions before starting a fresh session (see
/// [`SessionGroup::stale_sessions`] and [`SessionGroup::await_stale_sessions`]).
/// Groups should be sized to match that idea. If connecting to a live555 server
/// affected by the stale TCP session bug, it might be wise to have one group
/// per server, so that all such sessions can be drained before initiating new
/// connections. Otherwise it might be useful to have one group per describe
/// URL (potentially several per server) and have at most one active session per
/// URL.
#[derive(Default)]
pub struct SessionGroup {
    name: Option<String>,
    sessions: Mutex<SessionGroupInner>,
    notify: Notify,
}

#[derive(Default)]
struct SessionGroupInner {
    next_seqnum: u64,

    /// Stale sessions, unordered.
    sessions: Vec<StaleSession>,
}

/// The overall status of stale sessions that may be in state `Playing` and
/// belong to a particular group.
pub struct StaleSessionStatus {
    /// The maximum expire time of any such sessions.
    pub max_expires: Option<tokio::time::Instant>,

    /// The total number of sessions.
    pub num_sessions: usize,

    /// The `SessionGroupInner::next_seqnum` value as of when this was created.
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
    fn debug_id(&self) -> impl Debug {
        self.name.clone().unwrap_or_else(|| format!("{:p}", &self))
    }

    /// Returns the status of stale sessions in this group.
    ///
    /// Currently this only returns information about sessions which may be in
    /// state `Playing`. That is, ones for which Retina has either sent a
    /// `PLAY` request (regardless of whether it received a response) or
    /// discovered as described in [`SessionGroup`].
    ///
    /// The caller might use this in a loop with `await_stale_sessions` to sleep
    /// until there are no such sessions, logging updates
    pub fn stale_sessions(&self) -> StaleSessionStatus {
        let l = self.sessions.lock().unwrap();
        let playing = l.sessions.iter().filter(|s| s.maybe_playing);
        StaleSessionStatus {
            max_expires: playing.clone().map(|s| s.expires).max(),
            num_sessions: playing.count(),
            next_seqnum: l.next_seqnum,
        }
    }

    /// Waits for a reasonable attempt at `TEARDOWN` on all stale sessions that
    /// exist as of when this method is called, returning an error if any
    /// session's reasonable attempts fail.
    ///
    /// This has no timeout other than the sessions' expiration times. The
    /// caller can wrap the call in `tokio::time::timeout` for an earlier time.
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
    /// ## Panics
    ///
    /// If the `TEARDOWN` was initiated from a tokio runtime which has since
    /// shut down.
    pub async fn await_teardown(&self) -> Result<(), Error> {
        let mut watches: Vec<_>;
        {
            let l = self.sessions.lock().unwrap();
            watches = l
                .sessions
                .iter()
                .filter_map(|s| s.teardown_rx.clone())
                .collect();
        }

        let mut overall_result = Ok(());
        for w in &mut watches {
            let mut r = (*w.borrow_and_update()).clone();

            if r.is_none() {
                // An attempt hasn't finished yet. Wait for it.
                w.changed().await.expect(
                    "teardown Sender shouldn't be dropped; \
                             ensure the Session's tokio runtime is still alive",
                );
                r = (*w.borrow()).clone();
            }

            // Now an attempt has finished, success or failure.
            let r = r.expect("teardown result should be populated after change");
            overall_result = overall_result.and(r);
        }
        overall_result
    }

    /// Waits for all of the sessions described by `status` to expire or be torn down.
    pub async fn await_stale_sessions(&self, status: &StaleSessionStatus) {
        loop {
            let notified = self.notify.notified();
            {
                let l = self.sessions.lock().unwrap();
                let left = l
                    .sessions
                    .iter()
                    .filter(|s| s.maybe_playing && s.seqnum < status.next_seqnum)
                    .count();
                log::trace!(
                    "Session group {:?} has {} relevant sessions numbered < {}",
                    self.debug_id(),
                    left,
                    status.next_seqnum
                );
                if left == 0 {
                    return;
                }
            }
            notified.await;
        }
    }

    /// Removes the session with `seqnum` removing true iff it existed. Notifies waiters.
    fn try_remove_seqnum(&self, seqnum: u64) -> bool {
        let mut l = self.sessions.lock().unwrap();
        let i = l.sessions.iter().position(|s| s.seqnum == seqnum);
        match i {
            Some(i) => {
                l.sessions.swap_remove(i);
                drop(l);
                self.notify.notify_waiters();
                true
            }
            None => false,
        }
    }
}

/// Policy for when to send `TEARDOWN` requests.
///
/// Specify via [`SessionOptions::teardown`].
#[derive(Copy, Clone, Debug)]
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
    Auto,

    /// Always send `TEARDOWN` requests, regardless of transport.
    ///
    /// This tries repeatedly to tear down the session until success or expiration;
    /// [`SessionGroup`] will track it also.
    Always,

    /// Never send `TEARDOWN` or track stale sessions.
    Never,
}

impl Default for TeardownPolicy {
    fn default() -> Self {
        TeardownPolicy::Auto
    }
}

impl std::fmt::Display for TeardownPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.pad(match self {
            TeardownPolicy::Auto => "auto",
            TeardownPolicy::Never => "never",
            TeardownPolicy::Always => "always",
        })
    }
}

impl std::str::FromStr for TeardownPolicy {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "auto" => TeardownPolicy::Auto,
            "never" => TeardownPolicy::Never,
            "always" => TeardownPolicy::Always,
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "bad TeardownPolicy {}; expected auto, never, or always",
                s
            ))),
        })
    }
}

/// Policy for handling the `rtptime` parameter normally seem in the `RTP-Info` header.
/// This parameter is used to map each stream's RTP timestamp to NPT ("normal play time"),
/// allowing multiple streams to be played in sync.
#[derive(Copy, Clone, Debug)]
pub enum InitialTimestampPolicy {
    /// Default policy: currently `Require` when playing multiple streams,
    /// `Ignore` otherwise.
    Default,

    /// Require the `rtptime` parameter be present and use it to set NPT. Use
    /// when accurate multi-stream NPT is important.
    Require,

    /// Ignore the `rtptime` parameter and assume the first received packet for
    /// each stream is at NPT 0. Use with cameras that are known to set
    /// `rtptime` incorrectly.
    Ignore,

    /// Use the `rtptime` parameter when playing multiple streams if it's
    /// specified for all of them; otherwise assume the first received packet
    /// for each stream is at NPT 0.
    Permissive,
}

impl Default for InitialTimestampPolicy {
    fn default() -> Self {
        InitialTimestampPolicy::Default
    }
}

impl std::fmt::Display for InitialTimestampPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.pad(match self {
            InitialTimestampPolicy::Default => "default",
            InitialTimestampPolicy::Require => "require",
            InitialTimestampPolicy::Ignore => "ignore",
            InitialTimestampPolicy::Permissive => "permissive",
        })
    }
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
                "bad InitialTimestampPolicy {}; \
                 expected default, require, ignore or permissive",
                s
            ))),
        })
    }
}

/// Options which must be known right as a session is created.
///
/// Decisions which can be deferred are in [PlayOptions] instead.
#[derive(Default)]
pub struct SessionOptions {
    creds: Option<Credentials>,
    user_agent: Option<Box<str>>,
    transport: Transport,
    session_group: Option<Arc<SessionGroup>>,
    teardown: TeardownPolicy,
    unassigned_channel_data: UnassignedChannelDataPolicy,
}

/// Policy for handling data received on unassigned RTSP interleaved channels.
#[derive(Copy, Clone)]
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
    Auto,

    /// Assume the data is due to the live555 stale TCP session bug described
    /// in "Stale sessions" under [`SessionGroup`].
    ///
    /// This session will return error, and the `SessionGroup` will track the
    /// expiration of a stale session.
    AssumeStaleSession,

    /// Returns an error.
    Error,

    /// Ignores the data.
    ///
    /// Some broken IP cameras appear to have some default assignment of streams
    /// to interleaved channels. If there is no `SETUP` for that stream before
    /// `PLAY`, they will send data anyway, on this channel. In this mode, such
    /// data messages are ignored.
    Ignore,
}

impl Default for UnassignedChannelDataPolicy {
    fn default() -> Self {
        Self::Auto
    }
}

impl std::fmt::Display for UnassignedChannelDataPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.pad(match self {
            UnassignedChannelDataPolicy::Auto => "auto",
            UnassignedChannelDataPolicy::AssumeStaleSession => "assume-stale-session",
            UnassignedChannelDataPolicy::Error => "error",
            UnassignedChannelDataPolicy::Ignore => "ignore",
        })
    }
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
                "bad UnassignedChannelDataPolicy {}; expected auto, assume-stale-session, error, \
                 or ignore",
                s
            ))),
        })
    }
}

/// The RTP packet transport to request.
///
/// Defaults to `Transport::Tcp`.
#[derive(Copy, Clone, Debug)]
pub enum Transport {
    /// Sends RTP packets over the RTSP TCP connection via interleaved data.
    Tcp,

    /// Sends RTP packets over UDP (experimental).
    ///
    /// This support is currently only suitable for a LAN for a couple reasons:
    /// *   There's no reorder buffer, so out-of-order packets are all dropped.
    /// *   There's no support for sending RTCP RRs (receiver reports), so
    ///     servers won't have the correct information to measure packet loss
    ///     and pace packets appropriately.
    Udp,
}

impl Default for Transport {
    fn default() -> Self {
        Transport::Tcp
    }
}

impl std::fmt::Display for Transport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.pad(match self {
            Transport::Tcp => "tcp",
            Transport::Udp => "udp",
        })
    }
}

impl std::str::FromStr for Transport {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "tcp" => Transport::Tcp,
            "udp" => Transport::Udp,
            _ => bail!(ErrorInt::InvalidArgument(format!(
                "bad Transport {}; \
                 expected tcp or udp",
                s
            ))),
        })
    }
}

impl SessionOptions {
    /// Uses the given credentials when/if the server requests digest authentication.
    pub fn creds(mut self, creds: Option<Credentials>) -> Self {
        self.creds = creds;
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

    /// Sets the underlying transport to use.
    pub fn transport(mut self, transport: Transport) -> Self {
        self.transport = transport;
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
}

/// Options which must be decided at `PLAY` time.
///
/// These are mostly adjustments for non-compliant server implementations.
/// See also [`SessionOptions`] for options which must be decided earlier.
#[derive(Default)]
pub struct PlayOptions {
    initial_timestamp: InitialTimestampPolicy,
    ignore_zero_seq: bool,
    enforce_timestamps_with_max_jump_secs: Option<NonZeroU32>,
}

impl PlayOptions {
    /// Sets the policy for handling the `rtptime` parameter normally seem in the `RTP-Info` header.
    pub fn initial_timestamp(self, initial_timestamp: InitialTimestampPolicy) -> Self {
        Self {
            initial_timestamp,
            ..self
        }
    }

    /// If the `RTP-Time` specifies `seq=0`, ignore it.
    ///
    /// Some cameras set this value then start the stream with something
    /// dramatically different. (Eg the Hikvision DS-2CD2032-I on its metadata
    /// stream; the other streams are fine.)
    pub fn ignore_zero_seq(self, ignore_zero_seq: bool) -> Self {
        Self {
            ignore_zero_seq,
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

// TODO: this is `pub` yet not actually accessible from outside the crate, a combination which
// makes little sense.
#[doc(hidden)]
#[derive(Debug)]
pub struct Presentation {
    pub streams: Vec<Stream>,
    base_url: Url,
    pub control: Url,
    pub accept_dynamic_rate: bool,
    tool: Option<Tool>,
}

/// The server's version as declared in the `DESCRIBE` response's `a:tool` SDP attribute.
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
        &*self.0
    }
}

/// Information about a stream offered within a presentation.
///
/// Currently if multiple formats are offered, this only describes the first.
pub struct Stream {
    /// Media type, as specified in the [IANA SDP parameters media
    /// registry](https://www.iana.org/assignments/sdp-parameters/sdp-parameters.xhtml#sdp-parameters-1).
    pub media: String,

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
    pub encoding_name: String,

    /// RTP payload type.
    ///
    /// See the [registry](https://www.iana.org/assignments/rtp-parameters/rtp-parameters.xhtml#rtp-parameters-1).
    /// It's common to use one of the dynamically assigned values, 96–127.
    pub rtp_payload_type: u8,

    /// RTP clock rate, in Hz.
    pub clock_rate: u32,

    /// Number of audio channels, if applicable (`media` is `audio`) and known.
    pub channels: Option<NonZeroU16>,

    /// Video framerate if present in SDP attributes
    pub framerate: Option<f32>,

    depacketizer: Result<crate::codec::Depacketizer, String>,

    /// The specified control URL.
    ///
    /// This is needed with multiple streams to send `SETUP` requests and
    /// interpret the `PLAY` response's `RTP-Info` header.
    /// [RFC 2326 section C.3](https://datatracker.ietf.org/doc/html/rfc2326#appendix-C.3)
    /// says the server is allowed to omit it when there is only a single stream.
    pub control: Option<Url>,

    /// The sockets for `Transport::Udp`.
    sockets: Option<UdpSockets>,

    state: StreamState,
}

impl std::fmt::Debug for Stream {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("Stream")
            .field("media", &self.media)
            .field("control", &self.control.as_ref().map(Url::as_str))
            .field("encoding_name", &self.encoding_name)
            .field("rtp_payload_type", &self.rtp_payload_type)
            .field("clock_rate", &self.clock_rate)
            .field("channels", &self.channels)
            .field("framerate", &self.framerate)
            .field("depacketizer", &self.depacketizer)
            .field("UDP", &self.sockets)
            .field("state", &self.state)
            .finish()
    }
}

struct UdpSockets {
    local_ip: IpAddr,
    local_rtp_port: u16,
    remote_ip: IpAddr,
    remote_rtp_port: u16,
    rtp_socket: UdpSocket,
    remote_rtcp_port: u16,
    rtcp_socket: UdpSocket,
}

impl std::fmt::Debug for UdpSockets {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("UDP")
            .field("local_ip", &self.local_ip)
            .field("local_rtp_port", &self.local_rtp_port)
            .field("remote_ip", &self.remote_ip)
            .field("remote_rtp_port", &self.remote_rtp_port)
            .field("rtp_socket", &self.rtp_socket)
            .field("remote_rtcp_port", &self.remote_rtcp_port)
            .field("rtcp_socket", &self.rtcp_socket)
            .finish()
    }
}

impl Stream {
    /// Returns codec-specified parameters for this stream, if available.
    ///
    /// Returns `None` on unknown codecs, bad parameters, or if parameters aren't (yet) known.
    ///
    /// This is initially populated from the `DESCRIBE` response's SDP. Not all codecs guarantee
    /// parameters are provided in the SDP. Notably, H.264 allows parameters to be specified
    /// "in-band" (with the data packets) instead of or in addition to "out-of-band" (via SDP).
    /// Thus, it's unspecified whether a `parameters` call immediately after `Session::describe`
    /// will return `Some` or `None`.
    ///
    /// # With [`Demuxed`]
    ///
    /// When using [`Demuxed`]'s frame-by-frame `futures::Stream` impl:
    ///
    /// *   After `poll_next` returns `Ready`, `parameters` reflects all parameter changes as of
    ///     returned frame.
    /// *   After `poll_next` returns `Pending`, currently the parameters may or may not reflect
    ///     changes sent as part of the *next* frame that `poll_next` will return. (It's likely
    ///     that an upcoming Retina release will guarantee not.)
    ///
    /// If there is no packet loss, parameters are generally available after the first frame is
    /// returned. In the case of H.264, [RFC 6184 section
    /// 8.4](https://datatracker.ietf.org/doc/html/rfc6184#section-8.4) says "when parameter sets
    /// are added or updated, care SHOULD be taken to ensure that any parameter set is delivered
    /// prior to its usage."
    ///
    /// # Without [`Demuxed`]
    ///
    /// When directly using [`Session`]'s packet-by-packet `futures::Stream` impl, codec
    /// depacketization logic is bypassed. The parameters returned by this function may be out of
    /// date.
    pub fn parameters(&self) -> Option<crate::codec::Parameters> {
        self.depacketizer.as_ref().ok().and_then(|d| d.parameters())
    }
}

#[derive(Debug)]
enum StreamState {
    /// Uninitialized; no `SETUP` has yet been sent.
    Uninit,

    /// `SETUP` response has been received.
    Init(StreamStateInit),

    /// `PLAY` response has been received.
    Playing {
        timeline: Timeline,
        rtp_handler: rtp::InorderParser,
    },
}

#[derive(Copy, Clone, Debug, Default)]
struct StreamStateInit {
    /// The RTP synchronization source (SSRC), as defined in
    /// [RFC 3550](https://tools.ietf.org/html/rfc3550). This is normally
    /// supplied in the `SETUP` response's `Transport` header. Reolink cameras
    /// instead supply it in the `PLAY` response's `RTP-Info` header.
    ssrc: Option<u32>,

    /// The initial RTP sequence number, as specified in the `PLAY` response's
    /// `RTP-Info` header. This field is only used during the `play()` call
    /// itself; by the time it returns, the stream will be in state `Playing`.
    initial_seq: Option<u16>,

    /// The initial RTP timestamp, as specified in the `PLAY` response's
    /// `RTP-Info` header. This field is only used during the `play()` call
    /// itself; by the time it returns, the stream will be in state `Playing`.
    initial_rtptime: Option<u32>,
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
pub struct Described {
    sdp: Bytes,
}
impl State for Described {}

enum KeepaliveState {
    Idle,
    Flushing(u32),
    Waiting(u32),
}

/// State after a `PLAY`; use via `Session<Playing>`.
#[doc(hidden)]
pub struct Playing(());
impl State for Playing {}

/// The raw connection, without tracking session state.
struct RtspConnection {
    inner: crate::tokio::Connection,
    channels: ChannelMappings,

    /// The next `CSeq` header value to use when sending an RTSP request.
    next_cseq: u32,

    /// If Retina has received data on an unassigned RTSP interleaved data channel.
    seen_unassigned: bool,
}

/// Mode to use in `RtspConnection::send` when looking for a response.
enum ResponseMode {
    /// Anything but the response to this request is an error.
    Normal,

    /// Silently discard data messages on assigned channels.
    ///
    /// This is a workaround for recent Reolink cameras which appear to send
    /// RTCP sender reports immediately *before* the `PLAY` response when
    /// using interleaved data. It's simplest to discard them rather than
    /// attempt to interpret them before having `RTP-Info`.
    Play,

    /// Discard data messages and unrelated responses while awaiting the
    /// response to this request.
    Teardown,
}

/// An RTSP session.
///
/// The expected lifecycle is as follows:
///
/// 1. Create a session via [`Session::describe`].
/// 2. Examine the session's available streams via [`Session::streams`] and set
///    up one or more via [`Session::setup`].
/// 3. Start playing via [`Session::play`].
/// 4. Get packets via the [`futures::stream::Stream`] impl on `Session<Playing>`,
///    or frames via the [`futures::stream::Stream`] impl returned by [`Session<Playing>::demuxed`].
/// 5. Drop the session. Retina may issue a `TEARDOWN` in the background, depending on the
///    [`SessionOptions::teardown`] parameter.
/// 6. Possibly wait for `TEARDOWN` to complete; see
///    [`SessionOptions::session_group`] and [`SessionGroup::await_teardown`].
///
/// ## tokio runtime
///
/// All `Session` operations are currently expected to be performed from
/// "within" a tokio runtime with both time and I/O resource drivers enabled.
/// Operations may panic or fail otherwise.
pub struct Session<S: State>(Pin<Box<SessionInner>>, S);

#[pin_project(PinnedDrop)]
struct SessionInner {
    /// The connection. Currently there's expected to always be a RTSP
    /// connection, even while playing a RTP/AVP/UDP session. The only
    /// exception is during drop.
    conn: Option<RtspConnection>,

    options: SessionOptions,
    requested_auth: Option<http_auth::PasswordClient>,
    presentation: Presentation,

    /// This will be set iff one or more `SETUP` calls have been issued.
    /// This is sometimes true in state `Described` and always true in state
    /// `Playing`.
    session: Option<parse::SessionHeader>,

    // Keep some information about the DESCRIBE response. If a depacketizer
    // couldn't be constructed correctly for one or more streams, this will be
    // used to create a RtspResponseError on `State<Playing>::demuxed()`.
    // We defer such errors from DESCRIBE time until then because they only
    // matter if the stream is setup and the caller wants depacketization.
    describe_ctx: RtspMessageContext,
    describe_cseq: u32,
    describe_status: rtsp_types::StatusCode,

    /// The state of the keepalive request; only used in state `Playing`.
    keepalive_state: KeepaliveState,

    keepalive_timer: Option<Pin<Box<tokio::time::Sleep>>>,

    /// Set if the server may be in state Playing: we have sent a `PLAY`
    /// request, regardless of if the response has been received.
    maybe_playing: bool,

    /// The index within `presentation.streams` to start the next poll at.
    /// Round-robining between them rather than always starting at 0 should
    /// prevent one stream from starving the others.
    udp_next_poll_i: usize,
}

impl RtspConnection {
    async fn connect(url: &Url) -> Result<Self, Error> {
        let host =
            RtspConnection::validate_url(url).map_err(|e| wrap!(ErrorInt::InvalidArgument(e)))?;
        let port = url.port().unwrap_or(554);
        let inner = crate::tokio::Connection::connect(host, port)
            .await
            .map_err(|e| wrap!(ErrorInt::ConnectError(e)))?;
        Ok(Self {
            inner,
            channels: ChannelMappings::default(),
            next_cseq: 1,
            seen_unassigned: false,
        })
    }

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
            .ok_or_else(|| format!("Must specify host in rtsp url {}", &url))
    }

    /// Sends a request and expects an upcoming message from the peer to be its response.
    /// Takes care of authorization and `CSeq`. Returns `Error` if not successful.
    async fn send(
        &mut self,
        mode: ResponseMode,
        options: &SessionOptions,
        tool: Option<&Tool>,
        requested_auth: &mut Option<http_auth::PasswordClient>,
        req: &mut rtsp_types::Request<Bytes>,
    ) -> Result<(RtspMessageContext, u32, rtsp_types::Response<Bytes>), Error> {
        loop {
            let cseq = self.fill_req(options, requested_auth, req)?;
            self.inner
                .send(rtsp_types::Message::Request(req.clone()))
                .await
                .map_err(|e| wrap!(e))?;
            let method: &str = req.method().into();
            let (resp, msg_ctx) = loop {
                let msg = self.inner.next().await.unwrap_or_else(|| {
                    bail!(ErrorInt::RtspReadError {
                        conn_ctx: *self.inner.ctx(),
                        msg_ctx: self.inner.eof_ctx(),
                        source: std::io::Error::new(
                            std::io::ErrorKind::UnexpectedEof,
                            format!("EOF while expecting response to {} CSeq {}", method, cseq),
                        ),
                    })
                })?;
                let msg_ctx = msg.ctx;
                let description = match msg.msg {
                    rtsp_types::Message::Response(r) => {
                        if let Some(response_cseq) = parse::get_cseq(&r) {
                            if response_cseq == cseq {
                                break (r, msg_ctx);
                            }
                            if matches!(mode, ResponseMode::Teardown) {
                                debug!("ignoring unrelated response during TEARDOWN");
                                continue;
                            }
                            format!("{} response with CSeq {}", r.reason_phrase(), response_cseq)
                        } else {
                            format!("{} response with no/unparseable cseq", r.reason_phrase())
                        }
                    }
                    rtsp_types::Message::Data(d) => {
                        if matches!(mode, ResponseMode::Teardown { .. }) {
                            debug!("ignoring RTSP interleaved data during TEARDOWN");
                            continue;
                        } else if let (ResponseMode::Play, Some(m)) =
                            (&mode, self.channels.lookup(d.channel_id()))
                        {
                            debug!(
                                "ignoring interleaved data message on {:?} channel {} while \
                                     waiting for response to {} CSeq {}",
                                m.channel_type,
                                d.channel_id(),
                                method,
                                cseq
                            );
                            continue;
                        }
                        self.handle_unassigned_data(msg_ctx, options, tool, d)?;
                        continue;
                    }
                    rtsp_types::Message::Request(r) => format!("{:?} request", r.method()),
                };
                bail!(ErrorInt::RtspFramingError {
                    conn_ctx: *self.inner.ctx(),
                    msg_ctx,
                    description: format!(
                        "Expected response to {} CSeq {}, got {}",
                        method, cseq, description,
                    ),
                });
            };
            if resp.status() == rtsp_types::StatusCode::Unauthorized {
                if requested_auth.is_some() {
                    // TODO: the WWW-Authenticate might indicate a new domain or nonce.
                    // In that case, we should retry rather than returning error.
                    bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *self.inner.ctx(),
                        msg_ctx,
                        method: req.method().clone(),
                        cseq,
                        status: resp.status(),
                        description: "Received Unauthorized after trying digest auth".into(),
                    })
                }
                let www_authenticate = match resp.header(&rtsp_types::headers::WWW_AUTHENTICATE) {
                    None => bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *self.inner.ctx(),
                        msg_ctx,
                        method: req.method().clone(),
                        cseq,
                        status: resp.status(),
                        description: "Unauthorized without WWW-Authenticate header".into(),
                    }),
                    Some(h) => h,
                };
                if options.creds.is_none() {
                    bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *self.inner.ctx(),
                        msg_ctx,
                        method: req.method().clone(),
                        cseq,
                        status: resp.status(),
                        description: "Authentication requested and no credentials supplied"
                            .to_owned(),
                    })
                }
                let www_authenticate = www_authenticate.as_str();
                *requested_auth = match http_auth::PasswordClient::try_from(www_authenticate) {
                    Ok(c) => Some(c),
                    Err(e) => bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *self.inner.ctx(),
                        msg_ctx,
                        method: req.method().clone(),
                        cseq,
                        status: resp.status(),
                        description: format!("Can't understand WWW-Authenticate header: {}", e),
                    }),
                };
                continue;
            } else if !resp.status().is_success() {
                bail!(ErrorInt::RtspResponseError {
                    conn_ctx: *self.inner.ctx(),
                    msg_ctx,
                    method: req.method().clone(),
                    cseq,
                    status: resp.status(),
                    description: "Unexpected RTSP response status".into(),
                });
            }
            return Ok((msg_ctx, cseq, resp));
        }
    }

    /// Handles data on an unassigned RTSP channel.
    fn handle_unassigned_data(
        &mut self,
        msg_ctx: RtspMessageContext,
        options: &SessionOptions,
        tool: Option<&Tool>,
        data: Data<Bytes>,
    ) -> Result<(), Error> {
        let live555 = match options.unassigned_channel_data {
            UnassignedChannelDataPolicy::Auto
                if tool.map(Tool::has_live555_tcp_bug).unwrap_or(false) =>
            {
                true
            }
            UnassignedChannelDataPolicy::AssumeStaleSession => true,
            UnassignedChannelDataPolicy::Error => false,
            UnassignedChannelDataPolicy::Ignore | UnassignedChannelDataPolicy::Auto => {
                if !self.seen_unassigned {
                    log::warn!(
                        "Ignoring data on unassigned RTSP interleaved data channel {}. \
                         This is the first such message. Following messages will be logged \
                         at trace priority only.\n\n\
                         conn: {}\nmsg: {}\ndata: {:#?}",
                        data.channel_id(),
                        self.inner.ctx(),
                        &msg_ctx,
                        crate::hex::LimitedHex::new(data.as_slice(), 128),
                    );
                    self.seen_unassigned = true;
                } else {
                    log::trace!(
                        "Ignoring data on unassigned RTSP interleaved data channel {}.\n\n\
                         conn: {}\nmsg: {}\ndata: {:#?}",
                        data.channel_id(),
                        self.inner.ctx(),
                        &msg_ctx,
                        crate::hex::LimitedHex::new(data.as_slice(), 128),
                    );
                }
                return Ok(());
            }
        };

        if live555 {
            note_stale_live555_data(tool, options);
        }

        let channel_id = data.channel_id();
        let data = data.into_body();
        bail!(ErrorInt::RtspUnassignedChannelError {
            conn_ctx: *self.inner.ctx(),
            msg_ctx,
            channel_id,
            data,
        });
    }

    /// Fills out `req` with authorization and `CSeq` headers.
    fn fill_req(
        &mut self,
        options: &SessionOptions,
        requested_auth: &mut Option<http_auth::PasswordClient>,
        req: &mut rtsp_types::Request<Bytes>,
    ) -> Result<u32, Error> {
        let cseq = self.next_cseq;
        self.next_cseq += 1;
        if let Some(ref mut auth) = requested_auth {
            let creds = options
                .creds
                .as_ref()
                .expect("creds were checked when filling request_auth");
            let authorization = auth
                .respond(&http_auth::PasswordParams {
                    username: &creds.username,
                    password: &creds.password,
                    uri: req.request_uri().map(|u| u.as_str()).unwrap_or("*"),
                    method: req.method().into(),
                    body: Some(&[]),
                })
                .map_err(|e| wrap!(ErrorInt::Internal(e.into())))?;
            req.insert_header(rtsp_types::headers::AUTHORIZATION, authorization);
        }
        req.insert_header(rtsp_types::headers::CSEQ, cseq.to_string());
        if let Some(ref u) = options.user_agent {
            req.insert_header(rtsp_types::headers::USER_AGENT, u.to_string());
        }
        Ok(cseq)
    }
}

impl<S: State> Session<S> {
    /// Returns the available streams as described by the server.
    pub fn streams(&self) -> &[Stream] {
        &self.0.presentation.streams
    }

    /// Returns the server's version as declared in the `DESCRIBE` response's `a:tool` SDP
    /// attribute.
    pub fn tool(&self) -> Option<&Tool> {
        self.0.presentation.tool.as_ref()
    }
}

impl Session<Described> {
    /// Creates a new session from a `DESCRIBE` request on the given URL.
    ///
    /// This method is permissive; it will return success even if there are
    /// errors in the SDP that would prevent one or more streams from being
    /// depacketized correctly. If those streams are setup via
    /// `Session<Described>::setup`, the erorrs in question will be ultimately
    /// returned from `Stream<Playing>::demuxed`.
    ///
    /// Expects to be called from a tokio runtime.
    pub async fn describe(url: Url, options: SessionOptions) -> Result<Self, Error> {
        let conn = RtspConnection::connect(&url).await?;
        Self::describe_with_conn(conn, options, url).await
    }

    async fn describe_with_conn(
        mut conn: RtspConnection,
        options: SessionOptions,
        url: Url,
    ) -> Result<Self, Error> {
        let mut req = rtsp_types::Request::builder(Method::Describe, rtsp_types::Version::V1_0)
            .header(rtsp_types::headers::ACCEPT, "application/sdp")
            .request_uri(url.clone())
            .build(Bytes::new());
        let mut requested_auth = None;
        let (msg_ctx, cseq, response) = conn
            .send(
                ResponseMode::Normal,
                &options,
                None, // tool isn't known until after the DESCRIBE response is parsed below.
                &mut requested_auth,
                &mut req,
            )
            .await?;
        let presentation = parse::parse_describe(url, &response).map_err(|description| {
            wrap!(ErrorInt::RtspResponseError {
                conn_ctx: *conn.inner.ctx(),
                msg_ctx,
                method: rtsp_types::Method::Describe,
                cseq,
                status: response.status(),
                description,
            })
        })?;
        let describe_status = response.status();
        let sdp = response.into_body();
        Ok(Session(
            Box::pin(SessionInner {
                conn: Some(conn),
                options,
                requested_auth,
                presentation,
                session: None,
                describe_ctx: msg_ctx,
                describe_cseq: cseq,
                describe_status,
                keepalive_state: KeepaliveState::Idle,
                keepalive_timer: None,
                maybe_playing: false,
                udp_next_poll_i: 0,
            }),
            Described { sdp },
        ))
    }

    /// Returns the raw SDP (Session Description Protocol) session description of this URL.
    ///
    /// Retina interprets the SDP automatically, but the raw bytes may be useful for debugging.
    /// They're accessibled in the `Session<Described>` state. Currently, they're discarded on
    /// `play` to reduce memory usage.
    pub fn sdp(&self) -> &[u8] {
        &self.1.sdp
    }

    /// Sends a `SETUP` request for a stream.
    ///
    /// Note these can't reasonably be pipelined because subsequent requests
    /// are expected to adopt the previous response's `Session`. Likewise,
    /// the server may override the preferred interleaved channel id and it
    /// seems like a bad idea to try to assign more interleaved channels without
    /// inspect that first.
    ///
    /// Panics if `stream_i >= self.streams().len()`.
    pub async fn setup(&mut self, stream_i: usize) -> Result<(), Error> {
        let inner = &mut self.0.as_mut().project();
        let presentation = &mut inner.presentation;
        let options = &inner.options;
        let conn = inner
            .conn
            .as_mut()
            .ok_or_else(|| wrap!(ErrorInt::FailedPrecondition("no connection".into())))?;
        let stream = &mut presentation.streams[stream_i];
        if !matches!(stream.state, StreamState::Uninit) {
            bail!(ErrorInt::FailedPrecondition("stream already set up".into()));
        }
        let url = stream
            .control
            .as_ref()
            .unwrap_or(&presentation.control)
            .clone();
        let mut req = rtsp_types::Request::builder(Method::Setup, rtsp_types::Version::V1_0)
            .request_uri(url)
            .header(crate::X_DYNAMIC_RATE.clone(), "1".to_owned());
        match options.transport {
            Transport::Tcp => {
                let proposed_channel_id = conn.channels.next_unassigned().ok_or_else(|| {
                    wrap!(ErrorInt::FailedPrecondition(
                        "no unassigned channels".into()
                    ))
                })?;
                req = req.header(
                    rtsp_types::headers::TRANSPORT,
                    format!(
                        "RTP/AVP/TCP;unicast;interleaved={}-{}",
                        proposed_channel_id,
                        proposed_channel_id + 1
                    ),
                );
            }
            Transport::Udp => {
                // Bind an ephemeral UDP port on the same local address used to connect
                // to the RTSP server.
                let ip_addr = conn.inner.ctx().local_addr.ip();
                let pair = crate::tokio::UdpPair::for_ip(ip_addr)
                    .map_err(|e| wrap!(ErrorInt::Internal(e.into())))?;
                stream.sockets = Some(UdpSockets {
                    local_ip: ip_addr,
                    local_rtp_port: pair.rtp_port,
                    remote_ip: IpAddr::V4(Ipv4Addr::UNSPECIFIED),
                    remote_rtp_port: 0,
                    rtp_socket: pair.rtp_socket,
                    remote_rtcp_port: 0,
                    rtcp_socket: pair.rtcp_socket,
                });
                req = req.header(
                    rtsp_types::headers::TRANSPORT,
                    format!(
                        "RTP/AVP/UDP;unicast;client_port={}-{}",
                        pair.rtp_port,
                        pair.rtp_port + 1,
                    ),
                );
            }
        }
        if let Some(ref s) = inner.session {
            req = req.header(rtsp_types::headers::SESSION, s.id.to_string());
        }
        let (msg_ctx, cseq, response) = conn
            .send(
                ResponseMode::Normal,
                inner.options,
                presentation.tool.as_ref(),
                inner.requested_auth,
                &mut req.build(Bytes::new()),
            )
            .await?;
        debug!("SETUP response: {:#?}", &response);
        let conn_ctx = conn.inner.ctx();
        let status = response.status();
        let response = parse::parse_setup(&response).map_err(|description| {
            wrap!(ErrorInt::RtspResponseError {
                conn_ctx: *conn_ctx,
                msg_ctx,
                method: rtsp_types::Method::Setup,
                cseq,
                status,
                description,
            })
        })?;
        match inner.session.as_ref() {
            Some(SessionHeader { id, .. }) if id.as_ref() != &*response.session.id => {
                bail!(ErrorInt::RtspResponseError {
                    conn_ctx: *conn.inner.ctx(),
                    msg_ctx,
                    method: rtsp_types::Method::Setup,
                    cseq,
                    status,
                    description: format!(
                        "session id changed from {:?} to {:?}",
                        id, response.session.id,
                    ),
                });
            }
            Some(_) => {}
            None => *inner.session = Some(response.session),
        };
        let conn_ctx = conn.inner.ctx();
        match options.transport {
            Transport::Tcp => {
                let channel_id = match response.channel_id {
                    Some(id) => id,
                    None => bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *conn.inner.ctx(),
                        msg_ctx,
                        method: rtsp_types::Method::Setup,
                        cseq,
                        status,
                        description: "Transport header is missing interleaved parameter".to_owned(),
                    }),
                };
                conn.channels
                    .assign(channel_id, stream_i)
                    .map_err(|description| {
                        wrap!(ErrorInt::RtspResponseError {
                            conn_ctx: *conn_ctx,
                            msg_ctx,
                            method: rtsp_types::Method::Setup,
                            cseq,
                            status,
                            description,
                        })
                    })?;
            }
            Transport::Udp => {
                // TODO: RFC 2326 section 12.39 says "If the source address for
                // the stream is different than can be derived from the RTSP
                // endpoint address (the server in playback or the client in
                // recording), the source MAY be specified." Not MUST,
                // unfortunately. But let's see if we can get away with this
                // for now.
                let source = match response.source {
                    Some(s) => s,
                    None => conn.inner.ctx().peer_addr.ip(),
                };
                let server_port = response.server_port.ok_or_else(|| {
                    wrap!(ErrorInt::RtspResponseError {
                        conn_ctx: *conn_ctx,
                        msg_ctx,
                        method: rtsp_types::Method::Setup,
                        cseq,
                        status,
                        description: "Transport header is missing server_port parameter".to_owned(),
                    })
                })?;
                let udp_sockets = stream.sockets.as_mut().unwrap();
                udp_sockets.remote_ip = source;
                udp_sockets.remote_rtp_port = server_port.0;
                udp_sockets.remote_rtcp_port = server_port.1;
                udp_sockets
                    .rtp_socket
                    .connect(SocketAddr::new(source, udp_sockets.remote_rtp_port))
                    .await
                    .map_err(|e| wrap!(ErrorInt::ConnectError(e)))?;
                udp_sockets
                    .rtcp_socket
                    .connect(SocketAddr::new(source, udp_sockets.remote_rtcp_port))
                    .await
                    .map_err(|e| wrap!(ErrorInt::ConnectError(e)))?;
                punch_firewall_hole(&udp_sockets.rtp_socket, &udp_sockets.rtcp_socket)
                    .await
                    .map_err(|e| wrap!(ErrorInt::ConnectError(e)))?;
            }
        }
        stream.state = StreamState::Init(StreamStateInit {
            ssrc: response.ssrc,
            initial_seq: None,
            initial_rtptime: None,
        });
        Ok(())
    }

    /// Sends a `PLAY` request for the entire presentation.
    ///
    /// The presentation must support aggregate control, as defined in [RFC 2326
    /// section 1.3](https://tools.ietf.org/html/rfc2326#section-1.3).
    pub async fn play(mut self, policy: PlayOptions) -> Result<Session<Playing>, Error> {
        let inner = self.0.as_mut().project();
        let conn = inner
            .conn
            .as_mut()
            .ok_or_else(|| wrap!(ErrorInt::FailedPrecondition("no connection".into())))?;
        let session = inner.session.as_ref().ok_or_else(|| {
            wrap!(ErrorInt::FailedPrecondition(
                "must SETUP before PLAY".into()
            ))
        })?;
        if let Some(ref t) = inner.presentation.tool {
            if matches!(inner.options.transport, Transport::Tcp) {
                warn!(
                    "Connecting via TCP to known-broken RTSP server {:?}. \
                        See <https://github.com/scottlamb/retina/issues/17>. \
                        Consider using UDP instead!",
                    &*t
                );
            }
        }

        trace!("PLAY with channel mappings: {:#?}", &conn.channels);
        *inner.maybe_playing = true;
        let (msg_ctx, cseq, response) = conn
            .send(
                ResponseMode::Play,
                inner.options,
                inner.presentation.tool.as_ref(),
                inner.requested_auth,
                &mut rtsp_types::Request::builder(Method::Play, rtsp_types::Version::V1_0)
                    .request_uri(inner.presentation.control.clone())
                    .header(rtsp_types::headers::SESSION, &*session.id)
                    .header(rtsp_types::headers::RANGE, "npt=0.000-".to_owned())
                    .build(Bytes::new()),
            )
            .await?;
        parse::parse_play(&response, inner.presentation).map_err(|description| {
            wrap!(ErrorInt::RtspResponseError {
                conn_ctx: *conn.inner.ctx(),
                msg_ctx,
                method: rtsp_types::Method::Play,
                cseq,
                status: response.status(),
                description,
            })
        })?;

        // Count how many streams have been setup (not how many are in the presentation).
        let setup_streams = inner
            .presentation
            .streams
            .iter()
            .filter(|s| matches!(s.state, StreamState::Init(_)))
            .count();

        let all_have_time = inner.presentation.streams.iter().all(|s| match s.state {
            StreamState::Init(StreamStateInit {
                initial_rtptime, ..
            }) => initial_rtptime.is_some(),
            _ => true,
        });

        // Move all streams that have been set up from Init to Playing state. Check that required
        // parameters are present while doing so.
        for (i, s) in inner.presentation.streams.iter_mut().enumerate() {
            match s.state {
                StreamState::Init(StreamStateInit {
                    initial_rtptime,
                    initial_seq,
                    ssrc,
                    ..
                }) => {
                    let initial_rtptime = match policy.initial_timestamp {
                        InitialTimestampPolicy::Require | InitialTimestampPolicy::Default
                            if setup_streams > 1 =>
                        {
                            if initial_rtptime.is_none() {
                                bail!(ErrorInt::RtspResponseError {
                                    conn_ctx: *conn.inner.ctx(),
                                    msg_ctx,
                                    method: rtsp_types::Method::Play,
                                    cseq,
                                    status: response.status(),
                                    description: format!(
                                        "Expected rtptime on PLAY with mode {:?}, missing on \
                                             stream {} ({:?}). Consider setting initial timestamp \
                                             mode permissive.",
                                        policy.initial_timestamp, i, &s.control
                                    ),
                                });
                            }
                            initial_rtptime
                        }
                        InitialTimestampPolicy::Permissive
                            if setup_streams > 1 && all_have_time =>
                        {
                            initial_rtptime
                        }
                        _ => None,
                    };
                    let initial_seq = match initial_seq {
                        Some(0) if policy.ignore_zero_seq => {
                            log::info!("Ignoring seq=0 on stream {}", i);
                            None
                        }
                        o => o,
                    };
                    let conn_ctx = conn.inner.ctx();
                    s.state = StreamState::Playing {
                        timeline: Timeline::new(
                            initial_rtptime,
                            s.clock_rate,
                            policy.enforce_timestamps_with_max_jump_secs,
                        )
                        .map_err(|description| {
                            wrap!(ErrorInt::RtspResponseError {
                                conn_ctx: *conn_ctx,
                                msg_ctx,
                                method: rtsp_types::Method::Play,
                                cseq,
                                status: response.status(),
                                description,
                            })
                        })?,
                        rtp_handler: rtp::InorderParser::new(ssrc, initial_seq),
                    };
                }
                StreamState::Uninit => {}
                StreamState::Playing { .. } => unreachable!(),
            };
        }
        *inner.keepalive_timer = Some(Box::pin(tokio::time::sleep(KEEPALIVE_DURATION)));
        Ok(Session(self.0, Playing(())))
    }
}

/// Notes an unexpected RTSP interleaved data message.
///
/// This is assumed to be due to a live555 RTP/AVP/TCP session that belonged
/// to a since-closed RTSP connection, as described in case 2 of "Stale sessions"
/// at [`SessionGroup`]. If there's no known session which explains this,
/// adds an unknown session with live555's default timeout.
fn note_stale_live555_data(tool: Option<&Tool>, options: &SessionOptions) {
    let known_to_have_live555_tcp_bug = tool.map(Tool::has_live555_tcp_bug).unwrap_or(false);
    if !known_to_have_live555_tcp_bug {
        log::warn!(
            "Saw unexpected RTSP packet. This is presumed to be due to a bug in old live555 \
                    servers' TCP handling, though tool attribute {:?} does not refer to a \
                    known-buggy version. Consider switching to UDP.",
            tool
        );
    }

    let group = match options.session_group.as_ref() {
        Some(g) => g,
        None => {
            log::debug!("Not tracking stale session because there's no session group.");
            return;
        }
    };

    // The caller *might* have a better guess than LIVE555_EXPIRATION_SEC via a SETUP response,
    // but it's also possible for note_stale_live555_data to be called prior to SETUP.
    let expires =
        tokio::time::Instant::now() + std::time::Duration::from_secs(LIVE555_EXPIRATION_SEC);
    let seqnum;
    {
        let mut lock = group.sessions.lock().unwrap();
        for s in &lock.sessions {
            if s.is_tcp {
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
        }
        seqnum = lock.next_seqnum;
        lock.next_seqnum += 1;
        log::debug!(
            "Unexpected RTSP interleaved packet, presumed due to live555 stale \
             file descriptor bug; adding stale session {:?}/{} that will \
             expire in {} seconds.",
            group.debug_id(),
            seqnum,
            LIVE555_EXPIRATION_SEC,
        );
        lock.sessions.push(StaleSession {
            seqnum,
            expires,
            teardown_rx: None,
            is_tcp: true,
            maybe_playing: true,
        });
    }

    // Spawn a task which removes the stale session at its expiration.
    // We could instead prune expired entries on stale_session() calls and
    // set a deadline within await_stale_sessions() calls, which might be
    // a bit more efficient. But this is simpler given that we already are
    // spawning tasks for stale sessions created from Session's Drop impl.
    let group = group.clone();
    tokio::spawn(async move {
        tokio::time::sleep_until(expires).await;
        if !group.try_remove_seqnum(seqnum) {
            log::warn!(
                "Unable to find stale live555 file descriptor session {:?}/{} at expiration",
                group.debug_id(),
                seqnum
            );
        } else {
            log::debug!(
                "Stale live555 file descriptor bug session {:?}/{} presumed expired.",
                group.debug_id(),
                seqnum
            );
        }
    });
}

/// Sends dummy RTP and RTCP packets to punch a hole in connection-tracking
/// firewalls.
///
/// This is useful when the client is on the protected side of the firewall and
/// the server isn't. The server should discard these dummy packets, but they
/// prompt the firewall to add the appropriate connection tracking state for
/// server->client packets to make it through.
///
/// Note this is insufficient for NAT traversal; the NAT firewall must be
/// RTSP-aware to rewrite the Transport header's client_ports.
async fn punch_firewall_hole(
    rtp_socket: &UdpSocket,
    rtcp_socket: &UdpSocket,
) -> Result<(), std::io::Error> {
    #[rustfmt::skip]
    const DUMMY_RTP: [u8; 12] = [
        2 << 6,     // version=2 + p=0 + x=0 + cc=0
        0,          // m=0 + pt=0
        0, 0,       // sequence number=0
        0, 0, 0, 0, // timestamp=0 0,
        0, 0, 0, 0, // ssrc=0
    ];
    #[rustfmt::skip]
    const DUMMY_RTCP: [u8; 8] = [
        2 << 6,     // version=2 + p=0 + rc=0
        200,        // pt=200 (reception report)
        0, 1,       // length=1 (in 4-byte words minus 1)
        0, 0, 0, 0, // ssrc=0 (bogus but we don't know the ssrc reliably yet)
    ];
    rtp_socket.send(&DUMMY_RTP[..]).await?;
    rtcp_socket.send(&DUMMY_RTCP[..]).await?;
    Ok(())
}

/// An item yielded by [`Session<Playing>`]'s [`futures::stream::Stream`] impl.
#[derive(Debug)]
pub enum PacketItem {
    RtpPacket(rtp::Packet),
    SenderReport(rtp::SenderReport),
}

impl Session<Playing> {
    /// Returns a wrapper which demuxes/depacketizes into frames.
    ///
    /// Fails if a stream that has been setup can't be depacketized.
    pub fn demuxed(mut self) -> Result<Demuxed, Error> {
        let inner = self.0.as_mut().project();
        let conn = inner
            .conn
            .as_ref()
            .ok_or_else(|| wrap!(ErrorInt::FailedPrecondition("no connection".into())))?;
        for s in &mut inner.presentation.streams {
            if matches!(s.state, StreamState::Playing { .. }) {
                if let Err(ref description) = s.depacketizer {
                    bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *conn.inner.ctx(),
                        msg_ctx: *inner.describe_ctx,
                        method: rtsp_types::Method::Describe,
                        cseq: *inner.describe_cseq,
                        status: *inner.describe_status,
                        description: description.clone(),
                    });
                }
            }
        }
        Ok(Demuxed {
            state: DemuxedState::Waiting,
            session: self,
        })
    }

    /// Sends a `TEARDOWN`, ending the session.
    #[deprecated(since = "0.3.1", note = "Use `SessionGroup::await_teardown` instead")]
    pub async fn teardown(mut self) -> Result<(), Error> {
        let inner = self.0.as_mut().project();
        let mut req = rtsp_types::Request::builder(Method::Teardown, rtsp_types::Version::V1_0)
            .request_uri(inner.presentation.base_url.clone())
            .header(
                rtsp_types::headers::SESSION,
                inner.session.as_ref().unwrap().id.to_string(),
            )
            .build(Bytes::new());
        inner
            .conn
            .as_mut()
            .unwrap()
            .send(
                ResponseMode::Teardown,
                inner.options,
                inner.presentation.tool.as_ref(),
                inner.requested_auth,
                &mut req,
            )
            .await?;
        *inner.session = None;
        *inner.maybe_playing = false;
        Ok(())
    }

    fn handle_keepalive_timer(
        mut self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> Result<(), Error> {
        let inner = self.0.as_mut().project();
        let conn = inner
            .conn
            .as_mut()
            .ok_or_else(|| wrap!(ErrorInt::FailedPrecondition("no connection".into())))?;
        // Expect the previous keepalive request to have finished.
        match inner.keepalive_state {
            KeepaliveState::Flushing(cseq) => bail!(ErrorInt::WriteError {
                conn_ctx: *conn.inner.ctx(),
                source: std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    format!(
                        "Unable to write keepalive {} within {:?}",
                        cseq, KEEPALIVE_DURATION,
                    ),
                ),
            }),
            KeepaliveState::Waiting(cseq) => bail!(ErrorInt::RtspReadError {
                conn_ctx: *conn.inner.ctx(),
                msg_ctx: conn.inner.eof_ctx(),
                source: std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    format!(
                        "Server failed to respond to keepalive {} within {:?}",
                        cseq, KEEPALIVE_DURATION,
                    ),
                ),
            }),
            KeepaliveState::Idle => {}
        }

        // Currently the only outbound data should be keepalives, and the previous one
        // has already been flushed, so there's no reason the Sink shouldn't be ready.
        if matches!(conn.inner.poll_ready_unpin(cx), Poll::Pending) {
            bail!(ErrorInt::Internal(
                "Unexpectedly not ready to send keepalive".into()
            ));
        }

        // Send a new one and reset the timer.
        // Use a SET_PARAMETER with no body for keepalives, as recommended in the
        // ONVIF Streaming Specification version version 21.06 section 5.2.2.2.
        let session_id = &*inner.session.as_ref().unwrap().id;
        let mut req = rtsp_types::Request::builder(Method::SetParameter, rtsp_types::Version::V1_0)
            .request_uri(inner.presentation.base_url.clone())
            .header(rtsp_types::headers::SESSION, session_id.to_string())
            .build(Bytes::new());
        let cseq = conn.fill_req(inner.options, inner.requested_auth, &mut req)?;
        conn.inner
            .start_send_unpin(rtsp_types::Message::Request(req))
            .expect("encoding is infallible");
        *inner.keepalive_state = match conn.inner.poll_flush_unpin(cx) {
            Poll::Ready(Ok(())) => KeepaliveState::Waiting(cseq),
            Poll::Ready(Err(e)) => bail!(e),
            Poll::Pending => KeepaliveState::Flushing(cseq),
        };

        inner
            .keepalive_timer
            .as_mut()
            .expect("keepalive timer set in state Playing")
            .as_mut()
            .reset(tokio::time::Instant::now() + KEEPALIVE_DURATION);
        Ok(())
    }

    fn handle_response(
        mut self: Pin<&mut Self>,
        msg_ctx: &crate::RtspMessageContext,
        response: rtsp_types::Response<Bytes>,
    ) -> Result<(), Error> {
        let inner = self.0.as_mut().project();
        if matches!(inner.keepalive_state,
                    KeepaliveState::Waiting(cseq) if parse::get_cseq(&response) == Some(*cseq))
        {
            // We don't care if the keepalive response succeeds or fails. Just mark complete.
            *inner.keepalive_state = KeepaliveState::Idle;
            return Ok(());
        }

        // The only response we expect in this state is to our keepalive request.
        bail!(ErrorInt::RtspFramingError {
            conn_ctx: *inner
                .conn
                .as_ref()
                .expect("have conn when handling response")
                .inner
                .ctx(),
            msg_ctx: *msg_ctx,
            description: format!("Unexpected RTSP response {:#?}", response),
        })
    }

    fn handle_data(
        mut self: Pin<&mut Self>,
        msg_ctx: &RtspMessageContext,
        data: rtsp_types::Data<Bytes>,
    ) -> Result<Option<PacketItem>, Error> {
        let inner = self.0.as_mut().project();
        let conn = inner
            .conn
            .as_mut()
            .ok_or_else(|| wrap!(ErrorInt::FailedPrecondition("no connection".into())))?;
        let channel_id = data.channel_id();
        let pkt_ctx = crate::PacketContext(crate::PacketContextInner::Tcp {
            msg_ctx: *msg_ctx,
            channel_id,
        });
        let m = match conn.channels.lookup(channel_id) {
            Some(m) => m,
            None => {
                conn.handle_unassigned_data(
                    *msg_ctx,
                    inner.options,
                    inner.presentation.tool.as_ref(),
                    data,
                )?;
                return Ok(None);
            }
        };
        let stream = &mut inner.presentation.streams[m.stream_i];
        let (timeline, rtp_handler) = match &mut stream.state {
            StreamState::Playing {
                timeline,
                rtp_handler,
            } => (timeline, rtp_handler),
            _ => unreachable!(
                "Session<Playing>'s {}->{:?} not in Playing state",
                channel_id, m
            ),
        };
        match m.channel_type {
            ChannelType::Rtp => Ok(rtp_handler.rtp(
                inner.options,
                inner.presentation.tool.as_ref(),
                conn.inner.ctx(),
                &pkt_ctx,
                timeline,
                m.stream_i,
                data.into_body(),
            )?),
            ChannelType::Rtcp => {
                match rtp_handler.rtcp(
                    inner.options,
                    inner.presentation.tool.as_ref(),
                    &pkt_ctx,
                    timeline,
                    m.stream_i,
                    data.into_body(),
                ) {
                    Ok(p) => Ok(p),
                    Err(description) => Err(wrap!(ErrorInt::PacketError {
                        conn_ctx: *conn.inner.ctx(),
                        pkt_ctx,
                        stream_id: m.stream_i,
                        description,
                    })),
                }
            }
        }
    }

    /// Polls a single UDP stream, `inner.presentation.streams[i]`.
    ///
    /// Assumes `buf` is cleared and large enough for any UDP packet.
    /// Only returns `Poll::Pending` after both RTCP and RTP sockets have
    /// returned `Poll::Pending`.
    fn poll_udp_stream(
        &mut self,
        cx: &mut std::task::Context,
        buf: &mut tokio::io::ReadBuf,
        i: usize,
    ) -> Poll<Option<Result<PacketItem, Error>>> {
        debug_assert!(buf.filled().is_empty());
        let inner = self.0.as_mut().project();
        let conn_ctx = inner
            .conn
            .as_ref()
            .ok_or_else(|| wrap!(ErrorInt::FailedPrecondition("no connection".into())))?
            .inner
            .ctx();
        let s = &mut inner.presentation.streams[i];
        if let Some(sockets) = &mut s.sockets {
            let (timeline, rtp_handler) = match &mut s.state {
                StreamState::Playing {
                    timeline,
                    rtp_handler,
                } => (timeline, rtp_handler),
                _ => unreachable!("Session<Playing>'s {}->{:?} not in Playing state", i, s),
            };
            // Prioritize RTCP over RTP within a stream.
            while let Poll::Ready(r) = sockets.rtcp_socket.poll_recv(cx, buf) {
                let pkt_ctx = crate::PacketContext(crate::PacketContextInner::Udp {
                    local_addr: SocketAddr::new(sockets.local_ip, sockets.local_rtp_port + 1),
                    peer_addr: SocketAddr::new(sockets.remote_ip, sockets.remote_rtcp_port),
                    received_wall: crate::WallTime::now(),
                });
                match r {
                    Ok(()) => {
                        let msg = Bytes::copy_from_slice(buf.filled());
                        match rtp_handler.rtcp(
                            inner.options,
                            inner.presentation.tool.as_ref(),
                            &pkt_ctx,
                            timeline,
                            i,
                            msg,
                        ) {
                            Ok(Some(p)) => return Poll::Ready(Some(Ok(p))),
                            Ok(None) => buf.clear(),
                            Err(description) => {
                                return Poll::Ready(Some(Err(wrap!(ErrorInt::PacketError {
                                    conn_ctx: *conn_ctx,
                                    pkt_ctx,
                                    stream_id: i,
                                    description,
                                }))))
                            }
                        }
                    }
                    Err(source) => {
                        return Poll::Ready(Some(Err(wrap!(ErrorInt::UdpRecvError {
                            conn_ctx: *conn_ctx,
                            pkt_ctx,
                            source,
                        }))))
                    }
                }
            }
            while let Poll::Ready(r) = sockets.rtp_socket.poll_recv(cx, buf) {
                let pkt_ctx = crate::PacketContext(crate::PacketContextInner::Udp {
                    local_addr: SocketAddr::new(sockets.local_ip, sockets.local_rtp_port),
                    peer_addr: SocketAddr::new(sockets.remote_ip, sockets.remote_rtp_port),
                    received_wall: crate::WallTime::now(),
                });
                match r {
                    Ok(()) => {
                        let msg = Bytes::copy_from_slice(buf.filled());
                        match rtp_handler.rtp(
                            inner.options,
                            inner.presentation.tool.as_ref(),
                            conn_ctx,
                            &pkt_ctx,
                            timeline,
                            i,
                            msg,
                        ) {
                            Ok(Some(p)) => return Poll::Ready(Some(Ok(p))),
                            Ok(None) => buf.clear(),
                            Err(e) => return Poll::Ready(Some(Err(e))),
                        }
                    }
                    Err(source) => {
                        return Poll::Ready(Some(Err(wrap!(ErrorInt::UdpRecvError {
                            conn_ctx: *conn_ctx,
                            pkt_ctx,
                            source,
                        }))))
                    }
                }
            }
        }
        Poll::Pending
    }

    /// Polls all UDP streams, round-robining between them to avoid starvation.
    fn poll_udp(&mut self, cx: &mut std::task::Context) -> Poll<Option<Result<PacketItem, Error>>> {
        // For now, create a buffer on the stack large enough for any UDP packet, then
        // copy into a fresh allocation if it's actually used.
        // TODO: a ring buffer would be better: see
        // <https://github.com/scottlamb/retina/issues/6>.

        // SAFETY: this exactly matches an example in the documentation:
        // <https://doc.rust-lang.org/nightly/core/mem/union.MaybeUninit.html#initializing-an-array-element-by-element>.
        let mut buf: [MaybeUninit<u8>; 65_536] = unsafe { MaybeUninit::uninit().assume_init() };
        let mut buf = tokio::io::ReadBuf::uninit(&mut buf);

        // Assume 0 <= inner.udp_next_poll_i < inner.presentation.streams.len().
        // play() would have failed if there were no (setup) streams.
        let starting_i = *self.0.as_mut().project().udp_next_poll_i;
        loop {
            let inner = self.0.as_mut().project();
            let i = *inner.udp_next_poll_i;
            *inner.udp_next_poll_i += 1;
            if *inner.udp_next_poll_i == inner.presentation.streams.len() {
                *inner.udp_next_poll_i = 0;
            }

            if let Poll::Ready(r) = self.poll_udp_stream(cx, &mut buf, i) {
                return Poll::Ready(r);
            }

            if *self.0.as_mut().project().udp_next_poll_i == starting_i {
                break;
            }
        }
        Poll::Pending
    }
}

#[pin_project::pinned_drop]
impl PinnedDrop for SessionInner {
    fn drop(self: Pin<&mut Self>) {
        let this = self.project();

        let is_tcp = matches!(this.options.transport, Transport::Tcp);
        let just_try_once = match this.options.teardown {
            TeardownPolicy::Auto if is_tcp => {
                // If the server is known to have the live555 bug, try really hard to send a
                // TEARDOWN before considering the session cleaned up. Otherwise, try once on
                // the existing connection, primarily in case the server has
                // this bug but doesn't advertise a buggy version.
                !this
                    .presentation
                    .tool
                    .as_ref()
                    .map(Tool::has_live555_tcp_bug)
                    .unwrap_or(false)
            }
            TeardownPolicy::Auto | TeardownPolicy::Always => false,
            TeardownPolicy::Never => return,
        };

        let session = match this.session.take() {
            Some(s) => s,
            None => return,
        };

        // For now, assume the whole timeout is left.
        let expires = tokio::time::Instant::now()
            + std::time::Duration::from_secs(session.timeout_sec.into());

        // Track the session, if there is a group.
        let (teardown_tx, teardown_rx) = tokio::sync::watch::channel(None);
        let seqnum = if let Some(session_group) = this.options.session_group.as_ref() {
            let mut lock = session_group.sessions.lock().unwrap();
            let seqnum = lock.next_seqnum;
            lock.next_seqnum += 1;
            lock.sessions.push(StaleSession {
                seqnum,
                expires,
                teardown_rx: Some(teardown_rx),
                is_tcp,
                maybe_playing: *this.maybe_playing,
            });
            log::debug!(
                "{:?}/{} tracking TEARDOWN of session id {}",
                session_group.debug_id(),
                seqnum,
                &session.id
            );
            Some(seqnum)
        } else {
            None
        };

        tokio::spawn(teardown::background_teardown(
            seqnum,
            this.presentation.base_url.clone(),
            this.presentation.tool.take(),
            session.id,
            just_try_once,
            std::mem::take(this.options),
            this.requested_auth.take(),
            this.conn.take(),
            teardown_tx,
            expires,
        ));
    }
}

impl futures::Stream for Session<Playing> {
    type Item = Result<PacketItem, Error>;

    fn poll_next(
        mut self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Option<Self::Item>> {
        loop {
            // First try receiving data on the RTSP connection. Let this starve
            // sending keepalives; if we can't keep up, the server should
            // probably drop us.
            match Pin::new(&mut self.0.conn.as_mut().unwrap().inner).poll_next(cx) {
                Poll::Ready(Some(Ok(msg))) => match msg.msg {
                    rtsp_types::Message::Data(data) => {
                        match self.as_mut().handle_data(&msg.ctx, data) {
                            Err(e) => return Poll::Ready(Some(Err(e))),
                            Ok(Some(pkt)) => return Poll::Ready(Some(Ok(pkt))),
                            Ok(None) => continue,
                        };
                    }
                    rtsp_types::Message::Response(response) => {
                        if let Err(e) = self.as_mut().handle_response(&msg.ctx, response) {
                            return Poll::Ready(Some(Err(e)));
                        }
                        continue;
                    }
                    rtsp_types::Message::Request(request) => {
                        warn!("Received RTSP request in Playing state. Responding unimplemented.\n{:#?}",
                            request);
                    }
                },
                Poll::Ready(Some(Err(e))) => return Poll::Ready(Some(Err(e))),
                Poll::Ready(None) => return Poll::Ready(None),
                std::task::Poll::Pending => {}
            }

            // Next try receiving data on the UDP sockets, if any.
            if matches!(self.0.options.transport, Transport::Udp) {
                if let Poll::Ready(result) = self.as_mut().poll_udp(cx) {
                    return Poll::Ready(result);
                }
            }

            // Then check if it's time for a new keepalive.
            if matches!(
                self.0.keepalive_timer.as_mut().unwrap().as_mut().poll(cx),
                Poll::Ready(())
            ) {
                log::debug!("time for a keepalive");
                self.as_mut().handle_keepalive_timer(cx)?;
            }

            // Then finish flushing the current keepalive if necessary.
            if let KeepaliveState::Flushing(cseq) = self.0.keepalive_state {
                match self.0.conn.as_mut().unwrap().inner.poll_flush_unpin(cx) {
                    Poll::Ready(Ok(())) => self.0.keepalive_state = KeepaliveState::Waiting(cseq),
                    Poll::Ready(Err(e)) => return Poll::Ready(Some(Err(Error(Arc::new(e))))),
                    Poll::Pending => {}
                }
            }

            // Nothing to do. The poll calls above have already registered cx as necessary.
            return Poll::Pending;
        }
    }
}

enum DemuxedState {
    Waiting,
    Pulling(usize),
    Fused,
}

/// Wrapper returned by [`Session<Playing>::demuxed`] which demuxes/depacketizes into frames.
pub struct Demuxed {
    state: DemuxedState,
    session: Session<Playing>,
}

impl Demuxed {
    #[deprecated(since = "0.3.1", note = "Use `SessionGroup::await_teardown` instead")]
    pub async fn teardown(self) -> Result<(), Error> {
        #[allow(deprecated)]
        self.session.teardown().await
    }

    /// Returns the server's version as declared in the `DESCRIBE` response's `a:tool` SDP
    /// attribute.
    pub fn tool(&self) -> Option<&Tool> {
        self.session.tool()
    }

    /// Returns the available streams as described by the server.
    pub fn streams(&self) -> &[Stream] {
        self.session.streams()
    }
}

impl futures::Stream for Demuxed {
    type Item = Result<CodecItem, Error>;

    fn poll_next(
        mut self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        loop {
            let (stream_id, pkt) = match self.state {
                DemuxedState::Waiting => match ready!(Pin::new(&mut self.session).poll_next(cx)) {
                    Some(Ok(PacketItem::RtpPacket(p))) => (p.stream_id, Some(p)),
                    Some(Ok(PacketItem::SenderReport(p))) => {
                        return Poll::Ready(Some(Ok(CodecItem::SenderReport(p))))
                    }
                    Some(Err(e)) => return Poll::Ready(Some(Err(e))),
                    None => return Poll::Ready(None),
                },
                DemuxedState::Pulling(stream_id) => (stream_id, None),
                DemuxedState::Fused => return Poll::Ready(None),
            };
            let inner = self.session.0.as_mut().project();
            let depacketizer = match &mut inner.presentation.streams[stream_id].depacketizer {
                Ok(d) => d,
                Err(_) => unreachable!("depacketizer was Ok"),
            };
            let conn_ctx = inner
                .conn
                .as_ref()
                .ok_or_else(|| wrap!(ErrorInt::FailedPrecondition("no connection".into())))?
                .inner
                .ctx();
            if let Some(p) = pkt {
                let pkt_ctx = p.ctx;
                let stream_id = p.stream_id;
                let ssrc = p.ssrc;
                let sequence_number = p.sequence_number;
                depacketizer.push(p).map_err(|description| {
                    wrap!(ErrorInt::RtpPacketError {
                        conn_ctx: *conn_ctx,
                        pkt_ctx,
                        stream_id,
                        ssrc,
                        sequence_number,
                        description,
                    })
                })?;
            }
            match depacketizer.pull(conn_ctx) {
                Ok(Some(item)) => {
                    self.state = DemuxedState::Pulling(stream_id);
                    return Poll::Ready(Some(Ok(item)));
                }
                Ok(None) => {
                    self.state = DemuxedState::Waiting;
                    continue;
                }
                Err(e) => {
                    self.state = DemuxedState::Fused;
                    return Poll::Ready(Some(Err(e)));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::*;
    use crate::testutil::response;

    /// Cross-platform, tokio equivalent of `socketpair(2)`.
    async fn socketpair() -> (tokio::net::TcpStream, tokio::net::TcpStream) {
        // Another process on the machine could connect to the server and mess
        // this up, but that's unlikely enough to ignore in test code.
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let client = tokio::net::TcpStream::connect(addr);
        let server = listener.accept();
        (client.await.unwrap(), server.await.unwrap().0)
    }

    async fn connect_to_mock() -> (RtspConnection, crate::tokio::Connection) {
        let (client, server) = socketpair().await;
        let client = crate::tokio::Connection::from_stream(client).unwrap();
        let server = crate::tokio::Connection::from_stream(server).unwrap();
        let client = RtspConnection {
            inner: client,
            channels: ChannelMappings::default(),
            next_cseq: 1,
            seen_unassigned: false,
        };
        (client, server)
    }

    fn init_logging() {
        let h = mylog::Builder::new()
            .set_format(
                ::std::env::var("MOONFIRE_FORMAT")
                    .map_err(|_| ())
                    .and_then(|s| mylog::Format::from_str(&s))
                    .unwrap_or(mylog::Format::Google),
            )
            .set_spec(::std::env::var("MOONFIRE_LOG").as_deref().unwrap_or("info"))
            .build();
        let _ = h.install();
    }

    /// Receives a request and sends a response, filling in the matching `CSeq`.
    async fn req_response(
        server: &mut crate::tokio::Connection,
        expected_method: rtsp_types::Method,
        mut response: rtsp_types::Response<Bytes>,
    ) {
        let msg = server.next().await.unwrap().unwrap();
        let cseq = match msg.msg {
            rtsp_types::Message::Request(ref r) => {
                assert_eq!(r.method(), expected_method);
                r.header(&rtsp_types::headers::CSEQ).unwrap()
            }
            _ => panic!(),
        };
        response.insert_header(rtsp_types::headers::CSEQ, cseq.as_str());
        server
            .send(rtsp_types::Message::Response(response))
            .await
            .unwrap();
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
                rtsp_types::Method::Describe,
                response(include_bytes!("testdata/reolink_describe.txt"))
            ),
        );
        let mut session = session.unwrap();
        assert_eq!(session.streams().len(), 2);

        // SETUP.
        tokio::join!(
            async {
                session.setup(0).await.unwrap();
            },
            req_response(
                &mut server,
                rtsp_types::Method::Setup,
                response(include_bytes!("testdata/reolink_setup.txt"))
            ),
        );

        // PLAY.
        let (session, _) = tokio::join!(
            session.play(PlayOptions::default()),
            req_response(
                &mut server,
                rtsp_types::Method::Play,
                response(include_bytes!("testdata/reolink_play.txt"))
            ),
        );
        let drop_time;
        {
            let session = session.unwrap();
            tokio::pin!(session);

            // Packets: first ignored one (unassigned channel), then one passed through.
            tokio::join!(
                async {
                    match session.next().await {
                        Some(Ok(PacketItem::RtpPacket(p))) => {
                            assert_eq!(p.ssrc, 0xdcc4a0d8);
                            assert_eq!(p.sequence_number, 0x41d4);
                            assert_eq!(&p.payload[..], b"hello world");
                        }
                        o => panic!("unexpected item: {:#?}", o),
                    }
                },
                async {
                    let bad_pkt = b"data on unassigned channel";
                    server
                        .send(rtsp_types::Message::Data(rtsp_types::Data::new(
                            2,
                            Bytes::from_static(bad_pkt),
                        )))
                        .await
                        .unwrap();
                    let good_pkt = b"\x80\x60\x41\xd4\x00\x00\x00\x00\xdc\xc4\xa0\xd8hello world";
                    server
                        .send(rtsp_types::Message::Data(rtsp_types::Data::new(
                            0,
                            Bytes::from_static(good_pkt),
                        )))
                        .await
                        .unwrap();
                },
            );

            drop_time = tokio::time::Instant::now();
        };

        // Drop (initiated by exiting the scope above).
        // This server advertises an ancient version of live555, so Retina
        // sends a TEARDOWN even with TCP.
        let stale_sessions = group.stale_sessions();
        assert_eq!(stale_sessions.num_sessions, 1);
        tokio::join!(
            group.await_stale_sessions(&stale_sessions),
            req_response(
                &mut server,
                rtsp_types::Method::Teardown,
                response(include_bytes!("testdata/reolink_teardown.txt"))
            ),
        );
        assert_eq!(group.stale_sessions().num_sessions, 0);

        // elapsed is not zero because tokio advances the time unnecessarily, grr.
        // https://github.com/tokio-rs/tokio/issues/3108
        let elapsed = tokio::time::Instant::now() - drop_time;
        assert!(
            elapsed < std::time::Duration::from_secs(60),
            "elapsed={:?}",
            elapsed
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
                rtsp_types::Method::Describe,
                response(include_bytes!("testdata/reolink_describe.txt"))
            ),
        );
        let mut session = session.unwrap();
        assert_eq!(session.streams().len(), 2);

        // SETUP.
        tokio::join!(
            async {
                session.setup(0).await.unwrap();
            },
            req_response(
                &mut server,
                rtsp_types::Method::Setup,
                response(include_bytes!("testdata/reolink_setup.txt"))
            ),
        );

        // PLAY.
        let (session, _) = tokio::join!(
            session.play(PlayOptions::default()),
            req_response(
                &mut server,
                rtsp_types::Method::Play,
                response(include_bytes!("testdata/reolink_play.txt"))
            ),
        );
        let drop_time;
        {
            let session = session.unwrap();
            tokio::pin!(session);

            // Packet.
            tokio::join!(
                async {
                    match session.next().await {
                        Some(Ok(PacketItem::RtpPacket(p))) => {
                            assert_eq!(p.ssrc, 0xdcc4a0d8);
                            assert_eq!(p.sequence_number, 0x41d4);
                            assert_eq!(&p.payload[..], b"hello world");
                        }
                        o => panic!("unexpected item: {:#?}", o),
                    }
                },
                async {
                    let pkt = b"\x80\x60\x41\xd4\x00\x00\x00\x00\xdc\xc4\xa0\xd8hello world";
                    server
                        .send(rtsp_types::Message::Data(rtsp_types::Data::new(
                            0,
                            Bytes::from_static(pkt),
                        )))
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
        let stale_sessions = group.stale_sessions();
        assert_eq!(stale_sessions.num_sessions, 1);

        // Even if repeated attempts fail, the stale session will go await on timeout.
        // The "60" here is the RFC-defined default timeout when none is specified
        // in the SETUP response.
        group.await_stale_sessions(&stale_sessions).await;
        assert_eq!(group.stale_sessions().num_sessions, 0);

        // elapsed is not zero because tokio advances the time unnecessarily, grr.
        // https://github.com/tokio-rs/tokio/issues/3108
        let elapsed = tokio::time::Instant::now() - drop_time;
        assert!(
            elapsed >= std::time::Duration::from_secs(60),
            "elapsed={:?}",
            elapsed
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
        let bogus_rtp = rtsp_types::Message::Data(rtsp_types::Data::new(
            0,                                // RTP channel
            Bytes::from_static(b"bogus pkt"), // the real packet parses but this is fine.
        ));

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

        let stale_sessions = group.stale_sessions();
        assert_eq!(stale_sessions.num_sessions, 1);

        group.await_stale_sessions(&stale_sessions).await;
        let elapsed = tokio::time::Instant::now() - start;
        assert_eq!(group.stale_sessions().num_sessions, 0);

        assert!(
            elapsed >= std::time::Duration::from_secs(LIVE555_EXPIRATION_SEC),
            "elapsed={:?}",
            elapsed
        );
    }

    /// Tests ignoring bogus RTP and RTCP messages while waiting for PLAY response.
    #[tokio::test]
    async fn ignore_early_rtp_rtcp() {
        init_logging();
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();
        let bogus_rtp = rtsp_types::Message::Data(rtsp_types::Data::new(
            0,                                // RTP channel
            Bytes::from_static(b"bogus pkt"), // the real packet parses but this is fine.
        ));
        let bogus_rtcp = rtsp_types::Message::Data(rtsp_types::Data::new(
            1,                                // RTCP channel
            Bytes::from_static(b"bogus pkt"), // the real packet parses but this is fine.
        ));

        // DESCRIBE.
        let (session, _) = tokio::join!(
            Session::describe_with_conn(conn, SessionOptions::default(), url),
            async {
                req_response(
                    &mut server,
                    rtsp_types::Method::Describe,
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
                session.setup(0).await.unwrap();
            },
            req_response(
                &mut server,
                rtsp_types::Method::Setup,
                response(include_bytes!("testdata/reolink_setup.txt"))
            ),
        );

        // PLAY.
        let (session, _) = tokio::join!(session.play(PlayOptions::default()), async move {
            server.send(bogus_rtp).await.unwrap();
            server.send(bogus_rtcp).await.unwrap();
            req_response(
                &mut server,
                rtsp_types::Method::Play,
                response(include_bytes!("testdata/reolink_play.txt")),
            )
            .await
        },);
        let _session = session.unwrap();
    }

    // See with: cargo test -- --nocapture client::tests::print_sizes
    #[test]
    fn print_sizes() {
        init_logging();
        for (name, size) in &[
            ("PacketItem", std::mem::size_of::<PacketItem>()),
            ("Presentation", std::mem::size_of::<Presentation>()),
            ("RtspConnection", std::mem::size_of::<RtspConnection>()),
            (
                "Session",
                std::mem::size_of::<Session<Described>>(), // <Playing> is the same size.
            ),
            ("SessionInner", std::mem::size_of::<SessionInner>()),
            ("SessionOptions", std::mem::size_of::<SessionOptions>()),
            ("Demuxed", std::mem::size_of::<Demuxed>()),
            ("Stream", std::mem::size_of::<Stream>()),
            ("rtp::Packet", std::mem::size_of::<rtp::Packet>()),
            (
                "rtp::SenderReport",
                std::mem::size_of::<rtp::SenderReport>(),
            ),
        ] {
            println!("{:-40} {:4}", name, size);
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
        let stale_sessions = group.stale_sessions();
        assert_send(group.await_stale_sessions(&stale_sessions));
    }
}
