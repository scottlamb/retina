// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::mem::MaybeUninit;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::num::NonZeroU32;
use std::task::Poll;
use std::time::Instant;
use std::{borrow::Cow, fmt::Debug, num::NonZeroU16, pin::Pin};

use self::channel_mapping::*;
pub use self::timeline::Timeline;
use bytes::Bytes;
use futures::{ready, Future, SinkExt, StreamExt};
use log::{debug, trace, warn};
use pin_project::pin_project;
use rtsp_types::Method;
use tokio::net::UdpSocket;
use url::Url;

use crate::codec::CodecItem;
use crate::{Error, ErrorInt, RtspMessageContext};

mod channel_mapping;
mod parse;
pub mod rtp;
mod timeline;

/// Duration between keepalive RTSP requests during [Playing] state.
pub const KEEPALIVE_DURATION: std::time::Duration = std::time::Duration::from_secs(30);

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
    ignore_spurious_data: bool,
    transport: Transport,
}

#[derive(Copy, Clone, Debug)]
pub enum Transport {
    Tcp,

    /// UDP (experimental).
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
    /// Ignores RTSP interleaved data packets for channels that aren't assigned,
    /// aren't in PLAY state, or already have a different SSRC in use.
    ///
    /// This still assumes that for assigned channels, the packet's protocol
    /// (RTP or RTCP) matches the assignment. All known RTSP implementations
    /// only use RTP on even channels and RTCP on odd channels, so this seems
    /// reasonably safe.
    ///
    /// ``ignore_spurious_data` is necessary with some Reolink cameras for at
    /// least two reasons:
    /// *  Reolink RLC-410 (IPC_3816M) firmware version v2.0.0.1441_19032101:
    ///    the camera sent interleaved data that apparently belonged to a
    ///    previous RTSP session. This happened immediately on connection
    ///    establishment and continued for some time after the following PLAY
    ///    request.
    /// *  Reolink RLC-822A (IPC_523128M8MP) firmware v3.0.0.177_21012101):
    ///    the camera sent RTCP SR packets immediately *before* its PLAY
    ///    response rather than afterward. It's easiest to treat them similarly
    ///    to the above case and discard them. (An alternative workaround would
    ///    be to buffer them until after Retina has examined the server's
    ///    PLAY response.)
    ///
    /// Currently each packet is logged at debug priority. This may change.
    pub fn ignore_spurious_data(mut self, ignore_spurious_data: bool) -> Self {
        self.ignore_spurious_data = ignore_spurious_data;
        self
    }

    /// Use the given credentials when/if the server requests digest authentication.
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
}

/// Options which must be decided at `PLAY` time.
///
/// These are mostly adjustments for non-compliant server implementations.
/// See also [SessionOptions] for options which must be decided earlier.
#[derive(Default)]
pub struct PlayOptions {
    initial_timestamp: InitialTimestampPolicy,
    ignore_zero_seq: bool,
    enforce_timestamps_with_max_jump_secs: Option<NonZeroU32>,
}

impl PlayOptions {
    pub fn initial_timestamp(self, initial_timestamp: InitialTimestampPolicy) -> Self {
        Self {
            initial_timestamp,
            ..self
        }
    }

    /// If the `RTP-Time` specifies `seq=0`, ignore it. Some cameras set this value then start
    /// the stream with something dramatically different. (Eg the Hikvision DS-2CD2032-I on its
    /// metadata stream; the other streams are fine.)
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

#[derive(Debug)]
pub struct Presentation {
    pub streams: Vec<Stream>,
    base_url: Url,
    pub control: Url,
    pub accept_dynamic_rate: bool,
}

/// Information about a stream offered within a presentation.
/// Currently if multiple formats are offered, this only describes the first.
#[derive(Debug)]
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
    /// See the [registry](https://www.iana.org/assignments/rtp-parameters/rtp-parameters.xhtml#rtp-parameters-1).
    /// It's common to use one of the dynamically assigned values, 96–127.
    pub rtp_payload_type: u8,

    /// RTP clock rate, in Hz.
    pub clock_rate: u32,

    /// Number of audio channels, if applicable (`media` is `audio`) and known.
    pub channels: Option<NonZeroU16>,

    depacketizer: Result<crate::codec::Depacketizer, String>,

    /// The specified control URL.
    /// This is needed with multiple streams to send `SETUP` requests and
    /// interpret the `PLAY` response's `RTP-Info` header.
    /// [RFC 2326 section C.3](https://datatracker.ietf.org/doc/html/rfc2326#appendix-C.3)
    /// says the server is allowed to omit it when there is only a single stream.
    pub control: Option<Url>,

    /// The sockets for `Transport::Udp`.
    sockets: Option<UdpSockets>,

    state: StreamState,
}

#[derive(Debug)]
struct UdpSockets {
    local_ip: IpAddr,
    local_rtp_port: u16,
    remote_ip: IpAddr,
    remote_rtp_port: u16,
    rtp_socket: UdpSocket,
    remote_rtcp_port: u16,
    rtcp_socket: UdpSocket,
}

impl Stream {
    /// Returns the parameters for this stream.
    ///
    /// Returns `None` on unknown codecs, bad parameters, or if parameters aren't specified
    /// via SDP. Some codecs allow parameters to be specified in-band instead.
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

#[derive(Clone)]
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
}

/// Mode to use in `RtspConnection::send` when looking for a response.
enum ResponseMode {
    /// Anything but the response to this request is an error.
    Normal,

    /// Silently discard data messages and responses to the given keepalive
    /// while awaiting the response to this request.
    Teardown { keepalive_cseq: Option<u32> },
}

/// An RTSP session, or a connection that may be used in a proscriptive way.
/// See discussion at [State].
pub struct Session<S: State>(Pin<Box<SessionInner>>, S);

#[pin_project]
struct SessionInner {
    // TODO: allow this to be closed and reopened during a UDP session?
    conn: RtspConnection,

    options: SessionOptions,
    requested_auth: Option<digest_auth::WwwAuthenticateHeader>,
    presentation: Presentation,

    /// This will be set iff one or more `SETUP` calls have been issued.
    /// This is sometimes true in state `Described` and always true in state
    /// `Playing`.
    session_id: Option<Box<str>>,

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

    /// Sends a request and expects the next message from the peer to be its response.
    /// Takes care of authorization and `CSeq`. Returns `Error` if not successful.
    async fn send(
        &mut self,
        mode: ResponseMode,
        options: &SessionOptions,
        requested_auth: &mut Option<digest_auth::WwwAuthenticateHeader>,
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
                match msg.msg {
                    rtsp_types::Message::Response(r) => {
                        if let Some(response_cseq) = parse::get_cseq(&r) {
                            if response_cseq == cseq {
                                break (r, msg.ctx);
                            }
                            if let ResponseMode::Teardown {
                                keepalive_cseq: Some(k),
                            } = mode
                            {
                                if response_cseq == k {
                                    debug!("ignoring keepalive {} response during TEARDOWN", k);
                                    continue;
                                }
                            }
                        }
                    }
                    rtsp_types::Message::Data(_)
                        if matches!(mode, ResponseMode::Teardown { .. }) =>
                    {
                        debug!("ignoring RTSP data during TEARDOWN");
                        continue;
                    }
                    rtsp_types::Message::Data(d) if options.ignore_spurious_data => {
                        debug!(
                            "ignoring interleaved data message on channel {} while waiting \
                                for response to {} CSeq {}",
                            d.channel_id(),
                            method,
                            cseq
                        );
                        continue;
                    }
                    o => bail!(ErrorInt::RtspFramingError {
                        conn_ctx: *self.inner.ctx(),
                        msg_ctx: msg.ctx,
                        description: format!(
                            "Expected response to {} CSeq {}, got {:?}",
                            method, cseq, o,
                        ),
                    }),
                };
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
                let www_authenticate = www_authenticate.as_str();
                if !www_authenticate.starts_with("Digest ") {
                    // TODO: the header(s) might also indicate both Basic and Digest; we shouldn't
                    // error or not based on ordering.
                    bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *self.inner.ctx(),
                        msg_ctx,
                        method: req.method().clone(),
                        cseq,
                        status: resp.status(),
                        description: format!(
                            "Non-digest authentication requested: {}",
                            www_authenticate
                        ),
                    })
                }
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
                let www_authenticate = digest_auth::WwwAuthenticateHeader::parse(www_authenticate)
                    .map_err(|e| {
                        wrap!(ErrorInt::RtspResponseError {
                            conn_ctx: *self.inner.ctx(),
                            msg_ctx,
                            method: req.method().clone(),
                            cseq,
                            status: resp.status(),
                            description: format!(
                                "Bad WWW-Authenticate header {:?}: {}",
                                www_authenticate, e
                            ),
                        })
                    })?;
                *requested_auth = Some(www_authenticate);
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

    /// Fills out `req` with authorization and `CSeq` headers.
    fn fill_req(
        &mut self,
        options: &SessionOptions,
        requested_auth: &mut Option<digest_auth::WwwAuthenticateHeader>,
        req: &mut rtsp_types::Request<Bytes>,
    ) -> Result<u32, Error> {
        let cseq = self.next_cseq;
        self.next_cseq += 1;
        if let Some(ref mut auth) = requested_auth {
            let creds = options
                .creds
                .as_ref()
                .expect("creds were checked when filling request_auth");
            let uri = req.request_uri().map(|u| u.as_str()).unwrap_or("*");
            let method = digest_auth::HttpMethod(Cow::Borrowed(req.method().into()));
            let ctx = digest_auth::AuthContext::new_with_method(
                &creds.username,
                &creds.password,
                uri,
                Option::<&'static [u8]>::None,
                method,
            );

            // digest_auth's comments seem to say 'respond' failing means a parser bug.
            let authorization = auth
                .respond(&ctx)
                .map_err(|e| wrap!(ErrorInt::Internal(e.into())))?
                .to_string();
            req.insert_header(rtsp_types::headers::AUTHORIZATION, authorization);
        }
        req.insert_header(rtsp_types::headers::CSEQ, cseq.to_string());
        if let Some(ref u) = options.user_agent {
            req.insert_header(rtsp_types::headers::USER_AGENT, u.to_string());
        }
        Ok(cseq)
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
        Ok(Session(
            Box::pin(SessionInner {
                conn,
                options,
                requested_auth,
                presentation,
                session_id: None,
                describe_ctx: msg_ctx,
                describe_cseq: cseq,
                describe_status: response.status(),
                keepalive_state: KeepaliveState::Idle,
                keepalive_timer: None,
                udp_next_poll_i: 0,
            }),
            Described(()),
        ))
    }

    pub fn streams(&self) -> &[Stream] {
        &self.0.presentation.streams
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
        let conn = &mut inner.conn;
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
                        "RTP/AVP/UDP;client_port={}-{}",
                        pair.rtp_port,
                        pair.rtp_port + 1,
                    ),
                );
            }
        }
        if let Some(ref s) = inner.session_id {
            req = req.header(rtsp_types::headers::SESSION, s.to_string());
        }
        let (msg_ctx, cseq, response) = conn
            .send(
                ResponseMode::Normal,
                &inner.options,
                &mut inner.requested_auth,
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
        match inner.session_id.as_ref() {
            Some(old) if old.as_ref() != response.session_id => {
                bail!(ErrorInt::RtspResponseError {
                    conn_ctx: *inner.conn.inner.ctx(),
                    msg_ctx,
                    method: rtsp_types::Method::Setup,
                    cseq,
                    status,
                    description: format!(
                        "session id changed from {:?} to {:?}",
                        old, response.session_id,
                    ),
                });
            }
            Some(_) => {}
            None => *inner.session_id = Some(response.session_id.into()),
        };
        let conn_ctx = conn.inner.ctx();
        match options.transport {
            Transport::Tcp => {
                let channel_id = match response.channel_id {
                    Some(id) => id,
                    None => bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *inner.conn.inner.ctx(),
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
        let session_id = inner.session_id.as_deref().ok_or_else(|| {
            wrap!(ErrorInt::FailedPrecondition(
                "must SETUP before PLAY".into()
            ))
        })?;
        trace!("PLAY with channel mappings: {:#?}", &inner.conn.channels);
        let (msg_ctx, cseq, response) = inner
            .conn
            .send(
                ResponseMode::Normal,
                &inner.options,
                inner.requested_auth,
                &mut rtsp_types::Request::builder(Method::Play, rtsp_types::Version::V1_0)
                    .request_uri(inner.presentation.control.clone())
                    .header(rtsp_types::headers::SESSION, session_id.clone())
                    .header(rtsp_types::headers::RANGE, "npt=0.000-".to_owned())
                    .build(Bytes::new()),
            )
            .await?;
        parse::parse_play(&response, inner.presentation).map_err(|description| {
            wrap!(ErrorInt::RtspResponseError {
                conn_ctx: *inner.conn.inner.ctx(),
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
                                    conn_ctx: *inner.conn.inner.ctx(),
                                    msg_ctx,
                                    method: rtsp_types::Method::Play,
                                    cseq,
                                    status: response.status(),
                                    description: format!(
                                        "Expected rtptime on PLAY with mode {:?}, missing on \
                                             stream {} ({:?}). Consider setting initial timestamp \
                                             mode use-if-all-present.",
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
                    let conn_ctx = inner.conn.inner.ctx();
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
        for s in &mut inner.presentation.streams {
            if matches!(s.state, StreamState::Playing { .. }) {
                if let Err(ref description) = s.depacketizer {
                    bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *inner.conn.inner.ctx(),
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

    /// Tears down the session.
    ///
    /// This attempts to send a `TEARDOWN` request to end the session:
    /// *   When using UDP, this signals the server to end the data stream
    ///     promptly rather than wait for timeout.
    /// *   Even when using TCP, some old versions of `live555` servers will
    ///     incorrectly keep trying to send packets to this connection, burning
    ///     CPU until timeout, and potentially sending packets to a freshly
    ///     opened connection that happens to claim the same file descriptor
    ///     number.
    ///
    /// Discards any RTSP interleaved data messages received on the socket
    /// while waiting for `TEARDOWN` response.
    ///
    /// Currently closes the socket(s) immediately after `TEARDOWN` response,
    /// even on failure. This behavior may change in a future release.
    pub async fn teardown(mut self) -> Result<(), Error> {
        let inner = self.0.as_mut().project();
        let mut req = rtsp_types::Request::builder(Method::Teardown, rtsp_types::Version::V1_0)
            .request_uri(inner.presentation.base_url.clone())
            .header(
                rtsp_types::headers::SESSION,
                inner.session_id.as_deref().unwrap().to_string(),
            )
            .build(Bytes::new());
        let keepalive_cseq = match inner.keepalive_state {
            KeepaliveState::Idle => None,
            KeepaliveState::Flushing(cseq) => Some(*cseq),
            KeepaliveState::Waiting(cseq) => Some(*cseq),
        };
        inner
            .conn
            .send(
                ResponseMode::Teardown { keepalive_cseq },
                inner.options,
                inner.requested_auth,
                &mut req,
            )
            .await?;
        Ok(())
    }

    pub fn streams(&self) -> &[Stream] {
        &self.0.presentation.streams
    }

    fn handle_keepalive_timer(
        mut self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> Result<(), Error> {
        let inner = self.0.as_mut().project();
        // Expect the previous keepalive request to have finished.
        match inner.keepalive_state {
            KeepaliveState::Flushing(cseq) => bail!(ErrorInt::WriteError {
                conn_ctx: *inner.conn.inner.ctx(),
                source: std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    format!(
                        "Unable to write keepalive {} within {:?}",
                        cseq, KEEPALIVE_DURATION,
                    ),
                ),
            }),
            KeepaliveState::Waiting(cseq) => bail!(ErrorInt::RtspReadError {
                conn_ctx: *inner.conn.inner.ctx(),
                msg_ctx: inner.conn.inner.eof_ctx(),
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
        if matches!(inner.conn.inner.poll_ready_unpin(cx), Poll::Pending) {
            bail!(ErrorInt::Internal(
                "Unexpectedly not ready to send keepalive".into()
            ));
        }

        // Send a new one and reset the timer.
        // Use a SET_PARAMETER with no body for keepalives, as recommended in the
        // ONVIF Streaming Specification version version 21.06 section 5.2.2.2.
        let session_id = inner.session_id.as_deref().unwrap();
        let mut req = rtsp_types::Request::builder(Method::SetParameter, rtsp_types::Version::V1_0)
            .request_uri(inner.presentation.base_url.clone())
            .header(rtsp_types::headers::SESSION, session_id.to_string())
            .build(Bytes::new());
        let cseq = inner
            .conn
            .fill_req(inner.options, inner.requested_auth, &mut req)?;
        inner
            .conn
            .inner
            .start_send_unpin(rtsp_types::Message::Request(req))
            .expect("encoding is infallible");
        *inner.keepalive_state = match inner.conn.inner.poll_flush_unpin(cx) {
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
            conn_ctx: *inner.conn.inner.ctx(),
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
        let channel_id = data.channel_id();
        let pkt_ctx = crate::PacketContext(crate::PacketContextInner::Tcp {
            msg_ctx: *msg_ctx,
            channel_id,
        });
        let m = match inner.conn.channels.lookup(channel_id) {
            Some(m) => m,
            None if inner.options.ignore_spurious_data => {
                log::debug!(
                    "Ignoring interleaved data on unassigned channel id {}",
                    channel_id
                );
                return Ok(None);
            }
            None => bail!(ErrorInt::RtspUnassignedChannelError {
                conn_ctx: *inner.conn.inner.ctx(),
                msg_ctx: *msg_ctx,
                channel_id,
            }),
        };
        let stream = &mut inner.presentation.streams[m.stream_i];
        let (mut timeline, rtp_handler) = match &mut stream.state {
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
                &inner.options,
                inner.conn.inner.ctx(),
                &pkt_ctx,
                &mut timeline,
                m.stream_i,
                data.into_body(),
            )?),
            ChannelType::Rtcp => match rtp_handler.rtcp(
                &inner.options,
                &pkt_ctx,
                &mut timeline,
                m.stream_i,
                data.into_body(),
            ) {
                Ok(p) => Ok(p),
                Err(description) => Err(wrap!(ErrorInt::PacketError {
                    conn_ctx: *inner.conn.inner.ctx(),
                    pkt_ctx: pkt_ctx,
                    stream_id: m.stream_i,
                    description,
                })),
            },
        }
    }

    /// Polls a single UDP stream, `inner.presentation.streams[i]`.
    /// Assumes `buf` is cleared and large enough for any UDP packet.
    fn poll_udp_stream(
        &mut self,
        cx: &mut std::task::Context,
        buf: &mut tokio::io::ReadBuf,
        i: usize,
    ) -> Poll<Option<Result<PacketItem, Error>>> {
        debug_assert!(buf.filled().is_empty());
        let inner = self.0.as_mut().project();
        let s = &mut inner.presentation.streams[i];
        if let Some(sockets) = &mut s.sockets {
            let (mut timeline, rtp_handler) = match &mut s.state {
                StreamState::Playing {
                    timeline,
                    rtp_handler,
                } => (timeline, rtp_handler),
                _ => unreachable!("Session<Playing>'s {}->{:?} not in Playing state", i, s),
            };
            // Prioritize RTCP over RTP within a stream.
            if let Poll::Ready(r) = sockets.rtcp_socket.poll_recv(cx, buf) {
                let pkt_ctx = crate::PacketContext(crate::PacketContextInner::Udp {
                    local_addr: SocketAddr::new(sockets.local_ip, sockets.local_rtp_port + 1),
                    peer_addr: SocketAddr::new(sockets.remote_ip, sockets.remote_rtcp_port),
                    received_wall: crate::WallTime::now(),
                    received: Instant::now(),
                });
                match r {
                    Ok(()) => {
                        let msg = Bytes::copy_from_slice(buf.filled());
                        match rtp_handler.rtcp(&inner.options, &pkt_ctx, &mut timeline, i, msg) {
                            Ok(Some(p)) => return Poll::Ready(Some(Ok(p))),
                            Ok(None) => buf.clear(),
                            Err(description) => {
                                return Poll::Ready(Some(Err(wrap!(ErrorInt::PacketError {
                                    conn_ctx: *inner.conn.inner.ctx(),
                                    pkt_ctx,
                                    stream_id: i,
                                    description,
                                }))))
                            }
                        }
                    }
                    Err(source) => {
                        return Poll::Ready(Some(Err(wrap!(ErrorInt::UdpRecvError {
                            conn_ctx: *inner.conn.inner.ctx(),
                            pkt_ctx,
                            source,
                        }))))
                    }
                }
            }
            if let Poll::Ready(r) = sockets.rtp_socket.poll_recv(cx, buf) {
                let pkt_ctx = crate::PacketContext(crate::PacketContextInner::Udp {
                    local_addr: SocketAddr::new(sockets.local_ip, sockets.local_rtp_port),
                    peer_addr: SocketAddr::new(sockets.remote_ip, sockets.remote_rtp_port),
                    received_wall: crate::WallTime::now(),
                    received: Instant::now(),
                });
                match r {
                    Ok(()) => {
                        let msg = Bytes::copy_from_slice(buf.filled());
                        match rtp_handler.rtp(
                            &inner.options,
                            inner.conn.inner.ctx(),
                            &pkt_ctx,
                            &mut timeline,
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
                            conn_ctx: *inner.conn.inner.ctx(),
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
            match Pin::new(&mut self.0.conn.inner).poll_next(cx) {
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
                match self.0.conn.inner.poll_flush_unpin(cx) {
                    Poll::Ready(Ok(())) => self.0.keepalive_state = KeepaliveState::Waiting(cseq),
                    Poll::Ready(Err(e)) => return Poll::Ready(Some(Err(Error(Box::new(e))))),
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
    /// Tears down the session; see [`Session<Playing>::teardown`].
    pub async fn teardown(self) -> Result<(), Error> {
        self.session.teardown().await
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
            let conn_ctx = inner.conn.inner.ctx();
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
        };
        (client, server)
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

    /// Test the happy path of session initialization.
    #[tokio::test]
    async fn simple() {
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();

        // DESCRIBE.
        let (session, _) = tokio::join!(
            Session::describe_with_conn(conn, SessionOptions::default(), url),
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

        // End of stream.
        tokio::join!(
            async {
                assert!(session.next().await.is_none());
            },
            async {
                server.close().await.unwrap();
            },
        );
    }

    /// Tests the `ignore_spurious_data` feature:
    /// *   ignore a data packet while waiting for a RTSP response early on.
    /// *   ignore a data packet with the wrong ssrc after play.
    #[tokio::test]
    async fn ignore_spurious_data() {
        let (conn, mut server) = connect_to_mock().await;
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();
        let bogus_pkt = rtsp_types::Message::Data(rtsp_types::Data::new(
            0,
            Bytes::from_static(b"\x80\x60\xaa\xaa\x00\x00\x00\x00\xbb\xbb\xbb\xbbbogus pkt"),
        ));

        // DESCRIBE.
        let options = SessionOptions::default().ignore_spurious_data(true);
        let (session, _) = tokio::join!(Session::describe_with_conn(conn, options, url), async {
            server.send(bogus_pkt.clone()).await.unwrap();
            req_response(
                &mut server,
                rtsp_types::Method::Describe,
                response(include_bytes!("testdata/reolink_describe.txt")),
            )
            .await;
        },);
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
                server.send(bogus_pkt).await.unwrap();
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

        // End of stream.
        tokio::join!(
            async {
                assert!(session.next().await.is_none());
            },
            async {
                server.close().await.unwrap();
            },
        );
    }

    // See with: cargo test -- --nocapture client::tests::print_sizes
    #[test]
    fn print_sizes() {
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
}
