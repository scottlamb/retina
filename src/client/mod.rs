// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::num::NonZeroU32;
use std::task::Poll;
use std::{borrow::Cow, fmt::Debug, num::NonZeroU16, pin::Pin};

use self::channel_mapping::*;
pub use self::timeline::Timeline;
use bytes::Bytes;
use futures::{ready, Future, SinkExt, StreamExt};
use log::{debug, trace, warn};
use pin_project::pin_project;
use sdp::session_description::SessionDescription;
use tokio::pin;
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

/// Policy decisions to make on `PLAY`.
///
/// These are mostly adjustments for non-compliant server implementations.
#[derive(Default)]
pub struct PlayPolicy {
    initial_timestamp: InitialTimestampPolicy,
    ignore_zero_seq: bool,
    enforce_timestamps_with_max_jump_secs: Option<NonZeroU32>,
}

impl PlayPolicy {
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
    sdp: SessionDescription,
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

    /// Some buggy cameras expect the base URL to be interpreted as if it had an
    /// implicit trailing slash. (This is approximately what ffmpeg 4.3.1 does
    /// when the base URL has a query string.) If `RTP-Info` matching fails, try
    /// again with this URL.
    alt_control: Option<Url>,

    state: StreamState,
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

    /// `SETUP` reply has been received.
    Init(StreamStateInit),

    /// `PLAY` reply has been received.
    Playing {
        timeline: Timeline,
        rtp_handler: rtp::StrictSequenceChecker,
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
/// One or more `SETUP`s may have also been issued, in which case a `session_id`
/// will be assigned.
#[doc(hidden)]
pub struct Described {
    presentation: Presentation,
    session_id: Option<String>,
    channels: ChannelMappings,

    // Keep some information about the DESCRIBE response. If a depacketizer
    // couldn't be constructed correctly for one or more streams, this will be
    // used to create a RtspResponseError on `State<Playing>::demuxed()`.
    // We defer such errors from DESCRIBE time until then because they only
    // matter if the stream is setup and the caller wants depacketization.
    describe_ctx: RtspMessageContext,
    describe_cseq: u32,
    describe_status: rtsp_types::StatusCode,
}
impl State for Described {}

enum KeepaliveState {
    Idle,
    Flushing(u32),
    Waiting(u32),
}

/// State after a `PLAY`; use via `Session<Playing>`.
#[doc(hidden)]
#[pin_project(project = PlayingProj)]
pub struct Playing {
    presentation: Presentation,
    session_id: String,
    channels: ChannelMappings,
    keepalive_state: KeepaliveState,
    describe_ctx: RtspMessageContext,
    describe_cseq: u32,
    describe_status: rtsp_types::StatusCode,

    #[pin]
    keepalive_timer: tokio::time::Sleep,
}
impl State for Playing {}

/// The raw connection, without tracking session state.
struct RtspConnection {
    creds: Option<Credentials>,
    requested_auth: Option<digest_auth::WwwAuthenticateHeader>,
    inner: crate::tokio::Connection,
    user_agent: String,

    /// The next `CSeq` header value to use when sending an RTSP request.
    next_cseq: u32,
}

/// An RTSP session, or a connection that may be used in a proscriptive way.
/// See discussion at [State].
#[pin_project]
pub struct Session<S: State> {
    conn: RtspConnection,

    #[pin]
    state: S,
}

impl RtspConnection {
    async fn connect(url: &Url, creds: Option<Credentials>) -> Result<Self, Error> {
        let host =
            RtspConnection::validate_url(url).map_err(|e| wrap!(ErrorInt::InvalidArgument(e)))?;
        let port = url.port().unwrap_or(554);
        let inner = crate::tokio::Connection::connect(host, port)
            .await
            .map_err(|e| wrap!(ErrorInt::ConnectError(e)))?;
        Ok(Self {
            inner,
            creds,
            requested_auth: None,
            user_agent: "moonfire-rtsp test".to_string(),
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
        req: &mut rtsp_types::Request<Bytes>,
    ) -> Result<(RtspMessageContext, u32, rtsp_types::Response<Bytes>), Error> {
        loop {
            let cseq = self.fill_req(req)?;
            self.inner
                .send(rtsp_types::Message::Request(req.clone()))
                .await
                .map_err(|e| wrap!(e))?;
            let method: &str = req.method().into();
            let msg = self.inner.next().await.unwrap_or_else(|| {
                bail!(ErrorInt::ReadError {
                    conn_ctx: *self.inner.ctx(),
                    msg_ctx: self.inner.eof_ctx(),
                    source: std::io::Error::new(
                        std::io::ErrorKind::UnexpectedEof,
                        format!("EOF while expecting reply to {} CSeq {}", method, cseq),
                    ),
                })
            })?;
            let resp = match msg.msg {
                rtsp_types::Message::Response(r) if parse::get_cseq(&r) == Some(cseq) => r,
                o => bail!(ErrorInt::RtspFramingError {
                    conn_ctx: *self.inner.ctx(),
                    msg_ctx: msg.ctx,
                    description: format!("Expected reply to {} CSeq {}, got {:?}", method, cseq, o,),
                }),
            };
            if resp.status() == rtsp_types::StatusCode::Unauthorized {
                if self.requested_auth.is_some() {
                    // TODO: the WWW-Authenticate might indicate a new domain or nonce.
                    // In that case, we should retry rather than returning error.
                    bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *self.inner.ctx(),
                        msg_ctx: msg.ctx,
                        method: req.method().clone(),
                        cseq,
                        status: resp.status(),
                        description: "Received Unauthorized after trying digest auth".into(),
                    })
                }
                let www_authenticate = match resp.header(&rtsp_types::headers::WWW_AUTHENTICATE) {
                    None => bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *self.inner.ctx(),
                        msg_ctx: msg.ctx,
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
                        msg_ctx: msg.ctx,
                        method: req.method().clone(),
                        cseq,
                        status: resp.status(),
                        description: format!(
                            "Non-digest authentication requested: {}",
                            www_authenticate
                        ),
                    })
                }
                if self.creds.is_none() {
                    bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *self.inner.ctx(),
                        msg_ctx: msg.ctx,
                        method: req.method().clone(),
                        cseq,
                        status: resp.status(),
                        description: "Authentication requested and no credentials supplied"
                            .to_owned(),
                    })
                }
                let msg_ctx = msg.ctx;
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
                self.requested_auth = Some(www_authenticate);
                continue;
            } else if !resp.status().is_success() {
                bail!(ErrorInt::RtspResponseError {
                    conn_ctx: *self.inner.ctx(),
                    msg_ctx: msg.ctx,
                    method: req.method().clone(),
                    cseq,
                    status: resp.status(),
                    description: "Unexpected RTSP response status".into(),
                });
            }
            return Ok((msg.ctx, cseq, resp));
        }
    }

    /// Fills out `req` with authorization and `CSeq` headers.
    fn fill_req(&mut self, req: &mut rtsp_types::Request<Bytes>) -> Result<u32, Error> {
        let cseq = self.next_cseq;
        self.next_cseq += 1;
        if let Some(ref mut auth) = self.requested_auth {
            let creds = self
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
        req.insert_header(rtsp_types::headers::USER_AGENT, self.user_agent.clone());
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
    pub async fn describe(url: Url, creds: Option<Credentials>) -> Result<Self, Error> {
        let mut conn = RtspConnection::connect(&url, creds).await?;
        let mut req =
            rtsp_types::Request::builder(rtsp_types::Method::Describe, rtsp_types::Version::V1_0)
                .header(rtsp_types::headers::ACCEPT, "application/sdp")
                .request_uri(url.clone())
                .build(Bytes::new());
        let (msg_ctx, cseq, response) = conn.send(&mut req).await?;
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
        Ok(Session {
            conn,
            state: Described {
                presentation,
                session_id: None,
                channels: ChannelMappings::default(),
                describe_ctx: msg_ctx,
                describe_cseq: cseq,
                describe_status: response.status(),
            },
        })
    }

    pub fn streams(&self) -> &[Stream] {
        &self.state.presentation.streams
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
        let stream = &mut self.state.presentation.streams[stream_i];
        if !matches!(stream.state, StreamState::Uninit) {
            bail!(ErrorInt::FailedPrecondition("stream already set up".into()));
        }
        let proposed_channel_id = self.state.channels.next_unassigned().ok_or_else(|| {
            wrap!(ErrorInt::FailedPrecondition(
                "no unassigned channels".into()
            ))
        })?;
        let url = stream
            .control
            .as_ref()
            .unwrap_or(&self.state.presentation.control)
            .clone();
        let mut req =
            rtsp_types::Request::builder(rtsp_types::Method::Setup, rtsp_types::Version::V1_0)
                .request_uri(url)
                .header(
                    rtsp_types::headers::TRANSPORT,
                    format!(
                        "RTP/AVP/TCP;unicast;interleaved={}-{}",
                        proposed_channel_id,
                        proposed_channel_id + 1
                    ),
                )
                .header(crate::X_DYNAMIC_RATE.clone(), "1".to_owned());
        if let Some(ref s) = self.state.session_id {
            req = req.header(rtsp_types::headers::SESSION, s.clone());
        }
        let (msg_ctx, cseq, response) = self.conn.send(&mut req.build(Bytes::new())).await?;
        debug!("SETUP response: {:#?}", &response);
        let conn_ctx = self.conn.inner.ctx();
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
        match self.state.session_id.as_ref() {
            Some(old) if old != response.session_id => {
                bail!(ErrorInt::RtspResponseError {
                    conn_ctx: *self.conn.inner.ctx(),
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
            None => self.state.session_id = Some(response.session_id.to_owned()),
        };
        let conn_ctx = self.conn.inner.ctx();
        self.state
            .channels
            .assign(response.channel_id, stream_i)
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
    pub async fn play(mut self, policy: PlayPolicy) -> Result<Session<Playing>, Error> {
        let session_id = self.state.session_id.take().ok_or_else(|| {
            wrap!(ErrorInt::FailedPrecondition(
                "must SETUP before PLAY".into()
            ))
        })?;
        trace!("PLAY with channel mappings: {:#?}", &self.state.channels);
        let (msg_ctx, cseq, response) = self
            .conn
            .send(
                &mut rtsp_types::Request::builder(
                    rtsp_types::Method::Play,
                    rtsp_types::Version::V1_0,
                )
                .request_uri(self.state.presentation.control.clone())
                .header(rtsp_types::headers::SESSION, session_id.clone())
                .header(rtsp_types::headers::RANGE, "npt=0.000-".to_owned())
                .build(Bytes::new()),
            )
            .await?;
        parse::parse_play(&response, &mut self.state.presentation).map_err(|description| {
            wrap!(ErrorInt::RtspResponseError {
                conn_ctx: *self.conn.inner.ctx(),
                msg_ctx,
                method: rtsp_types::Method::Play,
                cseq,
                status: response.status(),
                description,
            })
        })?;

        // Count how many streams have been setup (not how many are in the presentation).
        let setup_streams = self
            .state
            .presentation
            .streams
            .iter()
            .filter(|s| matches!(s.state, StreamState::Init(_)))
            .count();

        let all_have_time = self
            .state
            .presentation
            .streams
            .iter()
            .all(|s| match s.state {
                StreamState::Init(StreamStateInit {
                    initial_rtptime, ..
                }) => initial_rtptime.is_some(),
                _ => true,
            });

        // Move all streams that have been set up from Init to Playing state. Check that required
        // parameters are present while doing so.
        for (i, s) in self.state.presentation.streams.iter_mut().enumerate() {
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
                                    conn_ctx: *self.conn.inner.ctx(),
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
                    let conn_ctx = self.conn.inner.ctx();
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
                        rtp_handler: rtp::StrictSequenceChecker::new(ssrc, initial_seq),
                    };
                }
                StreamState::Uninit => {}
                StreamState::Playing { .. } => unreachable!(),
            };
        }
        Ok(Session {
            conn: self.conn,
            state: Playing {
                presentation: self.state.presentation,
                session_id,
                channels: self.state.channels,
                keepalive_state: KeepaliveState::Idle,
                keepalive_timer: tokio::time::sleep(KEEPALIVE_DURATION),
                describe_ctx: self.state.describe_ctx,
                describe_cseq: self.state.describe_cseq,
                describe_status: self.state.describe_status,
            },
        })
    }
}

pub enum PacketItem {
    RtpPacket(rtp::Packet),
    SenderReport(rtp::SenderReport),
}

impl Session<Playing> {
    /// Returns a wrapper which demuxes/depacketizes into frames.
    ///
    /// Fails if a stream that has been setup can't be depacketized.
    pub fn demuxed(mut self) -> Result<Demuxed, Error> {
        for s in &mut self.state.presentation.streams {
            if matches!(s.state, StreamState::Playing { .. }) {
                if let Err(ref description) = s.depacketizer {
                    bail!(ErrorInt::RtspResponseError {
                        conn_ctx: *self.conn.inner.ctx(),
                        msg_ctx: self.state.describe_ctx,
                        method: rtsp_types::Method::Describe,
                        cseq: self.state.describe_cseq,
                        status: self.state.describe_status,
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

    fn handle_keepalive_timer(
        conn: &mut RtspConnection,
        state: &mut PlayingProj<'_>,
        cx: &mut std::task::Context<'_>,
    ) -> Result<(), Error> {
        // Expect the previous keepalive request to have finished.
        match state.keepalive_state {
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
            KeepaliveState::Waiting(cseq) => bail!(ErrorInt::ReadError {
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
        let mut req = rtsp_types::Request::builder(
            rtsp_types::Method::GetParameter,
            rtsp_types::Version::V1_0,
        )
        .request_uri(state.presentation.base_url.clone())
        .header(rtsp_types::headers::SESSION, state.session_id.clone())
        .build(Bytes::new());
        let cseq = conn.fill_req(&mut req)?;
        conn.inner
            .start_send_unpin(rtsp_types::Message::Request(req))
            .expect("encoding is infallible");
        *state.keepalive_state = match conn.inner.poll_flush_unpin(cx) {
            Poll::Ready(Ok(())) => KeepaliveState::Waiting(cseq),
            Poll::Ready(Err(e)) => bail!(e),
            Poll::Pending => KeepaliveState::Flushing(cseq),
        };

        state
            .keepalive_timer
            .as_mut()
            .reset(tokio::time::Instant::now() + KEEPALIVE_DURATION);
        Ok(())
    }

    fn handle_response(
        state: &mut PlayingProj<'_>,
        conn: &RtspConnection,
        msg_ctx: &crate::RtspMessageContext,
        response: rtsp_types::Response<Bytes>,
    ) -> Result<(), Error> {
        if matches!(*state.keepalive_state,
                    KeepaliveState::Waiting(cseq) if parse::get_cseq(&response) == Some(cseq))
        {
            // We don't care if the keepalive response succeeds or fails. Just mark complete.
            *state.keepalive_state = KeepaliveState::Idle;
            return Ok(());
        }

        // The only response we expect in this state is to our keepalive request.
        bail!(ErrorInt::RtspFramingError {
            conn_ctx: *conn.inner.ctx(),
            msg_ctx: *msg_ctx,
            description: format!("Unexpected RTSP response {:#?}", response),
        })
    }

    fn handle_data(
        state: &mut PlayingProj<'_>,
        conn: &RtspConnection,
        msg_ctx: &RtspMessageContext,
        data: rtsp_types::Data<Bytes>,
    ) -> Result<Option<PacketItem>, Error> {
        let channel_id = data.channel_id();
        let m = match state.channels.lookup(channel_id) {
            Some(m) => m,
            None => bail!(ErrorInt::RtspUnassignedChannelError {
                conn_ctx: *conn.inner.ctx(),
                msg_ctx: *msg_ctx,
                channel_id,
            }),
        };
        let stream = &mut state.presentation.streams[m.stream_i];
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
            ChannelType::Rtp => Ok(Some(rtp_handler.rtp(
                conn.inner.ctx(),
                msg_ctx,
                &mut timeline,
                channel_id,
                m.stream_i,
                data.into_body(),
            )?)),
            ChannelType::Rtcp => rtp_handler
                .rtcp(msg_ctx, &mut timeline, m.stream_i, data.into_body())
                .map_err(|description| {
                    wrap!(ErrorInt::RtspDataMessageError {
                        conn_ctx: *conn.inner.ctx(),
                        msg_ctx: *msg_ctx,
                        channel_id,
                        stream_id: m.stream_i,
                        description,
                    })
                }),
        }
    }

    pub fn streams(&self) -> &[Stream] {
        &self.state.presentation.streams
    }
}

impl futures::Stream for Session<Playing> {
    type Item = Result<PacketItem, Error>;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Option<Self::Item>> {
        let this = self.project();
        let mut state = this.state.project();
        loop {
            // First try receiving data. Let this starve keepalive handling; if we can't keep up,
            // the server should probably drop us.
            match Pin::new(&mut this.conn.inner).poll_next(cx) {
                Poll::Ready(Some(Ok(msg))) => match msg.msg {
                    rtsp_types::Message::Data(data) => {
                        match Session::handle_data(&mut state, &this.conn, &msg.ctx, data) {
                            Err(e) => return Poll::Ready(Some(Err(e))),
                            Ok(Some(pkt)) => return Poll::Ready(Some(Ok(pkt))),
                            Ok(None) => continue,
                        };
                    }
                    rtsp_types::Message::Response(response) => {
                        if let Err(e) =
                            Session::handle_response(&mut state, &this.conn, &msg.ctx, response)
                        {
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

            // Then check if it's time for a new keepalive.
            if matches!(state.keepalive_timer.as_mut().poll(cx), Poll::Ready(())) {
                Session::handle_keepalive_timer(this.conn, &mut state, cx)?;
            }

            // Then finish flushing the current keepalive if necessary.
            if let KeepaliveState::Flushing(cseq) = state.keepalive_state {
                match this.conn.inner.poll_flush_unpin(cx) {
                    Poll::Ready(Ok(())) => *state.keepalive_state = KeepaliveState::Waiting(*cseq),
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
#[pin_project]
pub struct Demuxed {
    state: DemuxedState,
    #[pin]
    session: Session<Playing>,
}

impl futures::Stream for Demuxed {
    type Item = Result<CodecItem, Error>;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let mut this = self.project();
        loop {
            let (stream_id, pkt) = match this.state {
                DemuxedState::Waiting => match ready!(this.session.as_mut().poll_next(cx)) {
                    Some(Ok(PacketItem::RtpPacket(p))) => (p.stream_id, Some(p)),
                    Some(Ok(PacketItem::SenderReport(p))) => {
                        return Poll::Ready(Some(Ok(CodecItem::SenderReport(p))))
                    }
                    Some(Err(e)) => return Poll::Ready(Some(Err(e))),
                    None => return Poll::Ready(None),
                },
                DemuxedState::Pulling(stream_id) => (*stream_id, None),
                DemuxedState::Fused => return Poll::Ready(None),
            };
            let session = this.session.as_mut().project();
            let playing = session.state.project();
            let depacketizer = match &mut playing.presentation.streams[stream_id].depacketizer {
                Ok(d) => d,
                Err(_) => unreachable!("depacketizer was Ok"),
            };
            let conn_ctx = session.conn.inner.ctx();
            if let Some(p) = pkt {
                let msg_ctx = p.ctx;
                let channel_id = p.channel_id;
                let stream_id = p.stream_id;
                let ssrc = p.ssrc;
                let sequence_number = p.sequence_number;
                depacketizer.push(p).map_err(|description| {
                    wrap!(ErrorInt::RtpPacketError {
                        conn_ctx: *conn_ctx,
                        msg_ctx,
                        channel_id,
                        stream_id,
                        ssrc,
                        sequence_number,
                        description,
                    })
                })?;
            }
            match depacketizer.pull(conn_ctx) {
                Ok(Some(item)) => {
                    *this.state = DemuxedState::Pulling(stream_id);
                    return Poll::Ready(Some(Ok(item)));
                }
                Ok(None) => {
                    *this.state = DemuxedState::Waiting;
                    continue;
                }
                Err(e) => {
                    *this.state = DemuxedState::Fused;
                    return Poll::Ready(Some(Err(e)));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // See with: cargo test -- --nocapture client::tests::print_sizes
    #[test]
    fn print_sizes() {
        for (name, size) in &[
            ("RtspConnection", std::mem::size_of::<RtspConnection>()),
            (
                "Session<Described>",
                std::mem::size_of::<Session<Described>>(),
            ),
            ("Session<Playing>", std::mem::size_of::<Session<Playing>>()),
            ("Demuxed", std::mem::size_of::<Demuxed>()),
            ("Stream", std::mem::size_of::<Stream>()),
            ("PacketItem", std::mem::size_of::<PacketItem>()),
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
